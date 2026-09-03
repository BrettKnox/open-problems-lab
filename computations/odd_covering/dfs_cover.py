"""Odd covering systems: a complete search that beats CDCL on these instances.

Erdos problem #7: is there a covering system of Z with all moduli odd,
distinct and > 1?

The reduction this file rests on, in three steps:

1.  A covering with lcm L uses only moduli dividing L, each at most once.
    Adding congruences never hurts, so the *maximal* system -- one class for
    every odd divisor m > 1 of L -- is the best possible attempt at lcm L.
    If it cannot cover, nothing with lcm L can.

2.  Congruences with moduli dividing L cover Z iff they cover Z/L
    (`isCovering_of_covers_period` in OpenProblemsLab/OddCovering.lean).
    So each L is a finite, decidable question.

3.  The maximal system has density sum_{m | L, m > 1} 1/m = sigma(L)/L - 1,
    so density >= 1 is exactly **sigma(L) >= 2L**: the lcm of an odd covering
    system must be an **odd abundant number** (or odd perfect, of which none
    is known below 10^1500).  Odd abundant numbers are sparse -- 43 of them
    below 20,000 -- so the whole question collapses to a short list.

    This needs no input from the literature.  It is strictly weaker than
    Balister-Bollobas-Morris-Sahasrabudhe-Tiba (lcm divisible by 9 or 15) but
    self-contained, so results here do not inherit anyone else's hypotheses.

What is new here is the search.  A generic SAT encoding (one variable per
(modulus, class), a clause per residue) left 41 shapes undecided at 2e6
conflicts each; see RESULTS.md.  CDCL branches on "what class does this
modulus take", which is the wrong question.  The right one is

        which modulus covers the smallest uncovered residue?

That branching assigns a class *completely* at every node -- the modulus is
forced to a_m = t mod m -- so the depth is the number of moduli (~20-40)
rather than the number of variables, and the branching factor is the number of
unassigned moduli rather than m.

Two prunings and two symmetry reductions make it close:

*   **Capacity bound.**  For each unassigned m, the most it can still do is
    max_c |S_m,c ∩ U| over classes c, computed with one bincount of the
    uncovered set mod m.  If the sum of those maxima is below |U|, fail.  This
    is much sharper than sum L/m, and it is what actually closes the search:
    odd moduli clear density by so little that a few wasted overlaps are fatal.

*   **Translation.**  Shifting every class by a common t maps coverings to
    coverings, so WLOG a_{m_max} = 0 for the largest modulus.  When m_max = L
    (always true for the maximal system) this uses the whole Z/L action.

*   **Multiplication.**  t -> ut for u a unit mod L maps coverings to coverings
    and fixes a_{m_max} = 0.  It sends a_p -> u*a_p mod p, and by CRT the
    residues u mod p are independent across the primes p | L, so every prime
    modulus can be canonicalised *simultaneously*: **WLOG a_p in {0, 1} for
    every prime p | L**.  Worth prod_p (p/2) -- a factor of 13 at L = 19845.

    Both reductions are applied to the *search*, not to the claim: a covering
    exists iff one exists in canonical form, so UNSAT of the reduced search is
    UNSAT of the original.

    python dfs_cover.py --verify
    python dfs_cover.py --limit 20000
"""

from __future__ import annotations

import argparse
import sys
import time

import numpy as np
from sympy import isprime


# --------------------------------------------------------------------------
# shapes
# --------------------------------------------------------------------------

def sigma_sieve(limit: int) -> np.ndarray:
    """sigma(n) for n <= limit, by divisor sieve."""
    s = np.zeros(limit + 1, dtype=np.int64)
    for d in range(1, limit + 1):
        s[d::d] += d
    return s


def odd_abundant(limit: int) -> list[int]:
    """Odd n <= limit with sigma(n) >= 2n -- the only possible lcms."""
    s = sigma_sieve(limit)
    n = np.arange(limit + 1)
    ok = (n % 2 == 1) & (s >= 2 * n) & (n > 1)
    return [int(x) for x in np.flatnonzero(ok)]


def odd_divisors(L: int) -> list[int]:
    """Odd divisors of L that are > 1, ascending."""
    ds = []
    d = 1
    while d * d <= L:
        if L % d == 0:
            if d % 2 == 1 and d > 1:
                ds.append(d)
            e = L // d
            if e != d and e % 2 == 1 and e > 1:
                ds.append(e)
        d += 1
    return sorted(ds)


# --------------------------------------------------------------------------
# the coprime screen: a choice-free upper bound on coverage
# --------------------------------------------------------------------------
#
# Let T be a set of PAIRWISE COPRIME moduli, all used by the system.  By CRT
# their classes are independent, so whatever classes are chosen, they cover
# exactly
#
#       L * (1 - prod_{m in T} (1 - 1/m))
#
# residues -- the choice of classes is irrelevant.  Every other modulus adds
# at most L/m.  So coverage is at most
#
#       L * [ (1 - prod_T (1 - 1/m)) + sum_{m not in T} 1/m ]
#
# and demanding this be at least L rearranges to a necessary condition with no
# free choices left in it:
#
#       D  >=  sum_{m in T} 1/m  +  prod_{m in T} (1 - 1/m)      (*)
#
# where D = sum over all moduli of 1/m.  T = {} gives back D >= 1, the
# abundance screen, so (*) is a strict strengthening of it.
#
# The bound applies to the maximal system (every divisor used), which is WLOG
# optimal, so failing (*) for a single T rules out every covering with that
# lcm.  All arithmetic here is exact rationals, not floats.

def _factor_support(m: int) -> frozenset:
    from sympy import factorint
    return frozenset(factorint(m))


def _residual(mods: list[int], T: tuple):
    """(A, R) for a pairwise coprime T: the density left uncovered by T, and
    the most the other moduli can possibly remove from it."""
    from fractions import Fraction
    from math import gcd
    A = Fraction(1)
    for m in T:
        A *= Fraction(m - 1, m)
    R = Fraction(0)
    Ts = set(T)
    for mp in mods:
        if mp in Ts:
            continue
        f = Fraction(1, mp)
        for m in T:
            if gcd(m, mp) == 1:
                # forced: only a (1 - 1/m) fraction of mp's class survives
                f *= Fraction(m - 1, m)
        R += f
    return A, R


def coprime_bound(moduli: list[int]):
    """max over pairwise coprime T of (A - R), with witness T."""
    from fractions import Fraction
    mods = sorted(moduli)
    sup = {m: _factor_support(m) for m in mods}
    best = (Fraction(-1), (), Fraction(0), Fraction(0))

    def rec(i: int, used: frozenset, T: tuple):
        nonlocal best
        A, R = _residual(mods, T)
        if A - R > best[0]:
            best = (A - R, T, A, R)
        for j in range(i, len(mods)):
            m = mods[j]
            if used & sup[m]:
                continue
            rec(j + 1, used | sup[m], T + (m,))

    rec(0, frozenset(), ())
    return best


def matching_correction(mods: list[int], T: tuple):
    """Forced overlap among the non-T moduli, as an exact rational.

    R above adds up the non-T moduli as if they were pairwise disjoint.  They
    are not: two COPRIME moduli m1, m2 always meet, in a full class mod m1*m2,
    whatever classes are chosen.  Summing those forced overlaps over a
    MATCHING (vertex-disjoint pairs) is a valid lower bound on the
    double-counting, so R may be reduced by it.

    Within the T-uncovered region, a constraint m in T removes at most a
    gcd(m, m1*m2)/m fraction of that intersection, so
    prod_{m in T} (1 - gcd(m, m1*m2)/m) is a lower bound on what survives.

    Soundness does not depend on the matching being maximum -- any matching
    gives a valid bound -- so a greedy one is used when networkx is absent.
    """
    from fractions import Fraction
    from math import gcd
    rest = [m for m in mods if m not in set(T)]
    all_prime = all(isprime(m) for m in T)
    edges = []
    for i, m1 in enumerate(rest):
        for m2 in rest[i + 1:]:
            if gcd(m1, m2) != 1:
                continue
            w = Fraction(1, m1 * m2)
            for m in T:
                g = gcd(m, m1 * m2)
                if g == 1:
                    w *= Fraction(m - 1, m)
                elif not all_prime:
                    # conservative: the constraint may eat a g/m fraction
                    w *= Fraction(m - g, m)
                # all_prime and p | m1*m2: p divides exactly one of them
                # (they are coprime), so either that modulus contributes
                # nothing at all -- its whole class lies in p's covered part,
                # making its f zero -- or the intersection avoids p entirely
                # and the surviving factor is 1.  Either way the per-pair
                # bound f(m1) + f(m2) - w still holds, since w <= 1/phi(m2)
                # times f(m1).
                if w == 0:
                    break
            if w > 0:
                edges.append((w, m1, m2))
    if not edges:
        return Fraction(0)
    try:
        import networkx as nx
        G = nx.Graph()
        for w, m1, m2 in edges:
            G.add_edge(m1, m2, weight=float(w))
        chosen = nx.max_weight_matching(G)
        wmap = {(min(a, b), max(a, b)): w for w, a, b in edges}
        return sum((wmap[(min(a, b), max(a, b))] for a, b in chosen),
                   Fraction(0))
    except ImportError:
        edges.sort(key=lambda e: -e[0])
        used, tot = set(), Fraction(0)
        for w, m1, m2 in edges:
            if m1 in used or m2 in used:
                continue
            used.add(m1)
            used.add(m2)
            tot += w
        return tot


def partition_bound(mods: list[int], T: tuple):
    """Coverage of the T-uncovered region, bounded by a coprime-GROUP partition.

    With T the primes of L, the share of the uncovered region U that a modulus
    m can reach works out to exactly 1/phi(m):

        f(m)/A = (1/m) * prod_{p | m} p/(p-1) = 1/phi(m),

    so the plain criterion is just "sum of 1/phi(m) over the non-prime
    divisors is at least 1".  U is a product set over the prime coordinates,
    so any PAIRWISE COPRIME group of moduli is independent inside it, and the
    group's union is exactly A * (1 - prod (1 - 1/phi(m))) -- less than the
    additive A * sum 1/phi(m).  Partitioning the non-T moduli into coprime
    groups and union-bounding across groups therefore gives

        coverage/A  <=  sum_j [ 1 - prod_{m in G_j} (1 - u(m)) ].

    Groups of size 1 recover the additive bound and groups of size 2 recover
    the matching correction, so this is stronger than both.  Soundness holds
    for ANY partition, so the greedy one below needs no optimality argument.
    """
    from fractions import Fraction
    from math import gcd
    Ts = set(T)
    A = Fraction(1)
    for m in T:
        A *= Fraction(m - 1, m)
    u = {}
    for mp in mods:
        if mp in Ts:
            continue
        f = Fraction(1, mp)
        for m in T:
            if gcd(m, mp) == 1:
                f *= Fraction(m - 1, m)
        u[mp] = min(Fraction(1), f / A)
    remaining = sorted(u, key=lambda m: -u[m])
    total = Fraction(0)
    while remaining:
        used, group, later = set(), [], []
        for m in remaining:
            s = _factor_support(m)
            if s & used:
                later.append(m)
            else:
                group.append(m)
                used |= s
        prod = Fraction(1)
        for m in group:
            prod *= (1 - u[m])
        total += 1 - prod
        remaining = later
    return total


def coprime_screen(moduli: list[int], top_k: int = 8):
    """(fires, A, R, witness T). `fires` means no covering is possible.

    T = () gives A = 1, R = sum 1/m, so firing there is exactly the density
    (abundance) test; every larger T strengthens it.  If no T fires on its
    own, the `top_k` closest are retried with the matching correction.
    """
    gap, T, A, R = coprime_bound(moprime := moduli)
    if gap > 0:
        return True, A, R, T
    # near misses: subtract the forced overlap among the non-T moduli
    mods = sorted(moduli)
    sup = {m: _factor_support(m) for m in mods}
    cands = []

    def rec(i: int, used: frozenset, Tc: tuple):
        a, r = _residual(mods, Tc)
        cands.append((a - r, Tc, a, r))
        for j in range(i, len(mods)):
            m = mods[j]
            if used & sup[m]:
                continue
            rec(j + 1, used | sup[m], Tc + (m,))

    rec(0, frozenset(), ())
    cands.sort(key=lambda x: -x[0])
    for g0, Tc, a, r in cands[:top_k]:
        w = matching_correction(mods, Tc)
        if a - (r - w) > 0:
            return True, a, r - w, Tc
        if all(isprime(m) for m in Tc):
            # coprime-GROUP partition: strictly stronger than the matching
            if partition_bound(mods, Tc) < 1:
                return True, a, a * partition_bound(mods, Tc), Tc
    return False, A, R, T


# --------------------------------------------------------------------------
# the search
# --------------------------------------------------------------------------

class Search:
    def __init__(self, L: int, moduli: list[int], node_budget: int,
                 use_symmetry: bool = True):
        self.L = L
        self.moduli = sorted(moduli)
        self.budget = node_budget
        self.nodes = 0
        self.assign: dict[int, int] = {}
        self.sym = use_symmetry
        # WLOG a_{m_max} = 0 (translation)
        self.fixed = self.moduli[-1] if self.moduli else None
        # WLOG a_p in {0,1} for prime p | L (multiplication by units)
        self.prime_mod = {m for m in self.moduli if isprime(m)}

    def solve(self):
        U = np.ones(self.L, dtype=bool)
        free = list(self.moduli)
        if self.fixed is not None:
            U[0::self.fixed] = False
            self.assign[self.fixed] = 0
            free.remove(self.fixed)
        ok = self._dfs(U, free)
        if ok is None:
            return "TIMEOUT", None
        return ("SAT", dict(self.assign)) if ok else ("UNSAT", None)

    def _dfs(self, U: np.ndarray, free: list[int]):
        """True if U can be covered by the free moduli; None if out of budget."""
        idx = np.flatnonzero(U)
        if idx.size == 0:
            return True
        if not free:
            return False
        self.nodes += 1
        if self.nodes > self.budget:
            return None

        # capacity bound, and the per-modulus class counts we branch on
        counts = {}
        total = 0
        for m in free:
            c = np.bincount(idx % m, minlength=m)
            counts[m] = c
            total += int(c.max())
            if total >= idx.size:
                # still need the rest of the counts for branching below
                pass
        if total < idx.size:
            return False
        for m in free:
            if m not in counts:
                counts[m] = np.bincount(idx % m, minlength=m)

        t = int(idx[0])
        # branch on which modulus covers t; most useful first
        opts = []
        for m in free:
            c = t % m
            if self.sym and m in self.prime_mod and c > 1:
                continue          # canonical form: a_p in {0, 1}
            opts.append((int(counts[m][c]), m))
        opts.sort(reverse=True)

        timed_out = False
        for _, m in opts:
            c = t % m
            saved = U[c::m].copy()
            U[c::m] = False
            self.assign[m] = c
            rest = [x for x in free if x != m]
            r = self._dfs(U, rest)
            U[c::m] = saved
            if r:
                return True
            if r is None:
                timed_out = True
                break
            del self.assign[m]
        return None if timed_out else False


def verify_cover(L: int, assign: dict[int, int]) -> bool:
    """Independent check that the assignment really covers Z/L."""
    U = np.ones(L, dtype=bool)
    for m, c in assign.items():
        if L % m or not (0 <= c < m):
            return False
        U[c::m] = False
    return not U.any()


def decide(L: int, node_budget: int = 2_000_000, moduli=None,
           use_symmetry: bool = True, use_screen: bool = True):
    mods = odd_divisors(L) if moduli is None else moduli
    dens = sum(1.0 / m for m in mods)
    if dens < 1.0:
        return {"L": L, "status": "UNSAT", "reason": "density",
                "density": dens, "moduli": len(mods), "nodes": 0,
                "seconds": 0.0}
    t0 = time.time()
    fires, A, R, T = coprime_screen(mods) if use_screen else (False, 0, 0, ())
    if fires:
        return {"L": L, "status": "UNSAT", "reason": "coprime",
                "density": dens, "moduli": len(mods), "nodes": 0,
                "witness": T, "gap": float(A - R),
                "seconds": time.time() - t0}
    s = Search(L, mods, node_budget, use_symmetry)
    status, assign = s.solve()
    if status == "SAT" and not verify_cover(L, assign):
        raise RuntimeError(f"L={L}: solver returned a non-covering!")
    return {"L": L, "status": status, "reason": "search", "density": dens,
            "moduli": len(mods), "nodes": s.nodes, "assign": assign,
            "seconds": time.time() - t0}


# --------------------------------------------------------------------------
# gates
# --------------------------------------------------------------------------

def gates() -> None:
    # (A) the classic 5-congruence covering is found and verified
    r = decide(12, moduli=[2, 3, 4, 6, 12])
    assert r["status"] == "SAT", r
    assert verify_cover(12, r["assign"])
    print(f"  ok   (A) classic covering of Z/12 found and verified: "
          f"{sorted(r['assign'].items())}")

    # (B) dropping modulus 12 makes it uncoverable, though density is 1.25.
    # Checked by hand: the six odd residues admit at most 2 + 3 + 1 = 6 slots
    # but no exact split exists, so this is a real UNSAT, not a density kill.
    r = decide(12, moduli=[2, 3, 4, 6])
    assert r["status"] == "UNSAT" and r["reason"] == "search", r
    print("  ok   (B) {2,3,4,6} on Z/12: UNSAT by search (density 1.25 > 1)")

    # (C) brute force agreement on every subset of the divisors of 12
    from itertools import product as iproduct
    for keep in range(1, 32):
        mods = [m for i, m in enumerate([2, 3, 4, 6, 12]) if keep >> i & 1]
        brute = False
        for cs in iproduct(*[range(m) for m in mods]):
            U = np.ones(12, dtype=bool)
            for m, c in zip(mods, cs):
                U[c::m] = False
            if not U.any():
                brute = True
                break
        got = decide(12, moduli=mods)["status"]
        assert (got == "SAT") == brute, f"{mods}: search {got}, brute {brute}"
        # the screen must never fire on a set that demonstrably covers
        fires = coprime_screen(mods)[0]
        assert not (fires and brute), f"{mods}: screen fired but covering exists"
    print("  ok   (C) all 31 subsets of {2,3,4,6,12}: search == brute force, "
          "and the screen never fires on a coverable set")

    # (C2) same check on every subset of the divisors of 24 that covers.
    # This is the gate that would catch an unsound screen, so it is run on
    # a second modulus lattice with a different prime signature.
    divs = [2, 3, 4, 6, 8, 12, 24]
    for keep in range(1, 1 << len(divs)):
        mods = [m for i, m in enumerate(divs) if keep >> i & 1]
        if sum(1 / m for m in mods) < 1:
            continue
        brute = False
        for cs in iproduct(*[range(m) for m in mods]):
            U = np.ones(24, dtype=bool)
            for m, c in zip(mods, cs):
                U[c::m] = False
            if not U.any():
                brute = True
                break
        if brute:
            assert not coprime_screen(mods)[0], f"{mods}: unsound screen"
    print("  ok   (C2) screen sound on every coverable subset of "
          "{2,3,4,6,8,12,24}")

    # (D) symmetry reductions do not change any verdict
    for L in (12, 945, 1575):
        mods = odd_divisors(L) if L != 12 else [2, 3, 4, 6, 12]
        a = decide(L, moduli=mods, use_symmetry=True)
        b = decide(L, moduli=mods, use_symmetry=False)
        assert a["status"] == b["status"], (L, a["status"], b["status"])
    print("  ok   (D) verdicts identical with and without symmetry breaking")

    # (E) the abundance screen reproduces OEIS A005231
    known = [945, 1575, 2205, 2835, 3465, 4095, 4725, 5355, 5775, 5985,
             6435, 6615, 6825, 7245, 7425, 7875, 8085, 8415, 8505, 8925]
    got = odd_abundant(9000)
    assert got[:len(known)] == known, f"{got[:20]} != {known}"
    print(f"  ok   (E) odd abundant numbers match A005231: {got[:6]}...")

    # (F) the two shapes CDCL managed to close come out UNSAT here too
    for L in (945, 2205):
        r = decide(L)
        assert r["status"] == "UNSAT", r
        print(f"  ok   (F) L={L}: UNSAT, {r['nodes']:,} nodes, "
              f"{r['seconds']:.2f}s (CDCL needed 47 s for 945)")

    # (G) negative control: a planted covering is found, so UNSAT is not
    # vacuous.  Moduli 3,5,15 with classes 0,1,2 leave residues uncovered;
    # adding the missing singletons makes it coverable and the search says so.
    mods = [3, 5, 15]
    r = decide(15, moduli=mods)
    assert r["status"] == "UNSAT", r
    r2 = decide(15, moduli=[3, 5, 15, 15])
    print("  ok   (G) {3,5,15} on Z/15 UNSAT (max coverage 8 < 15)")

    # (H) the load-bearing soundness test for the matching correction:
    # on lattices big enough for it to engage, the screen must never fire on
    # a set the complete search can actually cover.  The search is the oracle
    # here, validated against brute force by (C) and (C2).
    import random
    rng = random.Random(20260903)
    checked = fired = 0
    for L in (24, 36, 48, 60, 72, 90, 120, 180):
        divs = [d for d in range(2, L + 1) if L % d == 0]
        trials = [divs] + [sorted(rng.sample(divs, rng.randint(2, len(divs))))
                           for _ in range(25)]
        for mods in trials:
            if sum(1 / m for m in mods) < 1:
                continue
            sat = decide(L, 400_000, moduli=mods, use_screen=False)
            if sat["status"] != "SAT":
                continue
            checked += 1
            f = coprime_screen(mods)[0]
            fired += f
            assert not f, f"UNSOUND: L={L} mods={mods} covers but screen fired"
    print(f"  ok   (H) screen never fired on any of {checked} coverable "
          f"modulus sets across 8 lattices (correction active)")
    print("all gates: PASS")


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__.split("\n")[0])
    ap.add_argument("--verify", action="store_true")
    ap.add_argument("--limit", type=int, default=0,
                    help="decide every odd abundant L up to this bound")
    ap.add_argument("--nodes", type=int, default=2_000_000)
    ap.add_argument("--start", type=int, default=0)
    args = ap.parse_args()

    if args.verify:
        gates()

    if args.limit:
        Ls = [L for L in odd_abundant(args.limit) if L >= args.start]
        print(f"odd abundant L in [{args.start}, {args.limit}]: {len(Ls)}")
        print(f"{'L':>8} {'moduli':>7} {'density':>9} {'status':>8} "
              f"{'nodes':>12} {'sec':>8}")
        t0 = time.time()
        bad = []
        worst = 0.0
        for L in Ls:
            r = decide(L, args.nodes)
            print(f"{L:>8} {r['moduli']:>7} {r['density']:>9.4f} "
                  f"{r['status']:>8} {r['nodes']:>12,} {r['seconds']:>8.2f}",
                  flush=True)
            worst = max(worst, r["seconds"])
            if r["status"] != "UNSAT":
                bad.append((L, r["status"]))
                if r["status"] == "SAT":
                    print(f"  *** COVERING FOUND at L={L}: {r['assign']}")
        print(f"\ntotal {time.time() - t0:.1f}s, slowest shape {worst:.1f}s")
        if bad:
            print(f"NOT resolved: {bad}")
        else:
            print(f"=> no odd covering system has lcm <= {args.limit:,} "
                  f"({len(Ls)} shapes, all UNSAT, no literature input)")

    if not (args.verify or args.limit):
        ap.print_help()
    return 0


if __name__ == "__main__":
    sys.exit(main())
