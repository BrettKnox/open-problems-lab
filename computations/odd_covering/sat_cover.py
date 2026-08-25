"""Exhaustive SAT search for odd covering systems with a given lcm.

An odd covering system has distinct odd moduli m_i > 1 covering Z. Every
modulus divides L = lcm(m_i), and by the finite-period criterion proved in
OpenProblemsLab/OddCovering.lean (isCovering_of_covers_period) the system
covers Z iff it covers Z/L. Adding more moduli only helps, so for a fixed L
the most generous system uses *every* odd divisor m >= 3 of L.

So "does an odd covering system with lcm dividing L exist?" is exactly:

    choose a_m in Z/m for each odd divisor m >= 3 of L
    such that every r in Z/L has some m with r = a_m (mod m).

CNF: x[m][a] means "class a mod m is chosen"; exactly-one per modulus;
for each residue r of Z/L a clause OR_m x[m][r mod m].

UNSAT for every admissible L <= N therefore proves: no odd covering system
has lcm <= N. (Shapes are admissible only if 9 | L or 15 | L -- Balister,
Bollobas, Morris, Sahasrabudhe, Tiba 2022 -- and only if the density
sum 1/m over odd divisors reaches 1; both screens are applied first.)

    python sat_cover.py --verify
    python sat_cover.py --screen 200000
"""

from __future__ import annotations

import argparse
import sys
import time

from pysat.card import CardEnc, EncType
from pysat.formula import CNF, IDPool
from pysat.solvers import Solver

from density import divisors_odd


def build(L: int, mods: list[int]) -> tuple[CNF, dict]:
    """CNF for "one class per odd modulus covers all of Z/L".

    At-most-one uses pysat's sequential counter (linear in m); the naive
    pairwise encoding is quadratic and blows up on large moduli -- modulus
    32445 alone would need ~5.3e8 clauses."""
    cnf = CNF()
    pool = IDPool()
    var = {}
    for m in mods:
        for a in range(m):
            var[(m, a)] = pool.id(("x", m, a))
    for m in mods:
        lits = [var[(m, a)] for a in range(m)]
        cnf.append(lits)                            # at least one
        if m > 1:
            am1 = CardEnc.atmost(lits=lits, bound=1, vpool=pool,
                                 encoding=EncType.seqcounter)
            cnf.extend(am1.clauses)                 # at most one, linear
    for r in range(L):                              # every residue covered
        cnf.append([var[(m, r % m)] for m in mods])
    # Translation symmetry: shifting every class by a common t maps coverings
    # to coverings, so the class of one modulus may be fixed. Fixing the
    # largest modulus (L itself, always an odd divisor of L) uses the full
    # Z/L action and cuts the search space by a factor of L.
    if mods:
        cnf.append([var[(max(mods), 0)]])
    return cnf, var


def coverable(L: int, mods: list[int] | None = None, solver: str = "cd15",
              conf_budget: int | None = None):
    """(status, seconds, model). status True = a covering exists, False =
    proved impossible, None = the conflict budget ran out (undecided).

    Per-shape budgeting matters: the cost is very uneven (L=2205 decides in
    18 s, L=4095 needs many minutes), so an unbudgeted screen can stall on a
    single shape indefinitely. Undecided shapes are reported, never silently
    skipped."""
    mods = mods or divisors_odd(L)
    cnf, var = build(L, mods)
    t0 = time.time()
    with Solver(name=solver, bootstrap_with=cnf) as s:
        if conf_budget is None:
            ok = s.solve()
        else:
            s.conf_budget(conf_budget)
            ok = s.solve_limited()      # None when the budget is exhausted
        sysmodel = None
        if ok:
            pos = set(v for v in s.get_model() if v > 0)
            sysmodel = {m: next(a for a in range(m) if var[(m, a)] in pos)
                        for m in mods}
    return ok, time.time() - t0, sysmodel


def verify_system(L: int, system: dict) -> bool:
    """Independent check of a claimed covering (the Lean criterion)."""
    seen = bytearray(L)
    for m, a in system.items():
        for r in range(a % m, L, m):
            seen[r] = 1
    return all(seen)


def gates() -> None:
    # even moduli allowed: the classic system's lcm 12 IS coverable
    ok, dt, model = coverable(12, [2, 3, 4, 6, 12])
    assert ok and verify_system(12, model), "classic shape should be coverable"
    print(f"  ok   L=12 with moduli {{2,3,4,6,12}}: SAT, model verified "
          f"independently -> {model}")
    # odd-only at the same lcm is impossible (only odd divisor >= 3 is 3)
    ok2, _, _ = coverable(12, [3])
    assert not ok2
    print("  ok   L=12 restricted to odd moduli {3}: UNSAT")
    # a shape that IS coverable with odd moduli: L=9 needs 9 classes from
    # {3,9} -> 3+1 = 4 < 9 residues, so UNSAT; L=15 likewise
    for L in (9, 15, 45):
        ok3, _, _ = coverable(L)
        assert not ok3, f"L={L} unexpectedly coverable by odd moduli"
    print("  ok   small odd shapes L=9,15,45: UNSAT (as density predicts)")
    # negative control: a corrupted model must fail the independent verifier
    ok, _, model = coverable(12, [2, 3, 4, 6, 12])
    bad = dict(model)
    bad[2] = (bad[2] + 1) % 2
    assert not verify_system(12, bad)
    print("  ok   negative control: perturbed system rejected by the verifier")
    print("all gates: PASS")


def screen(bound: int, conf_budget: int | None, verbose: bool) -> int:
    t0 = time.time()
    admissible = killed_density = decided = 0
    found, undecided, times = [], [], []
    for L in range(3, bound + 1, 2):
        if not (L % 9 == 0 or L % 15 == 0):
            continue
        admissible += 1
        mods = divisors_odd(L)
        if sum(1.0 / m for m in mods) < 1.0:
            killed_density += 1
            continue
        ok, dt, model = coverable(L, mods, conf_budget=conf_budget)
        if ok is None:
            undecided.append(L)
            tag = "UNDECIDED (budget)"
        elif ok:
            assert verify_system(L, model), "SAT model failed the verifier!"
            found.append((L, model))
            tag = "*** ODD COVERING"
            print(f"  *** ODD COVERING at L={L}: {model}", flush=True)
        else:
            decided += 1
            times.append((dt, L))
            tag = "no covering"
        if verbose:
            print(f"  L={L:<7} {len(mods):>3} moduli  {tag:<20} {dt:8.1f}s"
                  f"   [{time.time() - t0:.0f}s total]", flush=True)
    print(f"\nadmissible shapes L <= {bound:,} (9|L or 15|L): {admissible:,}")
    print(f"  killed by density, no search:    {killed_density:,}")
    print(f"  proved impossible by SAT:        {decided:,}")
    print(f"  undecided (conflict budget hit): {len(undecided)}")
    print(f"  odd covering systems found:      {len(found)}")
    if undecided:
        print(f"  undecided shapes: {undecided}")
    if times:
        times.sort(reverse=True)
        print(f"  slowest decided: {[(L, round(d, 1)) for d, L in times[:5]]}")
    print(f"total {time.time() - t0:.0f}s")
    return 1 if found else 0


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__.split("\n")[0])
    ap.add_argument("--verify", action="store_true")
    ap.add_argument("--screen", type=int, default=0)
    ap.add_argument("--budget", type=int, default=2000000,
                    help="conflict budget per shape (0 = unlimited)")
    ap.add_argument("--quiet", action="store_true")
    ap.add_argument("--one", type=int, default=0, help="solve a single shape L")
    args = ap.parse_args()
    if args.verify:
        gates()
    if args.one:
        mods = divisors_odd(args.one)
        ok, dt, model = coverable(args.one, mods)
        print(f"L={args.one}: {len(mods)} odd moduli, "
              f"{'COVERABLE ' + str(model) if ok else 'UNSAT'}  [{dt:.1f}s]")
    if args.screen:
        return screen(args.screen, args.budget or None, not args.quiet)
    if not (args.verify or args.screen or args.one):
        ap.print_help()
    return 0


if __name__ == "__main__":
    sys.exit(main())
