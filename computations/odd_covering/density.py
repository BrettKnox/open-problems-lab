"""Odd covering systems (Erdos problem #7): how close can distinct odd moduli
come to covering the integers?

A covering system needs sum(1/m_i) >= 1 (each class a mod m has density 1/m).
For odd moduli the reachable density is bounded by which moduli are available
below a cutoff, and by the Balister-Bollobas-Morris-Sahasrabudhe-Tiba (2022)
theorem: an odd covering system must have lcm divisible by 9 or 15 (so the
"squarefree-with-small-lcm" shapes are dead).

This measures the frontier directly:
  * exact best achievable density with distinct odd moduli 3..M (greedy on
    1/m is optimal here: take every modulus, the sum is fixed);
  * exact maximum coverage of Z/L achievable by distinct odd moduli dividing
    a candidate lcm L, by exhaustive search over residue choices with
    branch-and-bound (this is the quantity that must reach L for a covering);
  * the resulting gap for each admissible shape L.

Verification is by the same finite-period criterion proved in Lean as
`isCovering_of_covers_period` (OpenProblemsLab/OddCovering.lean): a system of
moduli dividing L covers Z iff it covers {0..L-1}.

    python density.py --verify
    python density.py --shapes
"""

from __future__ import annotations

import argparse
import itertools
import sys
import time
from math import gcd


def divisors_odd(L: int, lo: int = 3) -> list[int]:
    """Odd divisors of L that are >= lo (candidate moduli for lcm L)."""
    out = []
    d = 1
    while d * d <= L:
        if L % d == 0:
            for x in (d, L // d):
                if x >= lo and x % 2 == 1 and x not in out:
                    out.append(x)
        d += 1
    return sorted(out)


def best_coverage(L: int, moduli: list[int], time_budget: float = 30.0):
    """Maximum number of residues of Z/L coverable by choosing one class
    a_i mod m_i for each modulus (each m_i used once). Branch and bound over
    moduli in decreasing density; returns (best_count, exhausted?)."""
    order = sorted(moduli, key=lambda m: 1.0 / m, reverse=True)
    n = len(order)
    # precompute the residue masks for each (modulus, offset)
    masks = []
    for m in order:
        per = []
        for a in range(m):
            v = 0
            for r in range(a % m, L, m):
                v |= 1 << r
            per.append(v)
        masks.append(per)
    remaining_gain = [0] * (n + 1)
    for i in range(n - 1, -1, -1):
        remaining_gain[i] = remaining_gain[i + 1] + L // order[i]
    best = [0]
    t0 = time.time()
    exhausted = [True]

    def rec(i: int, cov: int, cnt: int) -> None:
        if cnt > best[0]:
            best[0] = cnt
        if i == n or best[0] == L:
            return
        if time.time() - t0 > time_budget:
            exhausted[0] = False
            return
        if cnt + remaining_gain[i] <= best[0]:
            return
        for a in range(order[i]):
            nc = cov | masks[i][a]
            rec(i + 1, nc, bin(nc).count("1"))
            if best[0] == L or not exhausted[0]:
                return

    rec(0, 0, 0)
    return best[0], exhausted[0]


def covers(L: int, system: list[tuple[int, int]]) -> bool:
    """Finite-period check (the criterion proved in Lean)."""
    seen = [False] * L
    for a, m in system:
        assert L % m == 0
        for r in range(a % m, L, m):
            seen[r] = True
    return all(seen)


def gates() -> None:
    # the classic system, checked by the same criterion as the Lean theorem
    classic = [(0, 2), (0, 3), (1, 4), (5, 6), (7, 12)]
    assert covers(12, classic), "classic system should cover"
    assert not covers(12, classic[:-1]), "dropping a class should break it"
    print("  ok   classic {0(2),0(3),1(4),5(6),7(12)} covers Z/12; "
          "dropping one class breaks it (matches the Lean theorem)")
    # density necessity: any covering needs sum 1/m >= 1
    s = sum(1 / m for _, m in classic)
    assert s >= 1 - 1e-12, s
    print(f"  ok   density of the classic system = {s:.4f} >= 1")
    # density is NOT the obstruction: distinct odd moduli already clear 1
    odds = [3, 5, 7, 9, 11, 13, 15]
    dens = sum(1 / m for m in odds)
    assert dens > 1, dens
    small = [3, 5, 7, 9, 11, 13]
    assert sum(1 / m for m in small) < 1
    print(f"  ok   distinct odd moduli 3..15 have density {dens:.4f} > 1 "
          f"(3..13 gives {sum(1/m for m in small):.4f} < 1): the density "
          "bound is satisfiable, so it is NOT what obstructs odd coverings")
    # best_coverage sanity: moduli {3} on L=3 covers 1/3 of Z/3
    c, ex = best_coverage(3, [3])
    assert c == 1 and ex
    # {3,5,15} on L=15: naive 5+3+1 = 9, but CRT forces the mod-3 and mod-5
    # classes to meet in exactly one residue, so the true maximum is 8.
    c, ex = best_coverage(15, [3, 5, 15])
    assert ex and c == 8, (c, ex)
    print("  ok   best_coverage exact on small shapes ({3}/L=3 -> 1; "
          "{3,5,15}/L=15 -> 8, not the naive 5+3+1 = 9: coprime moduli "
          "overlap by CRT, which is the real obstruction)")
    # negative control: a wrong claim is caught
    assert not covers(15, [(0, 3), (0, 5)])
    print("  ok   negative control: an incomplete system is rejected")
    print("all gates: PASS")


SHAPES = [
    # (L, description) -- admissible lcm shapes under the BBMST 9-or-15 theorem
    (9 * 5 * 7, "9.5.7"),
    (9 * 5 * 7 * 11, "9.5.7.11"),
    (9 * 25 * 7, "9.25.7"),
    (27 * 5 * 7, "27.5.7"),
    (9 * 5 * 7 * 13, "9.5.7.13"),
    (15 * 7 * 11 * 13, "15.7.11.13"),
]


def shapes(budget: float) -> None:
    print("  shape           L      #odd moduli   density   best coverage / L      gap")
    for L, name in SHAPES:
        mods = divisors_odd(L)
        dens = sum(1 / m for m in mods)
        cov, ex = best_coverage(L, mods, time_budget=budget)
        tag = "" if ex else "  (budget hit: lower bound)"
        print(f"  {name:<12} {L:>7}   {len(mods):>6}      {dens:>7.4f}   "
              f"{cov:>8} / {L:<8} {L - cov:>6}{tag}", flush=True)


def screen(bound: int) -> None:
    """Rigorous pass: an odd covering with all moduli dividing L needs
    sum_{m | L, m odd, m >= 3} 1/m >= 1. Report which admissible shapes
    (odd L with 9 | L or 15 | L, per BBMST 2022) that kills outright."""
    dead = alive = 0
    survivors = []
    for L in range(3, bound + 1, 2):
        if not (L % 9 == 0 or L % 15 == 0):
            continue
        mods = divisors_odd(L)
        dens = sum(1 / m for m in mods)
        if dens < 1:
            dead += 1
        else:
            alive += 1
            survivors.append((L, dens, len(mods)))
    print(f"  admissible odd shapes L <= {bound:,} (9 | L or 15 | L): "
          f"{dead + alive:,}")
    print(f"  killed outright by the density bound (proof, no search): "
          f"{dead:,} ({dead / (dead + alive):.1%})")
    print(f"  survive density, so need real structure: {alive:,}")
    survivors.sort(key=lambda t: t[1])
    print("  tightest survivors (smallest density >= 1):")
    for L, d, k in survivors[:8]:
        print(f"    L = {L:>7}   density {d:.4f}   {k} odd moduli")


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__.split("\n")[0])
    ap.add_argument("--verify", action="store_true")
    ap.add_argument("--shapes", action="store_true")
    ap.add_argument("--budget", type=float, default=30.0)
    ap.add_argument("--screen", type=int, default=0,
                    help="density screen over admissible shapes L <= N")
    args = ap.parse_args()
    if args.verify:
        gates()
    if args.shapes:
        shapes(args.budget)
    if args.screen:
        screen(args.screen)
    if not (args.verify or args.shapes or args.screen):
        ap.print_help()
    return 0


if __name__ == "__main__":
    sys.exit(main())
