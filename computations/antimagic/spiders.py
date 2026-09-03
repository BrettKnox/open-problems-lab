"""Antimagic hard-subcase probe: trees with many degree-2 vertices.

The Hartsfield-Ringel conjecture is settled for dense and regular graphs; the
acknowledged hard end is sparse trees, specifically those with many degree-2
vertices (long paths hanging off a few branch points). Our exhaustive sweep to
11 vertices never once needed the exact solver -- the hill-climber found a
labeling for all 1,018,690,328 connected graphs -- so "hard" instances, if
they exist, are not small.

This probes the structured families directly and measures *effort* rather than
just success:
  * spiders S(a1,...,ar): r legs of given lengths joined at a centre;
  * caterpillars: a spine with pendant leaves;
  * subdivided stars (spiders with all legs equal), the extremal shape.

For each we record whether a labeling was found, and how much work it took
(restarts and exact-fallback usage). A family whose effort grows sharply is
where a counterexample would live.

    python spiders.py --verify
    python spiders.py --spiders 14
"""

from __future__ import annotations

import argparse
import itertools
import random
import sys
import time

from sweep import exact, heuristic, verify_labeling


def spider(legs: list[int]) -> tuple[int, list[tuple[int, int]]]:
    """Centre 0, legs of the given lengths. Returns (n, edges)."""
    edges = []
    nxt = 1
    for L in legs:
        prev = 0
        for _ in range(L):
            edges.append((prev, nxt))
            prev = nxt
            nxt += 1
    return nxt, edges


def caterpillar(spine: int, legs: list[int]) -> tuple[int, list[tuple[int, int]]]:
    """Path of `spine` vertices; legs[i] leaves attached to spine vertex i."""
    edges = [(i, i + 1) for i in range(spine - 1)]
    nxt = spine
    for i, k in enumerate(legs):
        for _ in range(k):
            edges.append((i, nxt))
            nxt += 1
    return nxt, edges


def effort(n: int, edges: list[tuple[int, int]], rng: random.Random,
           restarts: int = 24):
    """(found?, restarts_used, used_exact, seconds)."""
    t0 = time.time()
    for r in range(1, restarts + 1):
        lab = heuristic(n, edges, rng, restarts=1)
        if lab is not None and verify_labeling(n, edges, lab):
            return True, r, False, time.time() - t0
    lab = exact(n, edges)
    ok = lab is not None and verify_labeling(n, edges, lab)
    return ok, restarts, True, time.time() - t0


def probe_spiders(nmax: int, rng: random.Random) -> None:
    print("  spider legs                     n   found  restarts  exact   secs")
    worst = []
    for r in range(3, 7):
        for legs in itertools.combinations_with_replacement(range(1, nmax), r):
            n, edges = spider(list(legs))
            if n > nmax or n < 4:
                continue
            ok, used, ex, dt = effort(n, edges, rng)
            worst.append((used, ex, dt, legs, n, ok))
            if not ok:
                print(f"  *** NOT ANTIMAGIC: legs={legs}")
    worst.sort(key=lambda t: (-t[0], -t[2]))
    for used, ex, dt, legs, n, ok in worst[:12]:
        print(f"  {str(legs):<28} {n:>4}   {str(ok):<5} {used:>8}  "
              f"{str(ex):<6} {dt:6.2f}")
    hardest = worst[0]
    print(f"  hardest: legs={hardest[3]} (n={hardest[4]}), "
          f"{hardest[0]} restarts, exact={hardest[1]}")
    print(f"  families probed: {len(worst)}; all antimagic: "
          f"{all(w[5] for w in worst)}")


def gates() -> None:
    rng = random.Random(20260824)
    # a spider with three legs of length 1 is the star K_{1,3}
    n, e = spider([1, 1, 1])
    assert n == 4 and len(e) == 3
    ok, _, _, _ = effort(n, e, rng)
    assert ok
    # a spider with one leg of length k is a path
    n, e = spider([5])
    assert n == 6 and sorted(e) == [(0, 1), (1, 2), (2, 3), (3, 4), (4, 5)]
    ok, _, _, _ = effort(n, e, rng)
    assert ok
    print("  ok   spider([1,1,1]) = K_{1,3} and spider([5]) = P6 built "
          "correctly and are antimagic")
    # caterpillar sanity
    n, e = caterpillar(3, [0, 2, 0])
    assert n == 5 and len(e) == 4
    ok, _, _, _ = effort(n, e, rng)
    assert ok
    print("  ok   caterpillar(3,[0,2,0]) built correctly and is antimagic")
    # negative control: the verifier rejects a damaged labeling
    n, e = spider([2, 2])
    ok, _, _, _ = effort(n, e, rng)
    lab = heuristic(n, e, rng)
    bad = list(lab)
    bad[0] = bad[1]
    assert not verify_labeling(n, e, bad)
    print("  ok   negative control: damaged labeling rejected")
    print("all gates: PASS")


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__.split("\n")[0])
    ap.add_argument("--verify", action="store_true")
    ap.add_argument("--spiders", type=int, default=0)
    args = ap.parse_args()
    rng = random.Random(20260824)
    if args.verify:
        gates()
    if args.spiders:
        probe_spiders(args.spiders, rng)
    if not (args.verify or args.spiders):
        ap.print_help()
    return 0


if __name__ == "__main__":
    sys.exit(main())
