"""SAT encoding for superpermutations: is there a superpermutation of length
L on n symbols?

Encoding (CNF, fed to CaDiCaL via python-sat):
  x[i][c]   position i carries symbol c        (i < L, c < n)
            exactly-one per position
  m[p][s]   the window at s spells permutation p   (s <= L - n)
            m[p][s] -> x[s+j][p_j]  for each j
            for each p: OR_s m[p][s]           (p occurs somewhere)

Only the forward implication of m is needed: if m[p][s] holds the window is
forced to spell p, and the at-least-one clause forces every permutation to
occur. Nothing constrains the word beyond that, so a model is exactly a
superpermutation of length L, and UNSAT is exactly a proof that L(n) > L.

Symmetry breaking (optional, --sym): fix the first n positions to the
identity permutation. This is validated, not assumed: the gates check that
it changes no answer at n = 3, 4 where L(n) is known.

Known values (the gates): L(1..5) = 1, 3, 9, 33, 153.

    python sat.py --verify
    python sat.py --n 5 --len 152 --sym      # expect UNSAT
"""

from __future__ import annotations

import argparse
import itertools
import sys
import time

from pysat.formula import CNF
from pysat.solvers import Solver


def build(n: int, L: int, sym: bool) -> tuple[CNF, list[list[int]]]:
    cnf = CNF()
    x = [[0] * n for _ in range(L)]
    nv = 0
    for i in range(L):
        for c in range(n):
            nv += 1
            x[i][c] = nv
    # exactly one symbol per position
    for i in range(L):
        cnf.append([x[i][c] for c in range(n)])
        for a in range(n):
            for b in range(a + 1, n):
                cnf.append([-x[i][a], -x[i][b]])
    perms = list(itertools.permutations(range(n)))
    for p in perms:
        occ = []
        for s in range(L - n + 1):
            nv += 1
            mv = nv
            occ.append(mv)
            for j in range(n):
                cnf.append([-mv, x[s + j][p[j]]])
        cnf.append(occ)
    if sym:
        for j in range(n):
            cnf.append([x[j][j]])
    return cnf, x


def solve(n: int, L: int, sym: bool = False, solver: str = "cd15"):
    """(sat?, word or None, seconds)."""
    if L < n:
        return False, None, 0.0
    cnf, x = build(n, L, sym)
    t0 = time.time()
    with Solver(name=solver, bootstrap_with=cnf) as s:
        ok = s.solve()
        word = None
        if ok:
            model = set(v for v in s.get_model() if v > 0)
            word = "".join(
                str(next(c for c in range(n) if x[i][c] in model) + 1)
                for i in range(L))
    return ok, word, time.time() - t0


def is_superperm(word: str, n: int) -> bool:
    """Independent check, shares nothing with the SAT encoding."""
    need = {"".join(str(c + 1) for c in p) for p in itertools.permutations(range(n))}
    return all(w in word for w in need)


KNOWN = {1: 1, 2: 3, 3: 9, 4: 33, 5: 153}


def gates(deep: bool = False) -> None:
    for n in ((1, 2, 3, 4) if deep else (1, 2, 3)):
        Ln = KNOWN[n]
        for sym in (False, True):
            ok, w, dt = solve(n, Ln, sym)
            assert ok and is_superperm(w, n), f"n={n} L={Ln} sym={sym}: no word"
            ok2, _, dt2 = solve(n, Ln - 1, sym)
            assert not ok2, f"n={n} L={Ln-1} sym={sym}: found a word below L(n)!"
        print(f"  ok   n={n}: SAT at L={Ln} (word verified independently), "
              f"UNSAT at L={Ln - 1}, with and without symmetry breaking")
    # negative control: a corrupted word must be rejected by the checker
    ok, w, _ = solve(3, 9, False)
    bad = w[:4] + ("1" if w[4] != "1" else "2") + w[5:]
    assert is_superperm(w, 3) and not is_superperm(bad, 3)
    print("  ok   negative control: damaged word rejected by the checker")
    print("all gates: PASS")


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__.split("\n")[0])
    ap.add_argument("--verify", action="store_true")
    ap.add_argument("--deep", action="store_true",
                    help="include the n=4 gate (minutes)")
    ap.add_argument("--n", type=int, default=0)
    ap.add_argument("--len", type=int, default=0)
    ap.add_argument("--sym", action="store_true")
    ap.add_argument("--ladder", type=int, default=0,
                    help="n: solve L = L(n)-4 .. L(n) and print the curve")
    ap.add_argument("--solver", default="cd15")
    args = ap.parse_args()
    if args.verify:
        gates(args.deep)
    if args.ladder:
        n = args.ladder
        base = KNOWN.get(n)
        print(f"   n={n}   L     result     seconds")
        for L in range(base - 4, base + 1):
            ok, w, dt = solve(n, L, args.sym, args.solver)
            tag = "SAT" if ok else "UNSAT"
            if ok:
                assert is_superperm(w, n), "SAT model is not a superpermutation!"
            print(f"        {L:>4}   {tag:<6}    {dt:8.1f}", flush=True)
    if args.n and args.len:
        ok, w, dt = solve(args.n, args.len, args.sym, args.solver)
        print(f"n={args.n} L={args.len} sym={args.sym}: "
              f"{'SAT' if ok else 'UNSAT'}  [{dt:.1f}s]")
        if ok:
            print("word:", w)
            print("independent check:", is_superperm(w, args.n))
    if not (args.verify or args.ladder or (args.n and args.len)):
        ap.print_help()
    return 0


if __name__ == "__main__":
    sys.exit(main())
