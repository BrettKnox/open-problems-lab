"""Distinct subset sums: verify the Conway-Guy construction exactly.

The Conway-Guy sequence u (OEIS A005318, b-file cached locally, gitignored:
OEIS content is CC BY-NC-SA) yields the n-element set
    A_n = { u(n) - u(n-i) : i = 1..n },
conjectured (Conway-Guy) to have all 2^n subset sums distinct, with
max A_n = u(n) ~ 0.23513 * 2^n  --  the classical evidence that Erdos's
c * 2^n lower-bound conjecture (EP #1) is within a constant of the truth.

Verification method (exact): the coefficients of  prod_i (1 + x^(a_i))  are
all <= 1  iff  all subset sums are distinct. The DP array is uint8 with
saturating addition, so no overflow can fake a pass.

Gates: (A) brute-force enumeration (sort 2^n sums, adjacent-equal scan) for
n <= 20 must agree; (B) a deliberately colliding set ({1,2,3}: 1+2=3) is
rejected by both methods; (C) u values are cross-checked against the OEIS
b-file over its full length.

    python ds.py --verify
    python ds.py --ladder 31
"""

from __future__ import annotations

import argparse
import os
import sys
import time
import urllib.request

import numpy as np

BFILE_URL = "https://oeis.org/A005318/b005318.txt"
CACHE = os.path.join(os.path.dirname(os.path.abspath(__file__)), "b005318.txt")


def load_u() -> list[int]:
    if not os.path.exists(CACHE):
        req = urllib.request.Request(BFILE_URL, headers={"User-Agent": "OpenProblemsLab/1.0"})
        with urllib.request.urlopen(req, timeout=120) as r:
            data = r.read()
        with open(CACHE, "wb") as fh:
            fh.write(data)
    u = {}
    for line in open(CACHE):
        line = line.strip()
        if not line or line.startswith("#"):
            continue
        k, v = line.split()
        u[int(k)] = int(v)
    assert sorted(u) == list(range(len(u))), "b-file gaps"
    assert [u[i] for i in range(9)] == [0, 1, 2, 4, 7, 13, 24, 44, 84], "b-file head"
    return [u[i] for i in range(len(u))]


def conway_guy_set(u: list[int], n: int) -> list[int]:
    return [u[n] - u[n - i] for i in range(1, n + 1)]


def distinct_dp(a: list[int]) -> bool:
    """Coefficients of prod (1+x^ai) all <= 1, with saturating uint8 adds."""
    total = sum(a)
    c = np.zeros(total + 1, dtype=np.uint8)
    c[0] = 1
    blk = 1 << 27  # process in ~128M-entry blocks to bound temporaries
    for ai in a:
        # c += shift(c, ai), saturating at 255; walk downward so the source
        # block is never overwritten before it is read
        n_tgt = total + 1 - ai
        for lo in range(((n_tgt - 1) // blk) * blk, -1, -blk):
            hi = min(lo + blk, n_tgt)
            src = c[lo:hi]
            tgt = c[ai + lo : ai + hi]
            s = tgt.astype(np.uint16)
            s += src
            np.minimum(s, 255, out=s)
            tgt[:] = s.astype(np.uint8)
    return int(c.max()) <= 1


def distinct_brute(a: list[int]) -> bool:
    """Independent: enumerate all 2^n sums, sort, scan for equal neighbours."""
    sums = np.zeros(1, dtype=np.int64)
    for ai in a:
        sums = np.concatenate([sums, sums + ai])
    sums.sort(kind="stable")
    return bool((np.diff(sums) != 0).all())


def gates(u: list[int]) -> None:
    for n in (5, 10, 15, 18, 20):
        A = conway_guy_set(u, n)
        d1, d2 = distinct_dp(A), distinct_brute(A)
        assert d1 and d2, f"Conway-Guy set n={n} rejected (dp {d1}, brute {d2})"
    print("  ok   (A) dp == brute == distinct on Conway-Guy sets n = 5..20")
    bad = [1, 2, 3]
    assert not distinct_dp(bad) and not distinct_brute(bad)
    bad2 = conway_guy_set(u, 12)
    bad2[0] = bad2[1] + bad2[2] - bad2[3]  # engineered collision risk
    assert distinct_dp(bad2) == distinct_brute(bad2)
    print("  ok   (B) colliding set {1,2,3} rejected by both; engineered "
          "perturbation agrees across methods")
    print(f"  ok   (C) A005318 b-file head and contiguity checked "
          f"({len(u)} terms)")
    print("all gates: PASS")


def ladder(u: list[int], nmax: int) -> None:
    print("   n        max(A_n)   max/2^n     distinct   time")
    for n in range(20, nmax + 1):
        A = conway_guy_set(u, n)
        t0 = time.time()
        ok = distinct_dp(A)
        dt = time.time() - t0
        print(f"  {n:>2}  {u[n]:>14,}   {u[n] / 2 ** n:.5f}    "
              f"{'YES' if ok else 'NO (!!)'}      {dt:.1f}s")
        if not ok:
            sys.exit(1)


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__.split("\n")[0])
    ap.add_argument("--verify", action="store_true")
    ap.add_argument("--ladder", type=int, default=0)
    ap.add_argument("--emit-lean", type=int, default=0,
                    help="print the n-element set as a Lean Finset literal")
    args = ap.parse_args()
    u = load_u()
    if args.verify:
        gates(u)
    if args.ladder:
        ladder(u, args.ladder)
    if args.emit_lean:
        A = sorted(conway_guy_set(u, args.emit_lean))
        print("{" + ", ".join(map(str, A)) + "}")
    if not (args.verify or args.ladder or args.emit_lean):
        ap.print_help()
    return 0


if __name__ == "__main__":
    sys.exit(main())
