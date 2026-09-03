"""Altman's stability theorem, checked in the range our exact table reaches.

Altman (arXiv:1606.03635) proved  ||2^k * 3^l|| = 2k + 3l  for all k <= 48 and
all l -- the strongest known partial result toward ||2^n|| = 2n, and the
statement recorded in OpenProblemsLab/IntegerComplexity.lean as
`altmanStability`.

This checks that identity directly for every pair (k, l) with 2^k * 3^l inside
the exact table computed by complexity.py (validated against OEIS A005245 and
an independent brute force). That is a genuine instantiation of the theorem in
a bounded range, using our own tooling -- not a reproduction of his proof,
which reasons about low-defect polynomials rather than enumerating integers.

    python stability.py --limit 4294967296
"""

from __future__ import annotations

import argparse
import sys
import time

from complexity import integer_complexity_table


def check(limit: int, verbose: bool = True) -> dict:
    t0 = time.time()
    f = integer_complexity_table(limit, verbose=False)
    build = time.time() - t0
    rows = []
    failures = []
    kmax = lmax = 0
    n_pairs = 0
    k = 0
    while 2 ** k <= limit:
        l = 0
        while 2 ** k * 3 ** l <= limit:
            n = 2 ** k * 3 ** l
            if n >= 1:
                got = int(f[n])
                want = 2 * k + 3 * l
                n_pairs += 1
                if k + l > 0 and got != want:
                    failures.append((k, l, got, want))
                if k + l > 0:
                    kmax = max(kmax, k)
                    lmax = max(lmax, l)
            l += 1
        k += 1
    # the largest l reachable for each k, for the report
    for kk in range(0, kmax + 1):
        ll = 0
        while 2 ** kk * 3 ** (ll + 1) <= limit:
            ll += 1
        rows.append((kk, ll))
    return {"limit": limit, "pairs": n_pairs, "failures": failures,
            "kmax": kmax, "lmax": lmax, "rows": rows,
            "build_s": build, "total_s": time.time() - t0}


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__.split("\n")[0])
    ap.add_argument("--limit", type=int, default=1 << 32)
    args = ap.parse_args()
    r = check(args.limit)
    print(f"table to {r['limit']:,} built in {r['build_s']:.0f}s")
    print(f"pairs (k,l) with 2^k*3^l <= limit: {r['pairs']:,}")
    print(f"  ||2^k 3^l|| = 2k + 3l verified for all of them "
          f"(k up to {r['kmax']}, l up to {r['lmax']})"
          if not r["failures"] else f"  FAILURES: {r['failures']}")
    print("  reach per k (largest l with 2^k*3^l <= limit):")
    for k, l in r["rows"]:
        if k % 4 == 0 or k == r["kmax"]:
            print(f"    k={k:>2}: l <= {l}")
    print(f"total {r['total_s']:.0f}s")
    return 1 if r["failures"] else 0


if __name__ == "__main__":
    sys.exit(main())
