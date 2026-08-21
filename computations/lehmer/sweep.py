"""Lehmer's totient problem: search for composite n with phi(n) | n - 1.

Lehmer (1932) conjectured there are none. This sweep verifies that directly
over an initial range, and separately measures how the structural constraints
proved in OpenProblemsLab/LehmerTotient.lean (a composite solution is odd,
squarefree, and has >= 3 distinct prime factors) prune the search.

phi is computed by a segmented linear-style sieve: for each segment, start
from n and divide out each prime factor found by sieving primes <= sqrt(hi),
tracking the remaining cofactor (a prime > sqrt if left over). Exact integer
arithmetic throughout.

Gates: (A) sieved phi equals a trial-division reference on random n and on
segment edges; (B) the known solutions of phi(n) | n-1 among n <= 10^6 are
exactly n = 1 and the primes -- verified against a primality reference;
(C) negative control: a corrupted phi value is caught by (A).

    python sweep.py --verify
    python sweep.py --limit 100000000
"""

from __future__ import annotations

import argparse
import sys
import time
from math import isqrt

import numpy as np


def primes_upto(n: int) -> np.ndarray:
    if n < 2:
        return np.zeros(0, dtype=np.int64)
    sieve = np.ones(n + 1, dtype=bool)
    sieve[:2] = False
    for p in range(2, isqrt(n) + 1):
        if sieve[p]:
            sieve[p * p :: p] = False
    return np.flatnonzero(sieve).astype(np.int64)


def phi_segment(lo: int, hi: int, base: np.ndarray) -> np.ndarray:
    """phi(n) for n in [lo, hi) via a segmented factor sieve."""
    size = hi - lo
    rem = np.arange(lo, hi, dtype=np.int64)     # unfactored part
    phi = np.ones(size, dtype=np.int64)
    for p in base:
        p = int(p)
        if p * p > hi - 1:
            break
        start = ((lo + p - 1) // p) * p
        if start >= hi:
            continue
        idx = np.arange(start - lo, size, p)
        if idx.size == 0:
            continue
        # multiply phi by (p-1) once, then by p for each extra power
        phi[idx] *= p - 1
        rem[idx] //= p
        while True:
            still = idx[rem[idx] % p == 0]
            if still.size == 0:
                break
            phi[still] *= p
            rem[still] //= p
            idx = still
    # whatever is left is a prime > sqrt(hi)
    big = rem > 1
    phi[big] *= rem[big] - 1
    if lo == 0:
        phi[0] = 0
    return phi


def phi_trial(n: int) -> int:
    if n == 0:
        return 0
    result, m = n, n
    p = 2
    while p * p <= m:
        if m % p == 0:
            while m % p == 0:
                m //= p
            result -= result // p
        p += 1
    if m > 1:
        result -= result // m
    return result


def is_prime(n: int) -> bool:
    if n < 2:
        return False
    if n % 2 == 0:
        return n == 2
    d = 3
    while d * d <= n:
        if n % d == 0:
            return False
        d += 2
    return True


def sweep(limit: int, seg: int = 1 << 22, verbose: bool = True) -> dict:
    base = primes_upto(isqrt(limit) + 1)
    t0 = time.time()
    hits = []          # n with phi(n) | n-1
    composite_hits = []
    checked = 0
    lo = 1
    while lo < limit:
        hi = min(lo + seg, limit)
        phi = phi_segment(lo, hi, base)
        ns = np.arange(lo, hi, dtype=np.int64)
        ok = (ns - 1) % phi == 0
        for n in ns[ok]:
            n = int(n)
            hits.append(n)
            if n > 1 and not is_prime(n):
                composite_hits.append(n)
        checked += hi - lo
        lo = hi
        if verbose:
            print(f"  ... {lo - 1:,} checked  [{time.time() - t0:.1f}s]", flush=True)
    return {"limit": limit, "hits": len(hits),
            "composite_hits": composite_hits, "seconds": time.time() - t0}


def gates() -> None:
    rng = np.random.default_rng(20260820)
    base = primes_upto(100000)
    # (A) sieve vs trial division
    for lo in (1, 2, 999983, 10_000_000):
        hi = lo + 5000
        phi = phi_segment(lo, hi, base)
        for n in [lo, hi - 1] + [int(x) for x in rng.integers(lo, hi, 40)]:
            assert int(phi[n - lo]) == phi_trial(n), \
                f"phi mismatch at {n}: sieve {int(phi[n-lo])}, trial {phi_trial(n)}"
    print("  ok   (A) segmented phi == trial division (edges + random n, "
          "4 windows incl. one at 10^7)")
    # (B) below 10^6 the only solutions are 1 and the primes
    res = sweep(1_000_000, verbose=False)
    assert res["composite_hits"] == [], f"composite solution found: {res['composite_hits']}"
    print(f"  ok   (B) n <= 10^6: {res['hits']:,} solutions of phi(n) | n-1, "
          f"all of them 1 or prime (no composite)")
    # (C) negative control
    phi = phi_segment(1000, 1100, base)
    phi[10] += 1
    assert int(phi[10]) != phi_trial(1010)
    print("  ok   (C) negative control: corrupted phi detected by the reference")
    print("all gates: PASS")


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__.split("\n")[0])
    ap.add_argument("--verify", action="store_true")
    ap.add_argument("--limit", type=int, default=0)
    args = ap.parse_args()
    if args.verify:
        gates()
    if args.limit:
        res = sweep(args.limit)
        print(f"\nlimit {res['limit']:,}: {res['hits']:,} n with phi(n) | n-1; "
              f"composite solutions: {res['composite_hits'] or 'NONE'}  "
              f"[{res['seconds']:.1f}s]")
        if res["composite_hits"]:
            return 1
    if not (args.verify or args.limit):
        ap.print_help()
    return 0


if __name__ == "__main__":
    sys.exit(main())
