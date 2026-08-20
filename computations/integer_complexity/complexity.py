"""Integer complexity table: ||n|| for all n <= N (OEIS A005245).

||n|| is the least number of 1s needed to write n with +, * and parentheses.
The defining recurrence is

    ||1|| = 1
    ||n|| = min( min_{1 <= a <= n/2}      ||a|| + ||n-a||,        (additive)
                 min_{d | n, 1 < d <= sqrt n} ||d|| + ||n/d|| )   (multiplicative)

A direct implementation is Theta(N^2) because of the additive minimum. This
module computes the same table in near-linear time using one theorem and one
blocking argument, with no heuristics: the output is the exact A005245 table.

--------------------------------------------------------------------------
1. Additive pruning (Selfridge's bound)
--------------------------------------------------------------------------
Selfridge's lower bound, in the sharp integer form proved in this repository
as `cube_le_three_pow_complexity` in OpenProblemsLab/IntegerComplexity.lean:

    n^3 <= 3^||n||           for every n >= 1.

Let U be any known upper bound for ||n||.  If ||n|| is realised by an additive
split n = a + b with a <= b, then b >= ceil(n/2) and

    (a * ceil(n/2))^3 <= (a*b)^3 = a^3 * b^3 <= 3^||a|| * 3^||b|| = 3^||n|| <= 3^U

so the smaller summand obeys

    a <= floor( icbrt(3^U) / ceil(n/2) ) =: cap(U, n).             (*)

Empirically cap is a two-digit number even for n ~ 10^9, so only a few dozen
additive splits per n can ever matter.  (*) is an exact integer inequality --
`icbrt` is an exact integer cube root, no floating point is involved -- so
using it loses nothing.  Overestimating U only enlarges cap, which is safe.

--------------------------------------------------------------------------
2. Blocking
--------------------------------------------------------------------------
n is processed in blocks [L, R) chosen with R <= 2L.  For n in such a block,
every multiplicative split n = d*e with 2 <= d <= e has e <= n/2 < L, so both
factors are already final: the whole multiplicative pass is a set of strided
numpy writes, one per divisor d <= sqrt(R-1).

What is left inside a block is the additive recurrence, which is sequential
in n.  It is solved by relaxation to a fixed point:

  * step a = 1 (i.e. f[n] <= f[n-1] + 1) is applied in closed form by a
    running minimum of f[n] - n (`np.minimum.accumulate`), which collapses
    arbitrarily long chains of +1 in a single pass;
  * steps 2 <= a <= cap are applied as whole-array relaxations, restricted to
    the positions whose current bound admits that a by (*);
  * sweeps repeat until nothing changes.

Because every relaxation uses a genuine construction, the iterate is always an
upper bound; the dependency graph inside a block is acyclic (a >= 1 strictly
decreases n), so the fixed point is unique and equal to ||n||.

--------------------------------------------------------------------------
CLI
--------------------------------------------------------------------------
    python complexity.py --limit 1000000 --out table.npy
    python complexity.py --limit 4294967296 --verify

Memory is one int8 byte per integer plus ~10 bytes per block slot.
"""

from __future__ import annotations

import argparse
import time
from math import isqrt

import numpy as np

INF = np.int16(1 << 13)
#: complexities stay far below this; asserted at the end of every block.
WMAX = 128
#: fixed history prefix in the working buffer; must exceed every `cap` seen.
APREFIX = 1024
#: numbers below this are done by the plain quadratic recurrence.
SEED = 4096
#: switch from whole-array relaxation to indexed relaxation below this density.
DENSE_DIV = 4


def icbrt(x: int) -> int:
    """Exact integer cube root: largest r with r**3 <= x (x >= 0)."""
    if x < 1:
        return 0
    r = 1 << ((x.bit_length() + 2) // 3)
    while True:
        nr = (2 * r + x // (r * r)) // 3
        if nr >= r:
            break
        r = nr
    while r ** 3 > x:
        r -= 1
    while (r + 1) ** 3 <= x:
        r += 1
    return r


def brute_force(limit: int) -> np.ndarray:
    """||n|| for n <= limit straight from the definition. Theta(limit^2).

    Independent of the fast path, so it doubles as the reference oracle.
    """
    f = np.zeros(limit + 1, dtype=np.int16)
    if limit >= 1:
        f[1] = 1
    for n in range(2, limit + 1):
        h = n // 2
        best = int((f[1:h + 1] + f[n - 1:n - h - 1:-1]).min())
        for d in range(2, isqrt(n) + 1):
            if n % d == 0:
                v = int(f[d]) + int(f[n // d])
                if v < best:
                    best = v
        f[n] = best
    return f


class _Workspace:
    """Buffers reused across blocks (allocated once, at the largest span)."""

    def __init__(self, span: int) -> None:
        self.W = np.empty(APREFIX + span, dtype=np.int16)
        self.g = np.empty(APREFIX + span, dtype=np.int32)
        self.jj = np.arange(APREFIX + span, dtype=np.int32)
        self.buf = np.empty(span // 2 + 2, dtype=np.int16)


def _block(f: np.ndarray, L: int, R: int, ws: _Workspace, stats: list) -> None:
    """Fill f[L:R] exactly.  Requires R <= 2L and f[:L] already correct."""
    span = R - L
    W = ws.W[:APREFIX + span]
    Wb = W[APREFIX:]

    # ---- multiplicative splits n = d*e, 2 <= d <= e (so e <= n/2 < L) -------
    Wb.fill(INF)
    for d in range(2, isqrt(R - 1) + 1):
        e0 = max(d, -(-L // d))
        e1 = (R - 1) // d
        if e1 < e0:
            continue
        m = e1 - e0 + 1
        cand = ws.buf[:m]
        np.add(f[e0:e1 + 1], np.int16(f[d]), out=cand)
        view = Wb[d * e0 - L::d]
        np.minimum(view, cand, out=view)

    # ---- step a = 1, in closed form, over history + block ------------------
    W[:APREFIX] = f[L - APREFIX:L]
    jj = ws.jj[:APREFIX + span]
    g = ws.g[:APREFIX + span]

    def collapse_plus_one() -> None:
        np.subtract(W, jj, out=g, casting="unsafe")
        np.minimum.accumulate(g, out=g)
        np.add(g, jj, out=g)
        np.copyto(W, g, casting="unsafe")

    collapse_plus_one()

    # ---- how far the additive search has to go, from Selfridge's bound -----
    half = (L + 1) // 2                       # <= ceil(n/2) for every n in block
    cap_table = [icbrt(3 ** w) // half for w in range(WMAX)]
    bound = int(Wb.max())
    if bound >= WMAX:
        raise RuntimeError(f"upper bound {bound} >= WMAX={WMAX} at L={L}")
    cap = cap_table[bound]
    if cap >= APREFIX:                        # never seen; guard anyway
        raise RuntimeError(f"cap={cap} exceeds APREFIX={APREFIX} at L={L}")
    fa = f[1:max(cap, 1) + 1].astype(np.int16)

    # a in (cap_table[w-1], cap_table[w]] is only needed where the bound is >= w
    segments = []
    for w in range(1, WMAX):
        lo = max(2, cap_table[w - 1] + 1)
        hi = min(cap, cap_table[w])
        if lo <= hi:
            segments.append((w, lo, hi))

    sweeps = 0
    while True:
        sweeps += 1
        prev = Wb.copy()
        for w, lo, hi in segments:
            sel = Wb >= w
            count = int(np.count_nonzero(sel))
            if count == 0:
                continue
            if count * DENSE_DIV > span:
                for a in range(lo, hi + 1):
                    np.minimum(W[a:], fa[a - 1] + W[:-a], out=W[a:])
            else:
                idx = np.flatnonzero(sel) + APREFIX
                for a in range(lo, hi + 1):
                    W[idx] = np.minimum(W[idx], fa[a - 1] + W[idx - a])
        collapse_plus_one()
        if np.array_equal(Wb, prev):
            break

    hi_val = int(Wb.max())
    if hi_val >= WMAX:
        raise RuntimeError(f"complexity {hi_val} >= WMAX={WMAX} at L={L}")
    np.copyto(f[L:R], Wb, casting="unsafe")
    stats.append((L, span, cap, sweeps, hi_val))


def integer_complexity_table(limit: int, block: int = 1 << 26,
                             verbose: bool = True) -> np.ndarray:
    """Exact ||n|| for 0 <= n <= limit, as int8 (f[0] is a meaningless 0)."""
    if limit < 1:
        raise ValueError("limit must be >= 1")
    seed = min(limit, SEED)
    f = np.zeros(limit + 1, dtype=np.int8)
    np.copyto(f[:seed + 1], brute_force(seed), casting="unsafe")
    if limit <= seed:
        return f

    L = seed + 1
    ws = _Workspace(min(block, limit))
    stats: list = []
    t0 = time.perf_counter()
    while L <= limit:
        # R <= 2L keeps every cofactor of a block element strictly below L
        size = min(block, L, limit - L + 1)
        _block(f, L, L + size, ws, stats)
        L += size
        if verbose and len(stats) % 8 == 0:
            done = (L - 1) / limit
            el = time.perf_counter() - t0
            print(f"  n={L-1:>13,}  {done:6.1%}  {el:7.1f}s  "
                  f"eta {el/max(done,1e-9)-el:7.1f}s", flush=True)
    if verbose:
        print(f"  blocks={len(stats)} sweeps={sum(s[3] for s in stats)} "
              f"max_cap={max(s[2] for s in stats)} "
              f"max_complexity={max(s[4] for s in stats)}", flush=True)
    return f


def recompute_from_definition(f: np.ndarray, n: int, chunk: int = 1 << 23) -> int:
    """||n|| straight from the recurrence, using f for every smaller value.

    Scans the *entire* additive range 1 <= a <= n/2 -- no Selfridge pruning --
    so it is an independent audit of the pruning at values far beyond anything
    the OEIS b-file reaches.
    """
    best = int(INF)
    h = n // 2
    for s in range(1, h + 1, chunk):
        e = min(s + chunk - 1, h)
        lo = f[s:e + 1].astype(np.int16)
        hi = f[n - e:n - s + 1][::-1].astype(np.int16)
        v = int((lo + hi).min())
        if v < best:
            best = v
    for d in range(2, isqrt(n) + 1):
        if n % d == 0:
            v = int(f[d]) + int(f[n // d])
            if v < best:
                best = v
    return best


def audit(f: np.ndarray, samples: int = 64, seed: int = 20260820,
          verbose: bool = True) -> int:
    """Re-derive ||n|| from the definition for random large n; assert equality."""
    limit = len(f) - 1
    rng = np.random.default_rng(seed)
    lo = max(2, limit // 2)
    picks = sorted(set(int(x) for x in rng.integers(lo, limit + 1, size=samples)))
    picks += [limit, limit - 1, lo]
    t0 = time.perf_counter()
    for n in sorted(set(picks)):
        got, want = int(f[n]), recompute_from_definition(f, n)
        if got != want:
            raise AssertionError(
                f"AUDIT FAILED at n={n}: table says {got}, full recurrence "
                f"says {want}")
    if verbose:
        print(f"recurrence audit: {len(set(picks))} random n in "
              f"[{lo:,}, {limit:,}] re-derived from the full definition "
              f"(all additive splits, no pruning) -- all match "
              f"[{time.perf_counter()-t0:.1f}s]")
    return len(set(picks))


def main() -> None:
    p = argparse.ArgumentParser(description="Compute the A005245 table up to N.")
    p.add_argument("--limit", type=int, required=True, help="N (inclusive)")
    p.add_argument("--out", type=str, default=None, help="save table as .npy (int8)")
    p.add_argument("--block", type=int, default=1 << 26, help="block size in n")
    p.add_argument("--verify", action="store_true",
                   help="also run the OEIS b-file check and the power checks")
    p.add_argument("--selfcheck", type=int, default=0, metavar="M",
                   help="compare the first M entries against brute_force(M)")
    p.add_argument("--audit", type=int, default=0, metavar="K",
                   help="re-derive K random large n from the full recurrence")
    p.add_argument("--quiet", action="store_true")
    args = p.parse_args()

    t0 = time.perf_counter()
    f = integer_complexity_table(args.limit, block=args.block, verbose=not args.quiet)
    elapsed = time.perf_counter() - t0
    print(f"computed ||n|| for n <= {args.limit:,} in {elapsed:.2f} s "
          f"({args.limit/elapsed/1e6:.2f} M n/s), "
          f"max ||n|| = {int(f[1:].max())}")

    if args.out:
        t1 = time.perf_counter()
        np.save(args.out, f)
        print(f"saved {args.out} ({f.nbytes/2**20:.1f} MiB) in "
              f"{time.perf_counter()-t1:.2f} s")

    if args.selfcheck:
        m = min(args.selfcheck, args.limit)
        t1 = time.perf_counter()
        ref = brute_force(m)
        if not np.array_equal(f[:m + 1].astype(np.int16), ref):
            d = np.flatnonzero(f[:m + 1].astype(np.int16) != ref)
            raise AssertionError(f"self-check failed, first n={int(d[0])}")
        print(f"self-check: matches the quadratic reference recurrence on "
              f"n = 0..{m:,} [{time.perf_counter()-t1:.1f}s]")

    if args.verify:
        import validate_oeis
        import verify_powers
        validate_oeis.check(f, verbose=True)
        verify_powers.check(f, verbose=True)

    if args.audit:
        audit(f, samples=args.audit, verbose=True)


if __name__ == "__main__":
    main()
