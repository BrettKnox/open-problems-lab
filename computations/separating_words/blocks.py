"""Hunting N(5): the first length at which 5 states stop separating.

`N(k)` is the largest `n` such that some `k`-state DFA separates every pair of
distinct binary words of length `n`.  Exhaustive search (separate.py) gives

    N(1) = 0,  N(2) = 3,  N(3) = 9,  N(4) = 17,  N(5) >= 30,

and stops at `N(5) >= 30` because deciding `n = 31` exhaustively needs ~17 GiB:
it has to detect a collision among all `2^n` signatures.

But verifying and *witnessing* are not equally hard.  A witness is a single
unseparable pair, and the known ones are extremely structured:

    k = 3:  1^2 0^8   vs  1^8 0^2      (n = 10)
    k = 4:  1^3 0^15  vs  1^15 0^3     (n = 18)

Both are two-block words `1^a 0^(n-a)`.  That family has only `n + 1` members
per length, so it can be pushed to lengths exhaustive search will never reach.
A collision inside it proves `N(5) < n` outright -- an upper bound, to set
against the verified lower bound `N(5) >= 30`.

The family also admits a much better algorithm than running each word.  Let
`g(q) = delta(q, 0)`.  The end state of `1^a 0^(n-a)` is `g^(n-a)(s_a)`, where
`s_a` is the state after `1^a`.  Sweeping `m = n - a` upward while iterating
`g` once per step evaluates the whole family in O(#functions * n) work instead
of O(#functions * n^2).

    python blocks.py --verify
    python blocks.py --k 5 --nmax 200
"""

from __future__ import annotations

import argparse
import sys
import time

import numpy as np

import separate as S


def two_block_end_states(T: np.ndarray, n: int, first: int = 1) -> np.ndarray:
    """End states of the n+1 words `first^a other^(n-a)`, a = 0..n.

    Returns (M, n+1) with column `a` holding the end state of `first^a
    other^(n-a)` under each transition function.
    """
    m = T.shape[0]
    ar = np.arange(m)
    other = 1 - first
    # s[:, a] = state after reading first^a
    s = np.empty((m, n + 1), np.uint8)
    cur = np.zeros(m, np.uint8)
    s[:, 0] = cur
    for a in range(1, n + 1):
        cur = T[ar, cur, first]
        s[:, a] = cur
    # A holds g^j, applied by sweeping j = 0..n and reading off a = n - j
    out = np.empty((m, n + 1), np.uint8)
    A = np.tile(np.arange(T.shape[1], dtype=np.uint8), (m, 1))  # g^0 = id
    for j in range(n + 1):
        out[:, n - j] = A[ar, s[:, n - j]]
        if j < n:
            A = T[ar[:, None], A, other]
    return out


def first_collision(T: np.ndarray, n: int, first: int = 1):
    """(a, b) with a < b and the two-block words of index a, b unseparable."""
    out = two_block_end_states(T, n, first)
    # hash each column (a full signature over every transition function)
    cols = np.ascontiguousarray(out.T)
    view = cols.view([('', cols.dtype)] * cols.shape[1]).ravel()
    _, inv, cnt = np.unique(view, return_inverse=True, return_counts=True)
    dup = np.flatnonzero(cnt > 1)
    if dup.size == 0:
        return None
    idx = np.flatnonzero(inv == dup[0])
    return int(idx[0]), int(idx[1])


def word(a: int, n: int, first: int = 1) -> np.ndarray:
    other = 1 - first
    return np.array([first] * a + [other] * (n - a), np.uint8)


def scan(k: int, nmin: int, nmax: int, verbose: bool = True):
    T = S.icdfa_upto(k)
    if verbose:
        print(f"k = {k}: {T.shape[0]:,} canonical transition functions "
              f"with <= {k} states")
    t0 = time.time()
    for n in range(nmin, nmax + 1):
        for first in (1, 0):
            hit = first_collision(T, n, first)
            if hit is not None:
                a, b = hit
                u, v = word(a, n, first), word(b, n, first)
                return {"n": n, "a": a, "b": b, "first": first,
                        "u": S.word_str(u), "v": S.word_str(v),
                        "seconds": time.time() - t0}
        if verbose and n % 10 == 0:
            print(f"  n = {n}: no two-block collision  "
                  f"[{time.time() - t0:.0f}s]", flush=True)
    return {"n": None, "seconds": time.time() - t0}


# --------------------------------------------------------------------------
# three-block words, to test whether two blocks is really the worst case
# --------------------------------------------------------------------------

def iterate_tables(T: np.ndarray, n: int, letter: int) -> np.ndarray:
    """(n+1, M, k) with entry [j] the map q -> delta(q, letter^j)."""
    m, k = T.shape[0], T.shape[1]
    ar = np.arange(m)[:, None]
    out = np.empty((n + 1, m, k), np.uint8)
    out[0] = np.tile(np.arange(k, dtype=np.uint8), (m, 1))
    for j in range(1, n + 1):
        out[j] = T[ar, out[j - 1], letter]
    return out


def three_block_collision(T: np.ndarray, n: int, first: int = 1,
                          chunk: int = 256):
    """Unseparable pair among words `first^a other^b first^c`, a+b+c = n."""
    m = T.shape[0]
    ar = np.arange(m)
    other = 1 - first
    G = iterate_tables(T, n, other)
    H = iterate_tables(T, n, first)
    trip = [(a, b, n - a - b)
            for a in range(1, n - 1) for b in range(1, n - a)]
    trip = [t for t in trip if t[2] >= 1]
    sigs = {}
    for s in range(0, len(trip), chunk):
        blk = trip[s:s + chunk]
        av = np.array([t[0] for t in blk])
        bv = np.array([t[1] for t in blk])
        cv = np.array([t[2] for t in blk])
        x = H[av[None, :], ar[:, None], 0]            # after first^a from q0
        y = G[bv[None, :], ar[:, None], x]            # then other^b
        z = H[cv[None, :], ar[:, None], y]            # then first^c
        cols = np.ascontiguousarray(z.T)
        for i in range(cols.shape[0]):
            key = cols[i].tobytes()
            if key in sigs:
                return sigs[key], blk[i]
            sigs[key] = blk[i]
    return None


def gates() -> None:
    # (A) the family reproduces the known first witness for k = 3
    r = scan(3, 1, 20, verbose=False)
    assert r["n"] == 10, r
    assert {r["u"], r["v"]} == {"1100000000", "1111111100"}, r
    print(f"  ok   (A) k=3: first two-block collision at n=10, "
          f"{r['u']} / {r['v']} -- matches the exhaustive witness")

    # (B) and for k = 4
    r = scan(4, 1, 25, verbose=False)
    assert r["n"] == 18, r
    assert {r["u"], r["v"]} == {"111000000000000000",
                                "111111111111111000"}, r
    print(f"  ok   (B) k=4: first two-block collision at n=18, "
          f"{r['u']} / {r['v']} -- matches the exhaustive witness")

    # (C) those witnesses really need more than k states (independent check
    # through separate.min_states, which shares no code with this file)
    for k, u, v in ((3, "1100000000", "1111111100"),
                    (4, "111000000000000000", "111111111111111000")):
        got = S.min_states(S.parse_word(u), S.parse_word(v), kmax=6)
        assert got is not None and got > k, (k, got)
    print("  ok   (C) both witnesses need strictly more than k states "
          "(min_states cross-check)")

    # (D) the fast two-block routine agrees with running the words directly
    rng = np.random.default_rng(20260903)
    T = S.icdfa_upto(4)
    for n in (5, 9, 14, 21):
        for first in (0, 1):
            fast = two_block_end_states(T, n, first)
            wb = np.stack([word(a, n, first) for a in range(n + 1)])
            slow = S.batch_states(T, wb)
            assert np.array_equal(fast, slow), (n, first)
    print("  ok   (D) fast sweep == batch_states on k=4, n in {5,9,14,21}")

    # (E) negative control: a pair that IS separated shows no collision
    assert first_collision(S.icdfa_upto(4), 9) is None
    assert first_collision(S.icdfa_upto(3), 9) is None
    print("  ok   (E) negative control: no collision at n=9 for k=3,4 "
          "(N(3)=9, N(4)=17)")

    # (F) the Demaine-Eisenstat-Shallit-Wilson bound N(k) <= 2k-3+lcm(1..k)
    # is EXACT on every value exhaustive search knows
    from math import lcm
    known = {1: 0, 2: 3, 3: 9, 4: 17}
    for k, v in known.items():
        pred = 2 * k - 3 + lcm(*range(1, k + 1)) if k > 1 else 0
        assert pred == v, (k, pred, v)
    print("  ok   (F) N(k) = 2k-3+lcm(1..k) reproduces N(1..4) = 0,3,9,17 "
          "exactly; predicts N(5) = 67")

    # (G) the three-block family agrees with running the words directly
    T = S.icdfa_upto(4)
    for n, (a, b, c) in ((9, (2, 3, 4)), (12, (5, 1, 6))):
        G = iterate_tables(T, n, 0)
        H = iterate_tables(T, n, 1)
        ar = np.arange(T.shape[0])
        x = H[a, ar, 0]; y = G[b, ar, x]; z = H[c, ar, y]
        w = np.array([1] * a + [0] * b + [1] * c, np.uint8)
        assert np.array_equal(z, S.batch_states(T, w[None])[:, 0]), (n, a, b, c)
    print("  ok   (G) three-block sweep == batch_states")
    print("all gates: PASS")


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__.split("\n")[0])
    ap.add_argument("--verify", action="store_true")
    ap.add_argument("--k", type=int, default=5)
    ap.add_argument("--nmin", type=int, default=1)
    ap.add_argument("--nmax", type=int, default=0)
    args = ap.parse_args()
    if args.verify:
        gates()
    if args.nmax:
        r = scan(args.k, args.nmin, args.nmax)
        if r["n"] is None:
            print(f"no two-block collision for k={args.k} up to n={args.nmax} "
                  f"[{r['seconds']:.0f}s]")
        else:
            print(f"\ncollision at n={r['n']}: {r['u']} / {r['v']}")
            u, v = S.parse_word(r["u"]), S.parse_word(r["v"])
            got = S.min_states(u, v, kmax=6)
            print(f"min_states cross-check: needs {got} states "
                  f"(> {args.k} required)")
            print(f"=> N({args.k}) < {r['n']}")
        print(f"total {r['seconds']:.0f}s")
    if not (args.verify or args.nmax):
        ap.print_help()
    return 0


if __name__ == "__main__":
    sys.exit(main())
