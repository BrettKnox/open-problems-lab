"""Census of Erdos problem #414: trajectories of h(n) = n + tau(n).

Iterate h(n) = n + tau(n), tau = number of divisors (A000005). EP #414
(Spiro 1977; Erdos-Graham 1980, p. 82) asks whether the trajectories of any
two starting points eventually merge. OpenProblemsLab/TauTrajectories.lean
proves every 2 <= m <= 30 merges with the trajectory of 2; this census
checks every 2 <= m <= M empirically and measures how the merging happens.

Method: an exact height-synchronized event sweep ("rivers").

  * tau is computed by a chunked divisor-pair sieve (numpy, uint16):
    tau(n) = 2 * #{d : d | n, d*d <= n} - [n is a square]. Exact integers
    throughout; no floating point in any decision.
  * Every start m in [2, M] spawns a walker at height m. All walkers advance
    through the sieved chunks in increasing height. A dict `arrivals` maps
    each walker's next landing position to the walker. Two walkers landing
    on the same integer have merged: strictly increasing trajectories that
    share a value coincide forever after (TauTrajectories.lean, merged_of_eq).
  * On a collision the surviving walker is the one whose stream carries the
    smallest start ("label"). This makes the census equivalent to processing
    starts in increasing order and asking when each trajectory first touches
    the union of the earlier ones: a collision position v lies on
    orbit(label of the partner), and every value of an earlier orbit is some
    live walker's landing position at sweep time v, so first collision =
    first contact, exactly (gate D checks this against brute force).
  * Riders: when stream S dies into absorber A at height v, every start
    carried by S transfers to A with an offset so that its cumulative step
    count (and parity-flip count) stays exact. When the absorber carries the
    start 2, the transferring starts have just touched the trajectory of 2
    itself (the walker born at 2 IS the orbit of 2), and their depth-to-2 is
    finalized at v.
  * Termination: above M no walkers spawn, so when one stream remains
    nothing can ever happen again; the sweep stops. The last merge height
    H* is the exact height at which a single stream is achieved. B is only
    a safety cap (default 2*10^9), never reached in practice.

Parity structure (the mechanism): tau(n) is odd iff n is a square, so
h preserves parity except at squares. Two streams in opposite parity phases
occupy disjoint residues and cannot merge until one of them steps off a
square. The sweep records, per merge, the height since the later
phase-establishing event (birth or square-flip), and per start, the number
of parity flips its chain needed before joining the stream of 2.

Memory: O(chunk) for the sieve plus five flat arrays over the starts
(d1, d2 int32; flips int16; join value uint32; born-phase byte):
~15 bytes/start, 1.5 GB at M = 10^8.

    python census.py --M 10000000 --verify --negative-control
    python census.py --M 100000000            # stretch census
    python census.py --ladder                 # timing/H* scaling table
    python census.py --M 1000000 --bfile b064491.txt   # fully offline
"""

from __future__ import annotations

import argparse
import hashlib
import os
import platform
import sys
import time
import urllib.request
from array import array
from collections import deque
from math import isqrt

import numpy as np

BFILE_URL = "https://oeis.org/A064491/b064491.txt"
CACHE = os.path.join(os.path.dirname(os.path.abspath(__file__)), "b064491.txt")

# Witnesses from TauTrajectories.lean, merge_upTo30: m -> (i, j) with
# step^[i] m = step^[j] 2, found by search, kernel-verified. The census
# cross-checks that these are exactly the minimal indices.
LEAN_WITNESS = {
    2: (0, 0), 3: (2, 2), 4: (0, 1), 5: (1, 2), 6: (3, 5), 7: (0, 2),
    8: (1, 4), 9: (0, 3), 10: (2, 5), 11: (8, 8), 12: (0, 4), 13: (7, 8),
    14: (1, 5), 15: (6, 8), 16: (5, 8), 17: (6, 8), 18: (0, 5), 19: (5, 8),
    20: (3, 8), 21: (4, 8), 22: (3, 8), 23: (4, 8), 24: (0, 6), 25: (3, 8),
    26: (2, 8), 27: (13, 14), 28: (2, 8), 29: (13, 14), 30: (1, 8),
}


def tau_trial(n: int) -> int:
    """tau(n) by trial division. Independent reference, shares no code with
    the sieve."""
    t = 0
    d = 1
    while d * d < n:
        if n % d == 0:
            t += 2
        d += 1
    if d * d == n:
        t += 1
    return t


def sieve_tau(lo: int, hi: int) -> np.ndarray:
    """tau(n) for n in [lo, hi) as uint16, by the divisor-pair sieve:
    tau(n) = 2 * #{d : d | n, d*d <= n} - [n is a square]."""
    if not 1 <= lo < hi:
        raise ValueError("need 1 <= lo < hi")
    tau = np.zeros(hi - lo, dtype=np.uint16)
    for d in range(1, isqrt(hi - 1) + 1):
        start = d * d if d * d > lo else lo
        start = -(-start // d) * d  # round up to a multiple of d
        if start < hi:
            tau[start - lo::d] += 2
    s0 = isqrt(lo - 1) + 1 if lo > 1 else 1
    s1 = isqrt(hi - 1)
    if s1 >= s0:
        sq = np.arange(s0, s1 + 1, dtype=np.int64) ** 2 - lo
        tau[sq] -= 1
    return tau


def load_bfile(path: str | None = None, url: str = BFILE_URL) -> list[int]:
    """A064491 terms [a(1), a(2), ...]. Downloads to a local cache on first
    use (gitignored: OEIS content is CC BY-NC-SA); later runs are offline."""
    path = path or CACHE
    if not os.path.exists(path):
        req = urllib.request.Request(url, headers={"User-Agent": "OpenProblemsLab/1.0"})
        with urllib.request.urlopen(req, timeout=120) as r:
            data = r.read()
        with open(path, "wb") as fh:
            fh.write(data)
        print(f"downloaded {url} -> {path} ({len(data)} bytes)")
    ns, vs = [], []
    with open(path, "r", encoding="ascii") as fh:
        for line in fh:
            line = line.strip()
            if not line or line.startswith("#"):
                continue
            a, b = line.split()
            ns.append(int(a))
            vs.append(int(b))
    if ns != list(range(1, len(ns) + 1)):
        raise ValueError("b-file indices are not 1..N contiguous")
    return vs


# stream fields: [label, steps, flips, riders, last_flip_pos, lf_is_birth, lf_square]
_L, _ST, _FL, _RD, _LF, _LB, _SQ = range(7)


def census(M: int, B: int = 2_000_000_000, chunk: int = 1 << 23,
           record_v1: bool = False, corrupt: dict | None = None,
           quiet: bool = False, collect_R: int = 4096) -> dict:
    """Run the sweep for all starts 2..M. Returns a dict of arrays/records.

    record_v1: also store each start's first-contact value (gate D needs it).
    corrupt:   {n: delta} added to sieved tau (negative controls only).
    """
    if M < 3:
        raise ValueError("M >= 3")
    t_all = time.perf_counter()
    size = M + 1
    d1 = array('i', [-1]) * size      # steps to first contact w/ earlier traj
    d2 = array('i', [-1]) * size      # steps to join the trajectory of 2
    cf = array('h', [-1]) * size      # parity flips of the chain up to join
    v2 = array('I', [0]) * size       # join value (on the orbit of 2)
    v1 = array('I', [0]) * size if record_v1 else None
    bs2 = bytearray(size)             # born in the same phase as the 2-stream?
    assert d1.itemsize == 4 and v2.itemsize == 4 and cf.itemsize == 2

    arrivals: dict = {}
    alive = 0
    apar = [0, 0]                     # alive streams per parity phase
    parity2 = 0                       # current phase of the 2-stream
    stream2 = None
    Rlist: list[int] = []             # prefix of the orbit of 2
    squaresR: list[int] = []          # squares stepped from by the 2-stream
    late: list[dict] = []             # merge events above M (full detail)
    last10: deque = deque(maxlen=10)  # highest merge events
    hw_flip: dict = {}                # wait histogram, flip-anchored merges
    hw_birth: dict = {}               # wait histogram, birth-anchored merges
    births = deaths = into2 = events = 0
    max_wait = (-1, None)
    samples: list[tuple] = []
    HSTAR = None
    finished = False
    sieve_s = 0.0

    def die(S, A, n):
        """Stream S is absorbed by A at height n (both walkers landed on n)."""
        nonlocal deaths, into2, HSTAR, max_wait
        m0 = S[_L]
        d = S[_ST]
        d1[m0] = d
        if v1 is not None:
            v1[m0] = n
        # parity-mechanism stats: later phase-establishing event of the pair
        if S[_LF] >= A[_LF]:
            f, birth, sq = S[_LF], S[_LB], S[_SQ]
        else:
            f, birth, sq = A[_LF], A[_LB], A[_SQ]
        w = n - f
        h = hw_birth if birth else hw_flip
        b = w.bit_length()
        h[b] = h.get(b, 0) + 1
        if w > max_wait[0]:
            max_wait = (w, (n, m0, A[_L], birth, None if birth else sq))
        deaths += 1
        if A[_L] == 2:
            into2 += 1
            d2[m0] = d
            v2[m0] = n
            cf[m0] = S[_FL]
            Ss, Sf = S[_ST], S[_FL]
            for (m, os_, of_) in S[_RD]:
                d2[m] = Ss + os_
                v2[m] = n
                cf[m] = Sf + of_
        else:
            Ar, As, Af = A[_RD], A[_ST], A[_FL]
            Ar.append((m0, d - As, S[_FL] - Af))
            Ss, Sf = S[_ST], S[_FL]
            for (m, os_, of_) in S[_RD]:
                Ar.append((m, Ss + os_ - As, Sf + of_ - Af))
        HSTAR = n
        last10.append((n, m0, d, A[_L]))
        if n > M:
            late.append(dict(v=n, loser=m0, depth=d, into=A[_L], wait=w,
                             anchored_at_birth=birth,
                             enabling_square=None if birth else sq,
                             starts_carried=len(S[_RD]) + 1))

    lo = 2
    while not finished:
        if lo >= B:
            n_bad = int(np.count_nonzero(
                np.frombuffer(d2, dtype=np.int32)[2:] < 0))
            raise RuntimeError(
                f"bound B = {B:,} reached with {alive} streams alive and "
                f"{n_bad} starts unmerged; positions {sorted(arrivals)[:8]}")
        hi = min(lo + chunk, B)
        t_s = time.perf_counter()
        ta = sieve_tau(lo, hi)
        if corrupt:
            for pos, delta in corrupt.items():
                if lo <= pos < hi:
                    ta[pos - lo] += delta
        tl = ta.tolist()
        sieve_s += time.perf_counter() - t_s

        # ---- dense phase: every n <= M spawns a start -------------------
        # arrivals[v] is always a list of the streams whose next landing is v
        n_top = min(hi, M + 1)
        pop = arrivals.pop
        for n, t in zip(range(lo, n_top), tl):
            entry = pop(n, None)
            if entry is None:
                # fresh stream born at n
                par = n & 1
                if par == parity2:
                    bs2[n] = 1
                S = [n, 0, 0, [], n, True, 0]
                births += 1
                alive += 1
                nxt = n + t
                if t & 1:
                    if isqrt(n) ** 2 != n:
                        raise AssertionError(f"tau({n}) odd but {n} not a square")
                    S[_FL] = 1
                    S[_LF] = nxt
                    S[_LB] = False
                    S[_SQ] = n
                    apar[1 - par] += 1
                else:
                    apar[par] += 1
                if n == 2:
                    stream2 = S
                    parity2 = nxt & 1
                    Rlist.append(2)
                    Rlist.append(nxt)
                    d2[2] = 0
                    v2[2] = 2
                    cf[2] = 0
                    bs2[2] = 1
                    if v1 is not None:
                        v1[2] = 2
                arrivals.setdefault(nxt, []).append(S)
                continue
            # occupied: walker(s) landed on n
            events += len(entry)
            A = entry[0]
            for S in entry:
                S[_ST] += 1
                if S[_L] < A[_L]:
                    A = S
            for S in entry:
                if S is not A:
                    die(S, A, n)
                    alive -= 1
                    apar[n & 1] -= 1
            # start n rides the stream passing through it (depth 0)
            d1[n] = 0
            if (n & 1) == parity2:
                bs2[n] = 1
            if A[_L] == 2:
                d2[n] = 0
                v2[n] = n
                cf[n] = 0
                if v1 is not None:
                    v1[n] = n
            else:
                A[_RD].append((n, -A[_ST], -A[_FL]))
            if v1 is not None:
                v1[n] = n
            # step the surviving walker
            nxt = n + t
            if t & 1:
                if isqrt(n) ** 2 != n:
                    raise AssertionError(f"tau({n}) odd but {n} not a square")
                A[_FL] += 1
                A[_LF] = nxt
                A[_LB] = False
                A[_SQ] = n
                apar[n & 1] -= 1
                apar[nxt & 1] += 1
                if A is stream2:
                    parity2 = nxt & 1
                    squaresR.append(n)
            if A is stream2 and len(Rlist) < collect_R:
                Rlist.append(nxt)
            arrivals.setdefault(nxt, []).append(A)

        # ---- sparse phase: above M, only walker events ------------------
        if hi > M:
            while arrivals:
                if alive == 1:
                    finished = True
                    break
                n = min(arrivals)
                if n >= hi:
                    break
                entry = pop(n)
                t = tl[n - lo]
                events += len(entry)
                A = entry[0]
                for S in entry:
                    S[_ST] += 1
                    if S[_L] < A[_L]:
                        A = S
                for S in entry:
                    if S is not A:
                        die(S, A, n)
                        alive -= 1
                        apar[n & 1] -= 1
                nxt = n + t
                if t & 1:
                    if isqrt(n) ** 2 != n:
                        raise AssertionError(f"tau({n}) odd but {n} not a square")
                    A[_FL] += 1
                    A[_LF] = nxt
                    A[_LB] = False
                    A[_SQ] = n
                    apar[n & 1] -= 1
                    apar[nxt & 1] += 1
                    if A is stream2:
                        parity2 = nxt & 1
                        squaresR.append(n)
                if A is stream2 and len(Rlist) < collect_R:
                    Rlist.append(nxt)
                arrivals.setdefault(nxt, []).append(A)

        samples.append((hi, alive, apar[0], apar[1]))
        if not quiet:
            print(f"  chunk [{lo:,}, {hi:,})  alive={alive}"
                  f" (even-phase {apar[0]}, odd-phase {apar[1]})"
                  f"  [{time.perf_counter() - t_all:.1f}s]")
        lo = hi

    # ---- invariants -----------------------------------------------------
    assert alive == 1 and len(arrivals) == 1, "sweep ended without one stream"
    slot = next(iter(arrivals.values()))
    assert len(slot) == 1, "survivor slot holds several streams"
    survivor = slot[0]
    assert survivor is stream2 and survivor[_L] == 2, \
        "surviving stream is not the one containing 2"
    nd1 = np.frombuffer(d1, dtype=np.int32)
    nd2 = np.frombuffer(d2, dtype=np.int32)
    ncf = np.frombuffer(cf, dtype=np.int16)
    nv2 = np.frombuffer(v2, dtype=np.uint32)
    nbs = np.frombuffer(bs2, dtype=np.uint8)
    assert nd1[2] == -1 and int(nd1[3:].min()) >= 0, "unfinalized d1"
    assert int(nd2[2:].min()) >= 0, "unfinalized d2"
    assert int(ncf[2:].min()) >= 0, "unfinalized flip count"
    assert HSTAR is not None

    dig = hashlib.sha256()
    dig.update(nd1.tobytes())
    dig.update(nd2.tobytes())
    dig.update(nv2.tobytes())
    total_s = time.perf_counter() - t_all
    return dict(
        M=M, B=B, chunk=chunk, Hstar=HSTAR, d1=nd1, d2=nd2, cf=ncf, v2=nv2,
        bs2=nbs, v1=(np.frombuffer(v1, dtype=np.uint32) if v1 is not None else None),
        births=births, deaths=deaths, into2=into2, events=events,
        late=late, last10=list(last10), hw_flip=hw_flip, hw_birth=hw_birth,
        max_wait=max_wait, samples=samples, Rlist=Rlist, squaresR=squaresR,
        R_steps=survivor[_ST], R_flips=survivor[_FL],
        digest=dig.hexdigest()[:16], total_s=total_s, sieve_s=sieve_s)


def brute(M: int, cap: int = 200_000):
    """Independent reference: trial-division tau, explicit orbit sets,
    starts processed in increasing order. Returns (d1, v1, d2, v2) dicts."""
    R = []
    x = 2
    while x <= cap:
        R.append(x)
        x += tau_trial(x)
    Rset = set(R)
    top = R[-1]
    visited = set(R)
    d1, v1, d2, v2 = {}, {}, {2: 0}, {2: 2}
    for m in range(3, M + 1):
        x, d = m, 0
        while x not in Rset:
            x += tau_trial(x)
            d += 1
            if x > top:
                raise RuntimeError("brute cap too small (d2 walk)")
        d2[m], v2[m] = d, x
        x, d = m, 0
        path = []
        while x not in visited:
            path.append(x)
            x += tau_trial(x)
            d += 1
            if x > top:
                raise RuntimeError("brute cap too small (d1 walk)")
        d1[m], v1[m] = d, x
        visited.update(path)
    return d1, v1, d2, v2


# ---------------------------------------------------------------------------
# validation gates
# ---------------------------------------------------------------------------

def gate_sieve_vs_trial(samples: int = 10_000, seed: int = 20260820,
                        hi_limit: int = 50_000_000) -> None:
    """(A) chunked sieve vs trial division on random n, plus window edges."""
    import random
    rng = random.Random(seed)
    t0 = time.perf_counter()
    ta = sieve_tau(2, 2000)
    for n in range(2, 2000):
        assert int(ta[n - 2]) == tau_trial(n), f"sieve wrong at {n}"
    nwin = 25
    per = samples // nwin
    width = 400_000
    for _ in range(nwin):
        lo = rng.randrange(2, hi_limit - width)
        ta = sieve_tau(lo, lo + width)
        for n in (lo, lo + width - 1):
            assert int(ta[n - lo]) == tau_trial(n), f"sieve wrong at edge {n}"
        for _ in range(per):
            n = rng.randrange(lo, lo + width)
            assert int(ta[n - lo]) == tau_trial(n), f"sieve wrong at {n}"
    print(f"  ok   (A) sieve vs trial division: n = 2..1999 exhaustive + "
          f"{nwin * per:,} random n in {nwin} windows up to {hi_limit:,} "
          f"(+ window edges)  [{time.perf_counter() - t0:.1f}s]")


def gate_parity_square(limit: int = 1_000_000, tau_arr: np.ndarray | None = None,
                       verbose: bool = True) -> None:
    """(B) tau(n) odd <=> n is a square, for n = 1..limit, elementwise."""
    t0 = time.perf_counter()
    ta = tau_arr if tau_arr is not None else sieve_tau(1, limit + 1)
    odd = (ta & 1).astype(bool)
    is_sq = np.zeros(limit, dtype=bool)
    is_sq[np.arange(1, isqrt(limit) + 1, dtype=np.int64) ** 2 - 1] = True
    if not np.array_equal(odd, is_sq):
        bad = int(np.flatnonzero(odd != is_sq)[0]) + 1
        raise AssertionError(
            f"tau parity/square mismatch at n={bad}: tau={int(ta[bad - 1])}, "
            f"square={isqrt(bad) ** 2 == bad}")
    if verbose:
        print(f"  ok   (B) tau(n) odd <=> n square, elementwise on n = 1..{limit:,}"
              f"  [{time.perf_counter() - t0:.1f}s]")


def gate_bfile(bpath: str | None = None, corrupt_step: int | None = None,
               verbose: bool = True) -> int:
    """(C) the sieve-driven stepper reproduces OEIS A064491, all terms."""
    t0 = time.perf_counter()
    b = load_bfile(bpath)
    assert b[:9] == [1, 2, 4, 7, 9, 12, 18, 24, 32], "b-file head unexpected"
    ta = sieve_tau(1, b[-1] + 1)
    x = 1
    for k in range(1, len(b) + 1):
        if x != b[k - 1]:
            raise AssertionError(
                f"A064491 mismatch at term {k}: computed {x}, b-file {b[k - 1]}")
        if k == len(b):
            break
        t = int(ta[x - 1])
        if corrupt_step is not None and k == corrupt_step:
            t += 1
        x += t
    if verbose:
        print(f"  ok   (C) OEIS A064491: stepper reproduces all {len(b):,} terms "
              f"of the b-file (a({len(b)}) = {b[-1]:,})  "
              f"[{time.perf_counter() - t0:.1f}s]")
    return len(b)


def gate_brute_vs_sweep(Mtest: int = 3000, chunk: int = 1024,
                        corrupt: dict | None = None, verbose: bool = True) -> None:
    """(D) sweep vs independent brute force: d1, v1, d2, v2 for every start."""
    t0 = time.perf_counter()
    res = census(Mtest, B=10 ** 7, chunk=chunk, record_v1=True, quiet=True,
                 corrupt=corrupt)
    bd1, bv1, bd2, bv2 = brute(Mtest)
    assert res["d2"][2] == 0 and res["v2"][2] == 2
    for m in range(3, Mtest + 1):
        ok = (int(res["d1"][m]) == bd1[m] and int(res["v1"][m]) == bv1[m]
              and int(res["d2"][m]) == bd2[m] and int(res["v2"][m]) == bv2[m])
        if not ok:
            raise AssertionError(
                f"sweep vs brute mismatch at m={m}: sweep "
                f"d1={int(res['d1'][m])} v1={int(res['v1'][m])} "
                f"d2={int(res['d2'][m])} v2={int(res['v2'][m])}, brute "
                f"d1={bd1[m]} v1={bv1[m]} d2={bd2[m]} v2={bv2[m]}")
    if verbose:
        print(f"  ok   (D) sweep == brute force on every start m <= {Mtest} "
              f"(d1, v1, d2, v2 all equal; chunk={chunk})  "
              f"[{time.perf_counter() - t0:.1f}s]")


def gate_chunk_invariance(Mtest: int = 100_000,
                          chunks=(32768, 99991, 1 << 20)) -> None:
    """(E) the sweep result is invariant under the chunk size."""
    t0 = time.perf_counter()
    ref = None
    for c in chunks:
        r = census(Mtest, chunk=c, quiet=True)
        key = (r["digest"], r["Hstar"], r["R_steps"], r["deaths"])
        if ref is None:
            ref = key
        elif key != ref:
            raise AssertionError(f"chunk size {c} changed the result: {key} != {ref}")
    print(f"  ok   (E) chunk invariance at M = {Mtest:,}: chunk sizes "
          f"{list(chunks)} give identical results (digest {ref[0]})  "
          f"[{time.perf_counter() - t0:.1f}s]")


def gate_lean_witnesses(res: dict) -> None:
    """(G) census merge data for m <= 30 equals the kernel-checked witnesses
    in TauTrajectories.lean (merge_upTo30), and those witnesses are minimal."""
    R = res["Rlist"]
    for m, (i, j) in LEAN_WITNESS.items():
        di = int(res["d2"][m])
        v = int(res["v2"][m])
        assert di == i, f"m={m}: census depth {di} != Lean witness i={i}"
        assert R[j] == v, f"m={m}: census join {v} != Lean witness step^[{j}]2={R[j]}"
    print("  ok   (G) m <= 30: census merge depths and join points equal the "
          "kernel-checked Lean witnesses (merge_upTo30), all 29 starts")


def run_gates(bpath: str | None) -> None:
    print("--- validation gates ---")
    gate_sieve_vs_trial()
    gate_parity_square()
    gate_bfile(bpath)
    gate_brute_vs_sweep(300, chunk=37, verbose=False)
    gate_brute_vs_sweep(3000, chunk=1024)
    gate_chunk_invariance()
    print("all gates: PASS")


def negative_controls(bpath: str | None, seed: int = 20260820) -> None:
    """Each gate must catch a deliberately corrupted input."""
    import random
    rng = random.Random(seed)
    print("--- negative controls (each corruption must be caught) ---")
    n0 = rng.randrange(2, 1_000_000)

    # 1: parity-breaking tau corruption -> caught by (B)
    ta = sieve_tau(1, 1_000_001)
    ta[n0 - 1] += 1
    try:
        gate_parity_square(tau_arr=ta, verbose=False)
        raise SystemExit("control 1 NOT caught")
    except AssertionError as e:
        print(f"  control 1: tau({n0}) += 1  -> (B) parity gate: CAUGHT ({e})")

    # 2: parity-preserving corruption -> (B) passes, trial division catches
    ta = sieve_tau(1, 1_000_001)
    ta[n0 - 1] += 2
    gate_parity_square(tau_arr=ta, verbose=False)  # must NOT catch it
    if int(ta[n0 - 1]) == tau_trial(n0):
        raise SystemExit("control 2 NOT caught")
    print(f"  control 2: tau({n0}) += 2  -> (B) passes as expected (parity "
          "preserved), trial-division comparison: CAUGHT")

    # 3: one corrupted step in the A064491 walk -> caught by (C)
    try:
        gate_bfile(bpath, corrupt_step=500, verbose=False)
        raise SystemExit("control 3 NOT caught")
    except AssertionError as e:
        print(f"  control 3: step 500 of the A064491 walk corrupted -> (C): "
              f"CAUGHT ({e})")

    # 4: corrupted tau inside the sweep -> caught by (D) vs brute force
    try:
        gate_brute_vs_sweep(3000, corrupt={12: 2}, verbose=False)
        raise SystemExit("control 4 NOT caught")
    except AssertionError as e:
        msg = str(e)
        print(f"  control 4: sweep run with tau(12) += 2 -> (D) brute-force "
              f"comparison: CAUGHT ({msg[:80]}...)")
    print("negative controls: PASS (every corruption caught)")


# ---------------------------------------------------------------------------
# reporting
# ---------------------------------------------------------------------------

def _hist_lines(h: dict) -> list[str]:
    out = []
    for b in sorted(h):
        if b == 0:
            rng = "0"
        else:
            rng = f"{1 << (b - 1)}..{(1 << b) - 1}"
        out.append(f"      wait {rng:>16}: {h[b]:,}")
    return out


def summarize(res: dict) -> None:
    M, H = res["M"], res["Hstar"]
    d1, d2, cf, v2, bs2 = res["d1"], res["d2"], res["cf"], res["v2"], res["bs2"]
    print("\n--- census summary ---")
    print(f"starts 2..{M:,}; every one of them merged into the single stream "
          f"containing 2: YES")
    print(f"single stream achieved at H* = {H:,} (last merge; "
          f"{(H - M) / M:+.3%} above M); bound B = {res['B']:,} never binding")
    print(f"walkers born {res['births']:,} ({res['births'] / (M - 1):.2%} of "
          f"starts; the rest spawned on an already-visited value), "
          f"deaths {res['deaths']:,}, of which direct merges into the "
          f"2-stream {res['into2']:,} ({res['into2'] / res['deaths']:.1%})")
    print(f"orbit of 2: {res['R_steps']:,} steps below H*; parity flips "
          f"(squares stepped from): {res['R_flips']:,}; first squares on the "
          f"orbit: {res['squaresR'][:6]}{' ...' if len(res['squaresR']) > 6 else ''}")
    if res["squaresR"]:
        print(f"last square on the orbit of 2 below H*: {res['squaresR'][-1]:,}")

    # d1
    bc1 = np.bincount(d1[3:])
    mx1 = int(d1[3:].max())
    hold1 = (np.flatnonzero(d1 == mx1)).tolist()[:5]
    print(f"\nd1 = steps to first contact with any earlier trajectory "
          f"(starts 3..{M:,}):")
    print(f"  mean {d1[3:].mean():.4f}; P(d1=0) = {bc1[0] / (M - 2):.4f}")
    for d in range(len(bc1)):
        if bc1[d]:
            print(f"    d1={d:>2}: {int(bc1[d]):>12,}")
    print(f"  max d1 = {mx1}, holder(s): {hold1}")

    # d2
    mx2 = int(d2[2:].max())
    am2 = int(np.argmax(d2[2:]) + 2)
    q = np.percentile(d2[2:], [50, 90, 99, 99.9])
    print(f"\nd2 = steps to join the trajectory of 2 (starts 2..{M:,}):")
    print(f"  mean {d2[2:].mean():.3f}; median {q[0]:.0f}; p90 {q[1]:.0f}; "
          f"p99 {q[2]:.0f}; p99.9 {q[3]:.0f}; max {mx2}")
    print(f"  max-d2 holder: m = {am2:,} joins at {int(v2[am2]):,} after "
          f"{mx2} steps with {int(cf[am2])} parity flips")
    bc2 = np.bincount(d2[2:])
    head = min(len(bc2), 13)
    for d in range(head):
        if bc2[d]:
            print(f"    d2={d:>2}: {int(bc2[d]):>12,}")
    if len(bc2) > head:
        print(f"    d2>{head - 1}: {int(bc2[head:].sum()):>12,}")

    # join heights
    n_above = int(np.count_nonzero(v2[2:].astype(np.int64) > M))
    mmax = int(np.argmax(v2[2:]) + 2)
    climb = 0
    for a in range(2, M + 1, 10_000_000):
        b = min(a + 10_000_000, M + 1)
        c = int((v2[a:b].astype(np.int64) - np.arange(a, b)).max())
        climb = max(climb, c)
    print(f"\njoin heights: {n_above:,} starts joined the 2-stream above M; "
          f"the last, m = {mmax:,}, at H* = {H:,}")
    print(f"  largest climb v2 - m = {climb:,}")

    # parity mechanism
    born_same = int(np.count_nonzero(bs2[2:]))
    fl_bc = np.bincount(cf[2:])
    n0f = int(fl_bc[0]) if len(fl_bc) else 0
    same_mask = bs2[2:] != 0
    flip_mask = cf[2:] > 0
    tt = int(np.count_nonzero(same_mask & flip_mask))
    tf = int(np.count_nonzero(same_mask & ~flip_mask))
    ot = int(np.count_nonzero(~same_mask & flip_mask))
    of = int(np.count_nonzero(~same_mask & ~flip_mask))
    print(f"\nparity mechanism (tau odd exactly at squares; h flips parity "
          f"exactly there):")
    print(f"  starts born in the same phase as the 2-stream: {born_same:,} "
          f"({born_same / (M - 1):.2%})")
    print(f"  chain parity flips before joining 2-stream: "
          + ", ".join(f"{k}: {int(c):,}" for k, c in enumerate(fl_bc) if c))
    print(f"  cross-tab born-phase x chain-flips:")
    print(f"    same phase,     0 flips: {tf:>12,}   (plain same-phase collision)")
    print(f"    same phase,  >=1 flips:  {tt:>12,}")
    print(f"    opposite phase, 0 flips: {of:>12,}   (the 2-stream flipped instead)")
    print(f"    opposite phase, >=1 flips: {ot:>10,}")
    wf = sum(res["hw_flip"].values())
    wb = sum(res["hw_birth"].values())
    print(f"  walker merges anchored at a birth: {wb:,}; anchored at a parity "
          f"flip (square): {wf:,}")
    print(f"  height waited from the later phase-establishing event to the "
          f"merge (flip-anchored):")
    for line in _hist_lines(res["hw_flip"]):
        print(line)
    w, det = res["max_wait"]
    if det:
        n, m0, into, birth, sq = det
        anch = "birth" if birth else f"flip at square {sq:,}"
        print(f"  longest wait: {w:,} (merge at {n:,}, start {m0:,} into "
              f"stream {into}, anchored at {anch})")

    print(f"\nhighest merge events (v, dying stream's start, its depth, "
          f"absorbing label):")
    for (n, m0, d, al) in res["last10"]:
        print(f"    {n:>12,}  m={m0:<12,} d1={d:<5} into stream {al}")
    if res["late"]:
        print(f"  merges above M = {M:,}: {len(res['late'])}")
        for e in res["late"]:
            sq = (f"square {e['enabling_square']:,}" if e["enabling_square"]
                  else "birth")
            print(f"    v={e['v']:,}  loser={e['loser']:,} (depth "
                  f"{e['depth']}, carrying {e['starts_carried']} starts) into "
                  f"stream {e['into']}; waited {e['wait']:,} from {sq}")
    else:
        print(f"  merges above M: none (single stream already below M)")

    print("\nalive-stream count by height (streams crossing, ~ln x expected):")
    for (hgt, a, pe, po) in res["samples"][:40]:
        print(f"    up to {hgt:>13,}: alive {a:>3} ({pe} even-phase, {po} odd-phase)")

    # m <= 30 vs Lean
    if M >= 30:
        R = res["Rlist"]
        print("\nm <= 30 (cross-check vs TauTrajectories.lean merge_upTo30):")
        print("    m   d2  join   = step^[j] 2, j")
        for m in range(2, 31):
            v = int(res["v2"][m])
            j = R.index(v)
            print(f"   {m:>2}  {int(res['d2'][m]):>3}  {v:>4}   j={j}")
        gate_lean_witnesses(res)

    print(f"\ndigest (d1|d2|v2 sha256/16): {res['digest']}")
    print(f"timing: sieve {res['sieve_s']:.1f}s + sweep "
          f"{res['total_s'] - res['sieve_s']:.1f}s = {res['total_s']:.1f}s "
          f"({res['events']:,} walker landings)")


def ladder(Ms=(10 ** 4, 10 ** 5, 10 ** 6, 10 ** 7)) -> None:
    import math
    print("--- scaling ladder ---")
    print("        M       time        H*      H*-M   (H*-M)/(sqrt(M) ln M)   "
          "max d1   max d2")
    for M in Ms:
        r = census(M, quiet=True)
        gap = r["Hstar"] - M
        norm = gap / (math.sqrt(M) * math.log(M))
        print(f"  {M:>9,}  {r['total_s']:>7.1f}s  {r['Hstar']:>12,} {gap:>9,}"
              f"   {norm:>8.2f}               {int(r['d1'][3:].max()):>4}"
              f"     {int(r['d2'][2:].max()):>4}")


def main() -> None:
    p = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    p.add_argument("--M", type=int, default=None, help="census all starts 2..M")
    p.add_argument("--B", type=int, default=2_000_000_000, help="safety bound")
    p.add_argument("--chunk", type=int, default=1 << 23, help="sieve chunk size")
    p.add_argument("--verify", action="store_true", help="run validation gates")
    p.add_argument("--negative-control", action="store_true")
    p.add_argument("--ladder", action="store_true", help="timing/H* scaling table")
    p.add_argument("--bfile", type=str, default=None, help="local A064491 b-file")
    p.add_argument("--save", type=str, default=None, help="save arrays to .npz")
    args = p.parse_args()

    print(f"census of EP #414 trajectories, h(n) = n + tau(n)  "
          f"[python {platform.python_version()}, numpy {np.__version__}, "
          f"{platform.system()} {platform.machine()}]")
    if args.verify:
        run_gates(args.bfile)
    if args.negative_control:
        negative_controls(args.bfile)
    if args.ladder:
        ladder()
    if args.M is not None:
        print(f"\n--- census: M = {args.M:,}, B = {args.B:,}, "
              f"chunk = {args.chunk:,} ---")
        res = census(args.M, B=args.B, chunk=args.chunk)
        summarize(res)
        if args.save:
            np.savez_compressed(args.save, d1=res["d1"], d2=res["d2"],
                                cf=res["cf"], v2=res["v2"], bs2=res["bs2"])
            print(f"arrays saved to {args.save}")
    if not (args.verify or args.negative_control or args.ladder
            or args.M is not None):
        p.print_help()


if __name__ == "__main__":
    main()
