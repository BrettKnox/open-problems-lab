"""Exact values of the separating-words function sep(n).

For distinct binary words u != v of the same length n, minK(u,v) is the least
number of states of a DFA that accepts one of them and rejects the other, and

    sep(n) = max { minK(u,v) : |u| = |v| = n, u != v }.

Known: sep(n) = Omega(log n) (Demaine-Eisenstat-Shallit-Wilson 2011) and
sep(n) = O~(n^{1/3}) (Chase, STOC 2021); O(log n) is conjectured.  This module
computes sep(n) exactly by exhaustive search, with an independent brute-force
reference that shares no reasoning with the fast path.

==========================================================================
1. The reduction: accept sets are irrelevant
==========================================================================
Let delta be a transition function on a k-element state set with start state
q0, and write delta*(q0,w) for the state reached on w.  Claim:

    some k-state DFA separates u from v
      <=>  some k-state transition function delta and start q0 satisfy
           delta*(q0,u) != delta*(q0,v).

(=>) Acceptance of a word depends only on the state it ends in, so if the two
     runs ended in the same state the DFA would accept both or reject both.
(<=) Given delta with delta*(q0,u) != delta*(q0,v), take F = {delta*(q0,u)}.

So only transition functions are enumerated here, never accept sets -- a
factor 2^k saved, and more importantly the search becomes a question about
*end states*, which is what makes everything below possible.  The reduction is
not assumed: gate (A) below re-derives sep from the literal definition, accept
sets and all, and compares.

Two further reductions, both standard:

  * States unreachable from q0 can be deleted, so it suffices to enumerate
    *initially connected* transition structures with j <= k states.
  * Relabelling states does not change whether two runs end in different
    states, so we may fix q0 = 0 and require the remaining states to be
    numbered in BFS order (letter 0 before letter 1).  This is the canonical
    string of an ICDFA (Almeida-Moreira-Reis).  Counts over {0,1}:

        k       1     2      3       4        5          6
        #ICDFA  1    12    216    5248   160675    5931540

    versus k^(2k) = 1, 16, 729, 65536, 9765625, 2176782336 raw functions.

==========================================================================
2. sep is non-decreasing
==========================================================================
If delta*(0,u) = delta*(0,v) then delta*(0,ub) = delta*(0,vb) for any letter
b.  Contrapositive: any delta separating ub from vb already separates u from
v, so minK(ub,vb) >= minK(u,v) and hence sep(n+1) >= sep(n).  A theorem, not
an assumption -- but it is checked anyway, and it is what lets a single hard
pair at the first bad length serve as a witness at every larger length.

==========================================================================
3. The signature automaton
==========================================================================
Fix a set S of transition functions and define the signature

    sig_S(w) = ( delta*(0,w) )_{delta in S}.

Because each coordinate advances on its own, sig_S(wb) is a function of
sig_S(w) and b alone.  So the map w -> sig_S(w) is computed by a deterministic
automaton on tuples, and the array of signatures of all 2^(t+1) words of
length t+1 is obtained from the array for length t by one gather per delta:

    row_{t+1}[2x + b] = delta( row_t[x], b ).

Packing the pair (delta(q,0), delta(q,1)) into one uint16 makes each doubling
a single gather whose bytes already land in the right order, so the whole
length-n array for one delta costs 2^n gathers -- not n * 2^n, and with no
strided writes.  Two directions follow:

  UPPER BOUND.  If sig_S is injective on {0,1}^n for some S contained in the
  k-state functions, then sep(n) <= k.  Only a small S is needed (at least
  n / log2(k) machines, in practice not many more), so this is cheap.

  LOWER BOUND.  sep(n) > k iff sig_Delta_k is *not* injective, where Delta_k
  is the full canonical list.  Enumerating all of Delta_k over all 2^n words
  is far too expensive, so instead: refine with a growing S until the only
  remaining collision groups are small, then run *all* of Delta_k on the few
  surviving words.  A group that no delta in Delta_k splits is a genuinely
  unseparable set, and its pairs are exactly the hardest pairs.

The driver computes N(k) = max { n : sep(n) <= k } by running the levels
t = 1, 2, ... until the first genuine collision; then

    sep(n) = min { k : N(k) >= n }.

Memory is the binding constraint: one 64-bit signature hash per word of length
n, plus a bucketed sorted copy of a sixteenth of it, so n = 30 costs ~9 GiB and
each further n doubles that.  Signature *hashes* can collide, so every group
they propose is re-checked against the actual signatures before being believed;
equal signatures always hash equal, so no collision is ever missed.

==========================================================================
CLI
==========================================================================
    python separate.py --nmax 24 --kmax 5      # the sep(n) table
    python separate.py --pair 01101 10110      # minK for one pair
    python separate.py --verify                # all validation gates
    python separate.py --negative-control      # deliberately corrupted runs
"""

from __future__ import annotations

import argparse
import os
import sys
import time

import numpy as np

HERE = os.path.dirname(os.path.abspath(__file__))
CACHE = os.path.join(HERE, "icdfa_cache")

PRIME = np.uint64(0x100000001B3)
CHUNK = 1 << 20


# --------------------------------------------------------------------------
# words
# --------------------------------------------------------------------------
def bits_of(idx: int, n: int) -> np.ndarray:
    """Word of length n with index idx; the first letter is the high bit."""
    return np.array([(idx >> (n - 1 - i)) & 1 for i in range(n)], np.uint8)


def word_str(w) -> str:
    return "".join(str(int(b)) for b in w)


def parse_word(s: str) -> np.ndarray:
    if not s or any(c not in "01" for c in s):
        raise ValueError(f"not a binary word: {s!r}")
    return np.array([int(c) for c in s], np.uint8)


# --------------------------------------------------------------------------
# canonical transition functions (initially connected, start = 0, BFS-labelled)
# --------------------------------------------------------------------------
def icdfa_list(k: int, cache: bool = True) -> np.ndarray:
    """Every canonical k-state initially connected transition function.

    Positions 0..2k-1 hold delta(0,0), delta(0,1), delta(1,0), ... in BFS
    order.  A partial assignment is legal iff (a) the state whose transitions
    are being filled has already been discovered, and (b) every value is at
    most maxseen+1, so states are discovered in increasing order.  Returns
    shape (M, k, 2) uint8.
    """
    if k < 1:
        raise ValueError("k >= 1")
    if k > 6:
        # k = 7 is 256,182,290 functions: 3.6 GB on disk, and useless anyway,
        # since sep(n) <= 5 for every n this method can reach.
        raise ValueError(f"k = {k} would need {k ** (2 * k) // 720:,}+ functions; "
                         "k <= 6 only")
    if k == 1:
        return np.zeros((1, 1, 2), np.uint8)
    path = os.path.join(CACHE, f"icdfa{k}.npy")
    if cache and os.path.exists(path):
        return np.load(path)

    part = np.zeros((1, 0), np.uint8)
    ms = np.zeros(1, np.int64)  # largest state discovered so far
    for p in range(2 * k):
        state = p // 2
        keep = ms >= state
        part, ms = part[keep], ms[keep]
        hi = np.minimum(ms + 1, k - 1)
        counts = hi + 1
        rep = np.repeat(np.arange(len(part)), counts)
        offs = np.concatenate(([0], np.cumsum(counts)))
        vals = np.arange(int(counts.sum())) - np.repeat(offs[:-1], counts)
        new = np.empty((len(rep), p + 1), np.uint8)
        new[:, :p] = part[rep]
        new[:, p] = vals
        ms = np.maximum(ms[rep], vals)
        part = new
    out = np.ascontiguousarray(part[ms == k - 1].reshape(-1, k, 2))
    if cache:
        os.makedirs(CACHE, exist_ok=True)
        np.save(path, out)
    return out


def icdfa_upto(k: int) -> np.ndarray:
    """All canonical transition functions with j <= k states, padded to k.

    Padding adds unreachable self-looping states, which changes nothing: a
    j-state DFA is realisable on k >= j states.
    """
    blocks = []
    for j in range(1, k + 1):
        t = icdfa_list(j)
        if j == k:
            blocks.append(t)
        else:
            pad = np.empty((t.shape[0], k, 2), np.uint8)
            pad[:, :j, :] = t
            for q in range(j, k):
                pad[:, q, :] = q
            blocks.append(pad)
    return np.concatenate(blocks, axis=0)


# --------------------------------------------------------------------------
# running transition functions
# --------------------------------------------------------------------------
def batch_states(T: np.ndarray, wb: np.ndarray) -> np.ndarray:
    """End states: T is (M,k,2), wb is (W,n) of letters.  Returns (M,W)."""
    m, w = T.shape[0], wb.shape[0]
    cur = np.zeros((m, w), np.uint8)
    ar = np.arange(m)[:, None]
    for p in range(wb.shape[1]):
        cur = T[ar, cur, wb[None, :, p]]
    return cur


def delta_row(T: np.ndarray, level: int) -> np.ndarray:
    """End state of a single transition function on every word of length
    `level`, indexed by the word read as a binary number (first letter high).

    One doubling step is one gather: pack (delta(q,0), delta(q,1)) into a
    uint16 with delta(q,0) in the low byte, gather, then view the result as
    bytes.  On a little-endian machine that lays the two children out in
    exactly the right order, so the whole row costs 2^level gathers with no
    strided writes."""
    if sys.byteorder != "little":  # pragma: no cover
        raise RuntimeError("little-endian assumed")
    t01 = T[:, 0].astype(np.uint16) | (T[:, 1].astype(np.uint16) << np.uint16(8))
    row = np.zeros(1, np.uint8)
    for _ in range(level):
        row = t01[row].view(np.uint8)
    return row


def separates(T: np.ndarray, u: np.ndarray, v: np.ndarray) -> bool:
    st = batch_states(T[None], np.stack([u, v]))
    return bool(st[0, 0] != st[0, 1])


# --------------------------------------------------------------------------
# minK for one pair (fast path)
# --------------------------------------------------------------------------
def min_states(u, v, kmax: int = 6, tables=None):
    """Least k with a k-state DFA separating u from v, or None if kmax is not
    enough.  `tables` overrides the canonical lists (used by negative
    controls)."""
    wb = np.stack([np.asarray(u, np.uint8), np.asarray(v, np.uint8)])
    for j in range(1, kmax + 1):
        T = icdfa_list(j) if tables is None else tables(j)
        if T.shape[0] == 0:
            continue
        st = batch_states(T, wb)
        if np.any(st[:, 0] != st[:, 1]):
            return j
    return None


def witness_delta(u, v, k: int):
    """A canonical <=k-state transition function separating u from v."""
    wb = np.stack([np.asarray(u, np.uint8), np.asarray(v, np.uint8)])
    for j in range(1, k + 1):
        T = icdfa_list(j)
        st = batch_states(T, wb)
        hit = np.flatnonzero(st[:, 0] != st[:, 1])
        if hit.size:
            return j, T[hit[0]], (int(st[hit[0], 0]), int(st[hit[0], 1]))
    return None, None, None


def verify_pair(u, v, claim: int):
    """Check a claim minK(u,v) == claim: some <=claim-state function separates
    and no <=claim-1-state one does.  Returns (ok, message)."""
    if claim < 1:
        return False, "claim < 1"
    j, T, ends = witness_delta(u, v, claim)
    if j is None:
        return False, f"no transition function on <= {claim} states separates them"
    if claim > 1:
        j2, _, _ = witness_delta(u, v, claim - 1)
        if j2 is not None:
            return False, f"{j2} states already suffice, so minK <= {j2} < {claim}"
    return True, f"{j}-state witness, runs end in states {ends[0]} != {ends[1]}"


# --------------------------------------------------------------------------
# minK for one pair (independent slow reference: literal definition)
# --------------------------------------------------------------------------
def all_deltas(k: int) -> np.ndarray:
    """Every transition function on exactly k states: shape (k^(2k), k, 2).
    No connectivity filter, no canonical form, no symmetry reduction."""
    m = 2 * k
    idx = np.arange(k**m, dtype=np.int64)
    out = np.empty((k**m, m), np.uint8)
    for p in range(m - 1, -1, -1):
        out[:, p] = idx % k
        idx //= k
    return out.reshape(-1, k, 2)


def brute_min_states(u, v, kmax: int = 4, chunk: int = 1 << 18):
    """Independent reference for minK(u,v), from the definition.

    Enumerates *every* transition function on k states, *every* start state
    and *every* accept set, and tests acceptance of u and of v directly.  It
    uses none of the reductions in this module -- not the accept-set
    reduction, not initial connectivity, not q0 = 0, not canonical labelling.
    """
    u = np.asarray(u, np.uint8)
    v = np.asarray(v, np.uint8)
    for k in range(1, kmax + 1):
        D = all_deltas(k)
        for lo in range(0, D.shape[0], chunk):
            T = D[lo : lo + chunk]
            b = T.shape[0]
            ar = np.arange(b)
            for q0 in range(k):
                pu = np.full(b, q0, np.uint8)
                pv = np.full(b, q0, np.uint8)
                for a in u:
                    pu = T[ar, pu, a]
                for a in v:
                    pv = T[ar, pv, a]
                for F in range(1 << k):
                    mask = np.array([(F >> q) & 1 for q in range(k)], bool)
                    if np.any(mask[pu] != mask[pv]):
                        return k
    return None


def literal_sepmat(n: int, k: int) -> np.ndarray:
    """sepmat[u,v] = some k-state DFA accepts exactly one of u, v.

    Literal definition over all (delta, q0, F).  Exhaustive over all pairs of
    length-n words.  Used only as a validation reference.
    """
    W = 1 << n
    out = np.zeros((W, W), bool)
    D = all_deltas(k)
    chunk = max(1, (1 << 24) // (W * W))
    for lo in range(0, D.shape[0], chunk):
        T = D[lo : lo + chunk]
        b = T.shape[0]
        ar = np.arange(b)[:, None]
        for q0 in range(k):
            cur = np.full((b, 1), q0, np.uint8)
            for _ in range(n):
                new = np.empty((b, cur.shape[1] * 2), np.uint8)
                new[:, 0::2] = T[ar, cur, 0]
                new[:, 1::2] = T[ar, cur, 1]
                cur = new
            for F in range(1 << k):
                mask = np.array([(F >> q) & 1 for q in range(k)], bool)
                acc = mask[cur]
                out |= (acc[:, :, None] ^ acc[:, None, :]).any(0)
    return out


def fast_sepmat(n: int, k: int) -> np.ndarray:
    """Same matrix via the reduction: canonical <=k-state functions, end
    states only."""
    W = 1 << n
    out = np.zeros((W, W), bool)
    for T in icdfa_upto(k):
        e = delta_row(T, n)
        out |= e[:, None] != e[None, :]
    return out


# --------------------------------------------------------------------------
# level DP: N(k) = max { n : sep(n) <= k }
# --------------------------------------------------------------------------
def _hash_rows(S, level: int) -> np.ndarray:
    """64-bit fold of the signature of every word of length `level`."""
    n = 1 << level
    h = np.zeros(n, np.uint64)
    for T in S:
        row = delta_row(T, level)
        for lo in range(0, n, CHUNK):
            hi = min(n, lo + CHUNK)
            h[lo:hi] ^= row[lo:hi]
            h[lo:hi] *= PRIME
        del row
    return h


def _dup_values(h, maxvals=4096, target=1 << 26):
    """Hash values occurring more than once.

    Duplicates are found by sorting, but a full sorted copy of h would double
    peak memory, which is the binding constraint at n = 30.  So h is split
    into 2^j buckets by its top bits (a bucket is closed under equality, so no
    duplicate can straddle two) and each bucket is sorted on its own.  Both
    the bucket extraction and the sort work on at most ~`target` elements at a
    time; the scan of h itself is chunked so no full-size temporary is ever
    allocated."""
    n = h.size
    nb = 1
    while nb < 16 and n // nb > target:
        nb *= 2
    shift = np.uint64(64 - (nb.bit_length() - 1))
    out, got = [], 0
    for b in range(nb):
        if nb == 1:
            vals = h.copy()
        else:
            parts = []
            for lo in range(0, n, CHUNK):
                seg = h[lo : lo + CHUNK]
                parts.append(seg[(seg >> shift) == np.uint64(b)])
            vals = np.concatenate(parts)
            del parts
        if vals.size >= 2:
            vals.sort()
            eq = vals[1:] == vals[:-1]
            if eq.any():
                d = np.unique(vals[:-1][eq])
                out.append(d)
                got += d.size
            del eq
        del vals
        if got >= maxvals:
            break
    if not out:
        return np.zeros(0, np.uint64)
    return np.concatenate(out)[:maxvals]


def _collision_groups(h, S, level, maxgroups=4096):
    """Word indices sharing a signature, verified exactly (the hash only
    proposes candidates; equal signatures always hash equal, so nothing is
    missed)."""
    n = h.size
    if n < 2:
        return []
    if not S:
        return [np.arange(n)]
    dup = _dup_values(h, maxgroups)
    if dup.size == 0:
        return []
    ds = np.sort(dup)
    idxs = []
    for lo in range(0, n, CHUNK):
        seg = h[lo : lo + CHUNK]
        pos = np.searchsorted(ds, seg)
        np.clip(pos, 0, ds.size - 1, out=pos)
        m = ds[pos] == seg
        if m.any():
            idxs.append(lo + np.flatnonzero(m))
    idx = np.concatenate(idxs) if idxs else np.zeros(0, np.int64)
    if idx.size == 0:
        return []
    wb = np.stack([bits_of(int(i), level) for i in idx])
    st = batch_states(np.stack(S), wb)  # (s, |idx|)
    _, inv, cnt = np.unique(st.T, axis=0, return_inverse=True, return_counts=True)
    inv = inv.ravel()
    return [idx[inv == c] for c in np.flatnonzero(cnt > 1)]


def _focus(groups, level, maxgroups=32, per=3):
    """A small word set spanning the largest collision groups, plus the group
    id of each word."""
    gs = sorted(groups, key=len, reverse=True)[:maxgroups]
    words, gid = [], []
    for i, g in enumerate(gs):
        for w in g[:per]:
            words.append(bits_of(int(w), level))
            gid.append(i)
    return np.stack(words), np.array(gid, np.int64), len(gs), gs


def exact_classes(Tall, wb):
    """Partition `wb` by the full end-state signature over every transition
    function in Tall.  Returns a label per word; equal labels means no DFA in
    Tall separates them."""
    m, W = Tall.shape[0], wb.shape[0]
    st = np.empty((m, W), np.uint8)
    chunk = max(1, (1 << 25) // max(W, 1))
    for lo in range(0, m, chunk):
        st[lo : lo + chunk] = batch_states(Tall[lo : lo + chunk], wb)
    _, inv = np.unique(st.T, axis=0, return_inverse=True)
    return inv.ravel()


def _rank(st, gid, ng, k):
    """(gain, rank) per transition function.

    gain = how many new classes it creates inside the collision groups; a
    function with gain 0 splits nothing.  rank breaks ties by how widely the
    function spreads the focus words overall, which keeps the certificate
    short."""
    m = st.shape[0]
    key = (gid[None, :].astype(np.int32) * k + st).astype(np.int32)
    cnt = np.zeros((m, ng * k), bool)
    np.put_along_axis(cnt, key, True, axis=1)
    gain = cnt.sum(1) - ng
    spread = np.zeros(m, np.int64)
    for q in range(k):
        spread += (st == q).any(axis=1)
    return gain, gain * 64 + spread


def pick_delta(Tall, wb, gid, ng, k, rng, sample=8192):
    """A transition function splitting one of the collision groups, or None if
    *no* function in Tall splits any of them (which certifies those words are
    pairwise unseparable by <= k states).  A random sample is tried first; the
    exhaustive sweep runs when the sample fails, and always before None."""
    m = Tall.shape[0]
    chunk = max(1, (1 << 24) // max(wb.shape[0], 1))
    if m > sample:
        idx = rng.choice(m, sample, replace=False)
        gain, rank = _rank(batch_states(Tall[idx], wb), gid, ng, k)
        if gain.max() > 0:
            return Tall[idx[int(rank.argmax())]]
    best, bestrank, bestgain = None, -1, 0
    for lo in range(0, m, chunk):
        blk = Tall[lo : lo + chunk]
        gain, rank = _rank(batch_states(blk, wb), gid, ng, k)
        j = int(rank.argmax())
        if int(gain[j]) > 0 and int(rank[j]) > bestrank:
            bestrank, bestgain, best = int(rank[j]), int(gain[j]), blk[j]
    return best if bestgain > 0 else None


def max_length(k: int, nmax: int, rng, verbose=True, seed_S=None):
    """N(k) = largest n with sep(n) <= k, plus a hardest pair of length N(k)+1.

    Returns (N_k, witness, S, capped) where `capped` is True if the search hit
    nmax without finding a genuine collision (so only N_k >= nmax is proved).
    `seed_S` starts from an existing certificate; functions on fewer than k
    states are padded, which is legitimate because a j-state DFA is realisable
    on k >= j states.
    """
    Tall = icdfa_upto(k)
    S = []
    if seed_S is not None:
        for T in seed_S:
            j = T.shape[0]
            pad = np.empty((k, 2), np.uint8)
            pad[:j] = T[:k] if j >= k else T
            for q in range(j, k):
                pad[q, :] = q
            S.append(pad)
    for level in range(1, nmax + 1):
        t0 = time.time()
        h = _hash_rows(S, level)
        added = 0
        while True:
            groups = _collision_groups(h, S, level)
            if not groups:
                break
            wb, gid, ng, gs = _focus(groups, level)
            og = gid.copy()
            new = []
            # split the focus set completely before touching h again: the
            # expensive step is finding the groups, not adding a function
            while True:
                T = pick_delta(Tall, wb, gid, ng, k, rng)
                if T is None:
                    keep = gid == gid[0]
                    u, v = wb[keep][0], wb[keep][1]
                    g = gs[int(og[keep][0])]
                    cls = exact_classes(Tall, wb[keep])
                    if verbose:
                        print(
                            f"    k={k}: first unseparable pair at n={level}: "
                            f"{word_str(u)} / {word_str(v)}  (candidate group "
                            f"{len(g)}, unseparable class >= {int((cls == cls[0]).sum())})",
                            flush=True,
                        )
                    return level - 1, (u, v), S, False
                new.append(T)
                st = batch_states(T[None], wb)[0]
                _, inv, cnt = np.unique(
                    gid * k + st, return_inverse=True, return_counts=True
                )
                inv = inv.ravel()
                keep = cnt[inv] > 1
                if not keep.any() or len(new) >= 12:
                    break
                wb, og = wb[keep], og[keep]
                _, gid = np.unique(inv[keep], return_inverse=True)
                gid = gid.ravel()
                ng = int(gid.max()) + 1
            n = h.size
            for T in new:
                S.append(T)
                added += 1
                row = delta_row(T, level)
                for lo in range(0, n, CHUNK):
                    hi = min(n, lo + CHUNK)
                    h[lo:hi] ^= row[lo:hi]
                    h[lo:hi] *= PRIME
                del row
        del h
        if verbose:
            print(
                f"    k={k}: n={level:2d} separated by {len(S)} functions "
                f"(+{added})  [{time.time() - t0:.1f}s]",
                flush=True,
            )
    return nmax, None, S, True


def families(nmax: int, kmax: int = 5):
    """Hardest pair inside two structured families, as a cheap probe of where
    sep next increases:  1^a 0^b vs 1^b 0^a, and a single 1 at position i vs
    position j.  These are the shapes the exhaustive census turns up at every
    length where sep jumps, so a length where neither family is hard is
    evidence (not proof) that sep has not increased there."""
    out = {}
    for n in range(2, nmax + 1):
        best, arg = 0, None
        for a in range(1, n):
            if a == n - a:
                continue
            u = np.array([1] * a + [0] * (n - a), np.uint8)
            v = np.array([1] * (n - a) + [0] * a, np.uint8)
            k = min_states(u, v, kmax) or kmax + 1
            if k > best:
                best, arg = k, (word_str(u), word_str(v))
        for i in range(n):
            for j in range(i + 1, n):
                u = np.zeros(n, np.uint8)
                u[i] = 1
                v = np.zeros(n, np.uint8)
                v[j] = 1
                k = min_states(u, v, kmax) or kmax + 1
                if k > best:
                    best, arg = k, (word_str(u), word_str(v))
        out[n] = (best, arg)
    return out


def census(k: int, level: int, rng, maxwords=1 << 12):
    """Every pair of length `level` that no DFA with <= k states separates.
    The certificate built for length level-1 isolates the candidates; each
    candidate group is then refined by *all* canonical <= k-state functions."""
    Tall = icdfa_upto(k)
    _, _, S, _ = max_length(k, level - 1, rng, verbose=False)
    h = _hash_rows(S, level)
    groups = _collision_groups(h, S, level)
    del h
    if not groups or sum(len(g) for g in groups) > maxwords:
        return None
    hard = []
    for g in groups:
        wb = np.stack([bits_of(int(i), level) for i in g])
        lab = exact_classes(Tall, wb)
        for c in np.unique(lab):
            cls = g[lab == c]
            hard += [
                (int(cls[a]), int(cls[b]))
                for a in range(len(cls))
                for b in range(a + 1, len(cls))
            ]
    return sorted(hard)


# --------------------------------------------------------------------------
# validation gates
# --------------------------------------------------------------------------
def _canon(delta, k):
    """BFS canonical form of the reachable part; returns (#states, tuple)."""
    order, seen, i = [0], {0: 0}, 0
    while i < len(order):
        q = order[i]
        i += 1
        for b in (0, 1):
            r = int(delta[q][b])
            if r not in seen:
                seen[r] = len(order)
                order.append(r)
    return len(order), tuple(
        (seen[int(delta[q][0])], seen[int(delta[q][1])]) for q in order
    )


def gate_icdfa(kmax=4, tables=None):
    """The canonical enumeration equals brute-force canonicalisation of all
    k^(2k) transition functions."""
    ok = True
    for k in range(1, kmax + 1):
        got = set()
        for d in all_deltas(k):
            j, c = _canon(d, k)
            if j == k:
                got.add(c)
        lst = icdfa_list(k) if tables is None else tables(k)
        mine = {tuple((int(r[0]), int(r[1])) for r in t) for t in lst}
        if mine != got or len(mine) != lst.shape[0]:
            print(f"  FAIL icdfa k={k}: {len(mine)} generated vs {len(got)} canonical")
            ok = False
        else:
            print(f"  ok   icdfa k={k}: {len(got)} canonical transition functions")
    return ok


def gate_reduction(cases):
    """Literal all-(delta,q0,F) separability equals the end-state reduction on
    canonical functions, for every pair of words."""
    ok = True
    for n, k in cases:
        t0 = time.time()
        a = literal_sepmat(n, k)
        b = fast_sepmat(n, k)
        same = np.array_equal(a, b)
        ok &= same
        print(
            f"  {'ok  ' if same else 'FAIL'} reduction n={n} k={k}: "
            f"{(1 << n) * ((1 << n) - 1) // 2} pairs, "
            f"{k ** (2 * k) * k * (1 << k):,} literal DFAs  [{time.time() - t0:.1f}s]"
        )
    return ok


def gate_bruteforce_sep(nmax, kmax):
    """sep(n) from the literal all-DFA definition, for tiny n."""
    vals = {}
    for n in range(1, nmax + 1):
        W = 1 << n
        m = np.zeros((W, W), bool)
        for k in range(1, kmax + 1):
            m = literal_sepmat(n, k)
            iu = np.triu_indices(W, 1)
            if m[iu].all():
                vals[n] = k
                break
        else:
            vals[n] = None
    return vals


def gate_pairs(rng, trials=40, kmax=4):
    """min_states (fast) equals brute_min_states (literal) on random pairs."""
    ok = True
    for _ in range(trials):
        n = int(rng.integers(1, 13))
        while True:
            u = rng.integers(0, 2, n).astype(np.uint8)
            v = rng.integers(0, 2, n).astype(np.uint8)
            if not np.array_equal(u, v):
                break
        a = min_states(u, v, kmax)
        b = brute_min_states(u, v, kmax)
        if a != b:
            print(f"  FAIL pair {word_str(u)}/{word_str(v)}: fast {a} vs literal {b}")
            ok = False
    if ok:
        print(f"  ok   {trials} random pairs: fast minK == literal minK (k <= {kmax})")
    return ok


def gate_witnesses(seps, witnesses, kcap=5):
    """The literal all-DFA reference confirms minK for the shortest witness at
    each value of sep -- in particular it re-derives the lower bounds
    sep(n) > k by exhausting every DFA on <= k states, accept sets included."""
    ok = True
    for val in sorted(set(seps.values())):
        if val > kcap:
            continue
        n = min(n for n in seps if seps[n] == val and n in witnesses)
        u, v = witnesses[n]
        t0 = time.time()
        got = brute_min_states(u, v, val)
        good = got == val
        ok &= good
        total = sum(k ** (2 * k) * k * (1 << k) for k in range(1, val + 1))
        print(
            f"  {'ok  ' if good else 'FAIL'} n={n:<2} {word_str(u)}/{word_str(v)}: "
            f"literal minK = {got} (claimed {val}); {total:,} DFAs enumerated "
            f"[{time.time() - t0:.1f}s]"
        )
    return ok


def gate_sanity(rng, seps, trials=200):
    """Structural facts that must hold."""
    ok = True
    ns = sorted(seps)
    if any(seps[a] > seps[b] for a, b in zip(ns, ns[1:])):
        print("  FAIL sep is not non-decreasing")
        ok = False
    else:
        print("  ok   sep(n) non-decreasing over the computed range")

    bad = 0
    for _ in range(trials):
        n = int(rng.integers(2, 15))
        u = rng.integers(0, 2, n).astype(np.uint8)
        v = u.copy()
        i = int(rng.integers(0, n))
        v[i] ^= 1
        first = int(np.flatnonzero(u != v)[0]) + 1
        k = min_states(u, v, 8)
        if k is None or k > first + 2:
            bad += 1
    if bad:
        print(f"  FAIL first-difference bound minK <= i+2 violated {bad}x")
        ok = False
    else:
        print(f"  ok   {trials} pairs: minK <= i+2 for first difference at position i")

    bad = 0
    for _ in range(trials // 4):
        n = int(rng.integers(2, 10))
        while True:
            u = rng.integers(0, 2, n).astype(np.uint8)
            v = rng.integers(0, 2, n).astype(np.uint8)
            if not np.array_equal(u, v):
                break
        s = rng.integers(0, 2, int(rng.integers(1, 5))).astype(np.uint8)
        a = min_states(u, v, 8)
        b = min_states(np.concatenate([u, s]), np.concatenate([v, s]), 8)
        if a is None or b is None or b < a:
            bad += 1
    if bad:
        print(f"  FAIL suffix monotonicity minK(uw,vw) >= minK(u,v) violated {bad}x")
        ok = False
    else:
        print(f"  ok   {trials // 4} pairs: minK(uw,vw) >= minK(u,v)")

    bad = sum(
        1
        for _ in range(trials // 4)
        for n in [int(rng.integers(1, 12))]
        for u in [rng.integers(0, 2, n).astype(np.uint8)]
        for v in [1 - u]
        if (min_states(u, v, 8) or 0) < 2
    )
    if bad:
        print("  FAIL minK < 2 for a distinct pair")
        ok = False
    else:
        print("  ok   minK >= 2 always (a 1-state DFA accepts everything or nothing)")
    return ok


def negative_controls(rng, seps, witnesses):
    """Deliberately corrupt each result and confirm the gate fires."""
    ok = True

    # (1) a corrupted canonical list must be caught by gate_icdfa
    real = icdfa_list(3).copy()
    bad = real.copy()
    bad[0, 0, 0] ^= 1
    print("  control 1: one transition flipped in the k=3 canonical list")
    caught = not gate_icdfa(3, tables=lambda j: bad if j == 3 else icdfa_list(j))
    print(f"    -> {'CAUGHT' if caught else 'MISSED (gate is vacuous!)'}")
    ok &= caught

    # (2) dropping the separating machines must inflate minK vs the reference
    n = min(x for x in seps if seps[x] >= 3)
    u, v = witnesses[n]
    k = seps[n]
    T = icdfa_list(k)
    st = batch_states(T, np.stack([u, v]))
    keep = T[st[:, 0] == st[:, 1]]
    print(
        f"  control 2: delete the {T.shape[0] - keep.shape[0]} k={k} functions that "
        f"separate {word_str(u)}/{word_str(v)}"
    )
    got = min_states(u, v, k, tables=lambda j: keep if j == k else icdfa_list(j))
    ref = brute_min_states(u, v, k)
    caught = got != ref
    print(f"    -> fast says {got}, literal reference says {ref}: "
          f"{'CAUGHT' if caught else 'MISSED (gate is vacuous!)'}")
    ok &= caught

    # (3) claiming a witness pair is easier than it is
    for n, (u, v) in sorted(witnesses.items()):
        k = seps[n]
        good, msg = verify_pair(u, v, k)
        badok, badmsg = verify_pair(u, v, k - 1)
        print(f"  control 3 (n={n}): claim minK({word_str(u)},{word_str(v)})={k - 1}")
        print(f"    -> true claim {k}: {'accepted' if good else 'REJECTED'} ({msg})")
        print(f"    -> false claim {k - 1}: "
              f"{'CAUGHT' if not badok else 'MISSED (gate is vacuous!)'} ({badmsg})")
        ok &= good and not badok
        break

    # (4) claiming sep(n) <= k when it is not: the exhaustive sweep must find
    #     a group that no k-state function splits
    n = min(x for x in seps if seps[x] >= 3)
    k = seps[n] - 1
    print(f"  control 4: claim sep({n}) <= {k}")
    Nk, wit, _, capped = max_length(k, n, rng, verbose=False)
    caught = (not capped) and Nk < n
    print(f"    -> exhaustive search over all <= {k}-state functions gives N({k})={Nk}"
          f" < {n}: {'CAUGHT' if caught else 'MISSED (gate is vacuous!)'}")
    ok &= caught
    return ok


# --------------------------------------------------------------------------
# driver
# --------------------------------------------------------------------------
def run(nmax, kmax, rng, verbose=True):
    counts = {k: icdfa_list(k).shape[0] for k in range(1, kmax + 1)}
    print("canonical initially-connected transition functions over {0,1}:")
    for k, c in counts.items():
        print(f"  k={k}: {c:>10,}   (of k^(2k) = {k ** (2 * k):,})")
    print()

    N, hard, timings, certs = {}, {}, {}, {}
    prev = None
    for k in range(1, kmax + 1):
        t0 = time.time()
        Nk, wit, S, capped = max_length(k, nmax, rng, verbose=verbose, seed_S=prev)
        prev = S
        timings[k] = time.time() - t0
        N[k] = Nk
        hard[k] = wit
        certs[k] = S
        tag = f">= {Nk} (search capped at n={nmax})" if capped else f"= {Nk}"
        w = "" if wit is None else f"  hardest pair at n={Nk + 1}: {word_str(wit[0])} / {word_str(wit[1])}"
        print(f"N({k}) {tag}   [{timings[k]:.1f}s, {len(S)} functions in the certificate]{w}")
    print()

    seps, witnesses = {}, {}
    top = max(N.values())
    for n in range(1, top + 1):
        for k in range(1, kmax + 1):
            if N[k] >= n:
                seps[n] = k
                break
    for n in seps:
        k = seps[n]
        if hard.get(k - 1) is not None:
            u, v = hard[k - 1]
            pad = n - len(u)
            witnesses[n] = (
                np.concatenate([u, np.zeros(pad, np.uint8)]),
                np.concatenate([v, np.zeros(pad, np.uint8)]),
            )
    return N, seps, witnesses, timings, certs


def check_cert(path: str, n: int) -> bool:
    """Re-verify an upper bound sep(n) <= k from a saved certificate, without
    redoing the search: load the transition functions, check each one really is
    a function on <= k states, and check the signature map is injective on all
    2^n words."""
    S = np.load(path)
    k = S.shape[1]
    if S.ndim != 3 or S.shape[2] != 2 or not (S < k).all():
        print("certificate malformed")
        return False
    t0 = time.time()
    h = _hash_rows(list(S), n)
    dup = _dup_values(h, 1)
    ok = dup.size == 0
    print(
        f"certificate {os.path.basename(path)}: {S.shape[0]} transition functions "
        f"on {k} states; signatures of all {1 << n:,} words of length {n} are "
        f"{'distinct -> sep(%d) <= %d VERIFIED' % (n, k) if ok else 'NOT distinct -> claim REFUTED'}"
        f"  [{time.time() - t0:.1f}s]"
    )
    return ok


def print_table(seps, witnesses, verify=True):
    print("n   sep(n)  witness pair (minK = sep(n))")
    for n in sorted(seps):
        w = witnesses.get(n)
        if w is None:
            print(f"{n:<3} {seps[n]:<6}  -")
            continue
        u, v = w
        mark = ""
        if verify:
            ok, _ = verify_pair(u, v, seps[n])
            mark = "" if ok else "   <-- VERIFY FAILED"
        print(f"{n:<3} {seps[n]:<6}  {word_str(u)} / {word_str(v)}{mark}")


def main(argv=None):
    ap = argparse.ArgumentParser(description=__doc__.split("\n")[0])
    ap.add_argument("--nmax", type=int, default=20, help="largest word length to try")
    ap.add_argument("--kmax", type=int, default=5, help="largest state count to try")
    ap.add_argument("--seed", type=int, default=20260820)
    ap.add_argument("--pair", nargs=2, metavar=("U", "V"))
    ap.add_argument("--brute", action="store_true", help="also run the literal reference on --pair")
    ap.add_argument("--verify", action="store_true", help="run the validation gates")
    ap.add_argument("--deep", action="store_true", help="slower, wider validation cases")
    ap.add_argument("--negative-control", action="store_true")
    ap.add_argument("--census", type=int, default=0, help="list all unseparable pairs at this length for k=--kmax")
    ap.add_argument("--families", type=int, default=0, help="probe structured hard-pair families up to this length")
    ap.add_argument("--save-cert", metavar="PATH", help="save the sep(n) <= kmax certificate")
    ap.add_argument("--check-cert", metavar="PATH", help="re-verify a saved certificate at --nmax")
    args = ap.parse_args(argv)
    rng = np.random.default_rng(args.seed)

    if args.check_cert:
        return 0 if check_cert(args.check_cert, args.nmax) else 1

    if args.pair:
        u, v = parse_word(args.pair[0]), parse_word(args.pair[1])
        if len(u) != len(v):
            print("warning: words have different lengths", file=sys.stderr)
        k = min_states(u, v, 6)
        print(f"minK({args.pair[0]}, {args.pair[1]}) = {k}")
        j, T, ends = witness_delta(u, v, k)
        print(f"  witness: {j} states, delta = "
              + ", ".join(f"{q}:({int(T[q][0])},{int(T[q][1])})" for q in range(j))
              + f"; runs end in {ends[0]} != {ends[1]}, accept F = {{{ends[0]}}}")
        ok, msg = verify_pair(u, v, k)
        print(f"  verified: {ok} ({msg})")
        if args.brute:
            t0 = time.time()
            b = brute_min_states(u, v, min(k, 4))
            print(f"  literal reference (all delta, all q0, all accept sets): "
                  f"{b}  [{time.time() - t0:.1f}s]")
        return 0

    if args.families:
        t0 = time.time()
        for n, (k, arg) in families(args.families, args.kmax).items():
            tag = f">{args.kmax}" if k > args.kmax else str(k)
            print(f"n={n:<3} hardest in the two families: minK = {tag:<3} {arg[0]} / {arg[1]}",
                  flush=True)
        print(f"[{time.time() - t0:.1f}s]")
        return 0

    if args.census:
        pairs = census(args.kmax, args.census, rng)
        if pairs is None:
            print("collision set too large for a full census")
        else:
            print(f"{len(pairs)} pairs of length {args.census} that no "
                  f"<= {args.kmax}-state DFA separates:")
            for a, b in pairs:
                print(f"  {word_str(bits_of(a, args.census))} / "
                      f"{word_str(bits_of(b, args.census))}")
        return 0

    t0 = time.time()
    N, seps, witnesses, timings, certs = run(args.nmax, args.kmax, rng)
    if args.save_cert:
        S = certs[args.kmax]
        np.save(args.save_cert, np.stack(S) if S else np.zeros((0, args.kmax, 2), np.uint8))
        print(f"certificate for sep(n) <= {args.kmax} up to n={N[args.kmax]} "
              f"saved to {args.save_cert} ({len(S)} transition functions)")
    print_table(seps, witnesses)
    print(f"\nsequence: {', '.join(str(seps[n]) for n in sorted(seps))}")
    print(f"total {time.time() - t0:.1f}s")

    if args.verify:
        print("\n--- validation gates ---")
        ok = True
        print("(A) canonical enumeration vs brute-force canonicalisation")
        ok &= gate_icdfa(4)
        print("(B) accept-set reduction, exhaustive over all pairs and all DFAs")
        cases = [(n, 3) for n in range(1, 8)] + [(n, 4) for n in range(1, 6)]
        if args.deep:
            cases += [(8, 3), (6, 4), (7, 4), (8, 4)]
        ok &= gate_reduction(cases)
        print("(C) fast minK vs literal minK on random pairs")
        ok &= gate_pairs(rng, 40, 4)
        print("(D) sep(n) from the literal definition, tiny n")
        bf = gate_bruteforce_sep(6 if not args.deep else 7, 4)
        agree = all(bf[n] == seps[n] for n in bf if n in seps)
        print(f"  {'ok  ' if agree else 'FAIL'} literal sep(n) for n <= {max(bf)}: "
              f"{[bf[n] for n in sorted(bf)]} vs computed "
              f"{[seps[n] for n in sorted(bf)]}")
        ok &= agree
        print("(E) literal reference on the hardest pairs")
        ok &= gate_witnesses(seps, witnesses)
        print("(F) structural sanity")
        ok &= gate_sanity(rng, seps)
        print(f"\nall gates: {'PASS' if ok else 'FAIL'}")

    if args.negative_control:
        print("\n--- negative controls (each gate must catch a corrupted result) ---")
        ok = negative_controls(rng, seps, witnesses)
        print(f"\nnegative controls: {'PASS (every corruption caught)' if ok else 'FAIL'}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
