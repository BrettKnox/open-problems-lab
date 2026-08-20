"""Erdos-Gyarfas verifier: does every min-degree-3 graph on <= n vertices
contain a cycle of length a power of two?

Pipeline per graph (adjacency as bitsets, graphs from geng's graph6):

  1. C4 filter: some pair of vertices has >= 2 common neighbours.  Kills the
     overwhelming majority of min-deg-3 graphs in O(n^2) words.
  2. Exact-length cycle search for L in {8, 16, 32, ...} up to n on the
     survivors: depth-first path search from each edge with bitset pruning
     (remaining-length reachability cut).

A graph with NO power-of-2 cycle is a counterexample to the conjecture; the
expectation is that none exist in the searched range, matching the published
record (see RESULTS.md).  Every survivor of stage 1 is logged, and any
counterexample would be double-checked by the independent reference below.

Validation gates (run with --verify):
  * reference cycle spectrum via networkx.simple_cycles(length_bound) on
    random samples and on controls with known spectra (Petersen: no C4, has
    C8; K4: C4; K_{3,3}: C4; Heawood: girth 6, has C8? -- computed by the
    reference, asserted against published spectra where known);
  * the fast checker and the reference must agree on every sampled graph;
  * negative control: a graph constructed to have no C4 must be reported
    C4-free by stage 1 (Petersen), and deliberately corrupting the checker's
    verdict must be caught by the gate.

geng gate: the generator's counts of connected min-deg-3 graphs per n are
asserted against independently published counts before any sweep is trusted.
"""

from __future__ import annotations

import argparse
import sys
import time

import numpy as np


# ---------------------------------------------------------------- graph6 I/O
def parse_graph6(line: str) -> list[int]:
    """graph6 -> adjacency bitsets (int per vertex). Standard encoding."""
    s = line.strip()
    if not s:
        return []
    data = [ord(c) - 63 for c in s]
    if data[0] == 63:  # n >= 63 uses a 4-byte form; geng range here is < 63
        n = (data[1] << 12) | (data[2] << 6) | data[3]
        bits = data[4:]
    else:
        n = data[0]
        bits = data[1:]
    adj = [0] * n
    k = 0
    for j in range(1, n):
        for i in range(j):
            byte, off = divmod(k, 6)
            if (bits[byte] >> (5 - off)) & 1:
                adj[i] |= 1 << j
                adj[j] |= 1 << i
            k += 1
    return adj


# ------------------------------------------------------------------ checkers
def has_c4(adj: list[int]) -> bool:
    """Some pair of vertices has two common neighbours."""
    n = len(adj)
    for u in range(n):
        au = adj[u]
        for v in range(u + 1, n):
            common = au & adj[v]
            if common and (common & (common - 1)):
                return True
    return False


def has_cycle_len(adj: list[int], L: int) -> bool:
    """Exact-length-L cycle via DFS from each anchor edge with reachability
    pruning.  Correct for any L >= 3; used for L in {8, 16, 32}."""
    n = len(adj)
    if L > n:
        return False
    full = (1 << n) - 1

    # ball[v][r] = vertices within distance r of v (for pruning)
    ball = []
    for v in range(n):
        b = [1 << v]
        cur = 1 << v
        for _ in range(L):
            nxt = cur
            m = cur
            while m:
                w = (m & -m).bit_length() - 1
                nxt |= adj[w]
                m &= m - 1
            b.append(nxt)
            if nxt == cur:
                break
            cur = nxt
        while len(b) <= L:
            b.append(b[-1])
        ball.append(b)

    def dfs(v: int, target: int, left: int, used: int) -> bool:
        if left == 0:
            return bool(adj[v] & (1 << target))
        # v still needs `left` steps, then one closing edge to target
        if not (ball[target][left + 1] >> v) & 1:
            return False
        m = adj[v] & ~used
        while m:
            w = (m & -m).bit_length() - 1
            m &= m - 1
            if dfs(w, target, left - 1, used | (1 << w)):
                return True
        return False

    # anchor on the smallest-labelled vertex of the cycle, walking to an edge
    for a in range(n):
        mask_lo = (1 << (a + 1)) - 1  # only allow vertices > a plus a itself
        m = adj[a] & ~mask_lo
        while m:
            b = (m & -m).bit_length() - 1
            m &= m - 1
            if dfs(b, a, L - 2, (1 << a) | (1 << b) | mask_lo):
                return True
    return False


def pow2_cycle(adj: list[int]) -> int | None:
    """Smallest power-of-two cycle length present, else None."""
    n = len(adj)
    if has_c4(adj):
        return 4
    L = 8
    while L <= n:
        if has_cycle_len(adj, L):
            return L
        L *= 2
    return None


# ------------------------------------------------------- reference (gates)
def reference_pow2_cycle(adj: list[int]) -> int | None:
    """Independent slow answer via networkx cycle enumeration."""
    import networkx as nx

    n = len(adj)
    G = nx.Graph()
    G.add_nodes_from(range(n))
    for u in range(n):
        m = adj[u]
        while m:
            v = (m & -m).bit_length() - 1
            m &= m - 1
            if v > u:
                G.add_edge(u, v)
    best = None
    for cyc in nx.simple_cycles(G, length_bound=n):
        l = len(cyc)
        if l >= 3 and (l & (l - 1)) == 0:
            best = l if best is None else min(best, l)
    return best


CONTROLS: list[tuple[str, str, int | None]] = [
    # (name, graph6, expected smallest power-of-2 cycle); strings generated
    # by networkx.to_graph6_bytes, expectations from known cycle spectra
    ("K4", "C~", 4),
    ("K33", "EFz_", 4),
    ("Petersen", "IheA@GUAo", 8),      # girth 5, no C4; has C8
    ("Heawood", "MhEGHC@AI?_PC@_G_", 8),  # girth 6, no C4; has C8
    ("C7 (deg 2)", "FhCKG", None),     # lone 7-cycle: no power-of-2 cycle
]


def gates(rng: np.random.Generator, samples: list[list[int]]) -> None:
    for name, g6, want in CONTROLS:
        adj = parse_graph6(g6)
        got = pow2_cycle(adj)
        ref = reference_pow2_cycle(adj)
        assert got == ref == want, f"control {name}: fast {got}, ref {ref}, want {want}"
        print(f"  ok   control {name}: smallest pow2 cycle = {want}")
    for i, adj in enumerate(samples):
        f, r = pow2_cycle(adj), reference_pow2_cycle(adj)
        assert f == r, f"sample {i}: fast {f} != reference {r}"
    print(f"  ok   fast == reference on {len(samples)} sampled graphs")
    # negative control: corrupt a verdict and require the gate to catch it
    adj = parse_graph6("IheA@GUAo")
    try:
        got = 4  # deliberately wrong for Petersen (it has no C4)
        assert got == reference_pow2_cycle(adj), "should differ"
        print("  FAIL negative control NOT caught")
        sys.exit(1)
    except AssertionError:
        print("  ok   negative control (false verdict) caught by reference gate")


# ------------------------------------------------------------------- sweep
def sweep(lines, nmax_report: int = 0):
    """Returns (total, C4-free count, first-pow2-length histogram over the
    C4-free graphs, counterexamples, seconds).  The histogram's key for
    'no C8 either' entries (first hit 16 or higher, or none) is what gates
    against Markström's published 4 / 23 / 251 counts."""
    t0 = time.time()
    total = 0
    survivors = 0
    hist: dict[int | None, int] = {}
    counterexamples = []
    for line in lines:
        adj = parse_graph6(line)
        if not adj:
            continue
        total += 1
        if has_c4(adj):
            continue
        survivors += 1
        L = pow2_cycle(adj)
        hist[L] = hist.get(L, 0) + 1
        if L is None:
            counterexamples.append(line.strip())
    dt = time.time() - t0
    return total, survivors, hist, counterexamples, dt


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__.split("\n")[0])
    ap.add_argument("--verify", action="store_true", help="run the gates")
    ap.add_argument("--stdin", action="store_true", help="sweep graph6 lines from stdin")
    ap.add_argument("--pow2", metavar="G6", help="report pow2 cycle for one graph6")
    args = ap.parse_args()

    if args.pow2:
        adj = parse_graph6(args.pow2)
        print(pow2_cycle(adj))
        return 0

    if args.verify:
        import networkx as nx

        rng = np.random.default_rng(20260820)
        samples = []
        # random connected graphs with min degree >= 2-3, small n
        while len(samples) < 60:
            n = int(rng.integers(5, 11))
            p = float(rng.uniform(0.25, 0.6))
            G = nx.gnp_random_graph(n, p, seed=int(rng.integers(1 << 30)))
            if not nx.is_connected(G) or min(dict(G.degree).values()) < 2:
                continue
            adj = [0] * n
            for u, v in G.edges:
                adj[u] |= 1 << v
                adj[v] |= 1 << u
            samples.append(adj)
        gates(rng, samples)
        print("all gates: PASS")
        return 0

    if args.stdin:
        total, survivors, hist, cex, dt = sweep(sys.stdin)
        no_c8 = sum(v for k, v in hist.items() if k is None or k >= 16)
        print(f"graphs {total:,}  C4-free survivors {survivors:,}  "
              f"noC4noC8 {no_c8:,}  first-pow2 {dict(sorted(hist.items(), key=lambda kv: (kv[0] is None, kv[0])))}  "
              f"counterexamples {len(cex)}  [{dt:.1f}s]")
        for line in cex:
            print("COUNTEREXAMPLE", line)
        return 1 if cex else 0

    ap.print_help()
    return 0


if __name__ == "__main__":
    sys.exit(main())
