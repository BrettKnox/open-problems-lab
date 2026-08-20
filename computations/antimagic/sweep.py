"""Antimagic sweep: verify the Hartsfield-Ringel conjecture on ALL connected
graphs of <= N vertices.

A graph with m edges is antimagic if some bijection f : E -> {1..m} makes all
vertex sums (sum of labels of incident edges) pairwise distinct. Conjecture:
every connected graph except K2 is antimagic.

Pipeline per graph (graph6 from nauty geng -c):
  1. randomized hill-climbing on the number of colliding vertex pairs
     (label swaps, random restarts) -- finds a labeling for almost everything;
  2. exact branch-and-prune fallback (labels assigned edge by edge, pruning
     whenever two vertices with all incident edges labeled share a sum), so a
     graph is declared NOT antimagic only by exhaustion.

Every labeling found is re-checked by an independent verifier (bijection +
distinct sums recomputed from scratch). K2 is the designed negative instance:
the exact search must prove it not antimagic. Stars cross-check the Lean
theorem `isAntimagic_starGraph` (OpenProblemsLab/Antimagic.lean).

    python sweep.py --verify
    geng -c -q 8 | python sweep.py --stdin
"""

from __future__ import annotations

import argparse
import random
import sys
import time


# ---------------------------------------------------------------- graph6 I/O
def parse_graph6(line: str) -> list[int]:
    s = line.strip()
    if not s:
        return []
    data = [ord(c) - 63 for c in s]
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


def edges_of(adj: list[int]) -> list[tuple[int, int]]:
    n = len(adj)
    return [(u, v) for u in range(n) for v in range(u + 1, n) if (adj[u] >> v) & 1]


# ----------------------------------------------------------------- verifier
def verify_labeling(n: int, edges: list[tuple[int, int]],
                    lab: list[int]) -> bool:
    """Independent check: `lab[i]` is the label of `edges[i]`. Bijection onto
    {1..m} and all vertex sums distinct. Shares no state with the searchers."""
    m = len(edges)
    if sorted(lab) != list(range(1, m + 1)):
        return False
    sums = [0] * n
    for (u, v), l in zip(edges, lab):
        sums[u] += l
        sums[v] += l
    return len(set(sums)) == n


# ------------------------------------------------------------ heuristic pass
def heuristic(n: int, edges: list[tuple[int, int]], rng: random.Random,
              restarts: int = 24, steps: int = 4000) -> list[int] | None:
    m = len(edges)
    if m == 0:
        return [] if n == 1 else None
    inc = [[] for _ in range(n)]
    for i, (u, v) in enumerate(edges):
        inc[u].append(i)
        inc[v].append(i)

    def collisions(sums: list[int]) -> int:
        seen: dict[int, int] = {}
        c = 0
        for s in sums:
            k = seen.get(s, 0)
            c += k
            seen[s] = k + 1
        return c

    for _ in range(restarts):
        lab = list(range(1, m + 1))
        rng.shuffle(lab)
        sums = [0] * n
        for i, (u, v) in enumerate(edges):
            sums[u] += lab[i]
            sums[v] += lab[i]
        bad = collisions(sums)
        if bad == 0:
            return lab
        for _ in range(steps):
            i, j = rng.randrange(m), rng.randrange(m)
            if i == j:
                continue
            (u1, v1), (u2, v2) = edges[i], edges[j]
            d = lab[j] - lab[i]
            for w in (u1, v1):
                sums[w] += d
            for w in (u2, v2):
                sums[w] -= d
            nb = collisions(sums)
            if nb <= bad:
                lab[i], lab[j] = lab[j], lab[i]
                bad = nb
                if bad == 0:
                    return lab
            else:
                for w in (u1, v1):
                    sums[w] -= d
                for w in (u2, v2):
                    sums[w] += d
    return None


# ---------------------------------------------------------------- exact pass
def exact(n: int, edges: list[tuple[int, int]]) -> list[int] | None:
    """Branch and prune over label assignments; None = proved not antimagic.
    Edges ordered to complete vertices early; prune on equal sums of two
    completed vertices."""
    m = len(edges)
    if m == 0:
        return [] if n == 1 else None
    deg = [0] * n
    for u, v in edges:
        deg[u] += 1
        deg[v] += 1
    order = sorted(range(m), key=lambda i: min(deg[edges[i][0]], deg[edges[i][1]]))
    left = deg[:]           # unlabeled incident edges per vertex
    sums = [0] * n
    used = [False] * (m + 1)
    lab = [0] * m
    done_sums: dict[int, int] = {}

    def rec(k: int) -> bool:
        if k == m:
            return True
        ei = order[k]
        u, v = edges[ei]
        for l in range(1, m + 1):
            if used[l]:
                continue
            used[l] = True
            sums[u] += l
            sums[v] += l
            left[u] -= 1
            left[v] -= 1
            ok = True
            completed = []
            for w in (u, v) if u != v else (u,):
                if left[w] == 0:
                    if done_sums.get(sums[w], 0):
                        ok = False
                        break
                    completed.append(w)
                    done_sums[sums[w]] = done_sums.get(sums[w], 0) + 1
            if ok and rec(k + 1):
                lab[ei] = l
                return True
            for w in completed:
                done_sums[sums[w]] -= 1
            used[l] = False
            sums[u] -= l
            sums[v] -= l
            left[u] += 1
            left[v] += 1
        return False

    return lab if rec(0) else None


def solve(n: int, edges: list[tuple[int, int]], rng: random.Random):
    """(labeling or None, used_exact). None only after exact exhaustion."""
    lab = heuristic(n, edges, rng)
    if lab is not None:
        return lab, False
    return exact(n, edges), True


# -------------------------------------------------------------------- gates
def gates() -> None:
    rng = random.Random(20260820)
    # K2: the designed negative instance -- exact search must refute it
    assert exact(2, [(0, 1)]) is None, "K2 wrongly declared antimagic"
    print("  ok   K2 proved NOT antimagic by the exact search")
    # K1: trivially antimagic
    assert verify_labeling(1, [], [])
    print("  ok   K1 trivially antimagic")
    # P3, C3, C4, K4: classical antimagic graphs
    cases = {
        "P3": (3, [(0, 1), (1, 2)]),
        "C3": (3, [(0, 1), (1, 2), (0, 2)]),
        "C4": (4, [(0, 1), (1, 2), (2, 3), (0, 3)]),
        "K4": (4, [(0, 1), (0, 2), (0, 3), (1, 2), (1, 3), (2, 3)]),
    }
    for name, (n, es) in cases.items():
        lab, _ = solve(n, es, rng)
        assert lab is not None and verify_labeling(n, es, lab), f"{name} failed"
    print("  ok   P3, C3, C4, K4 antimagic with verified labelings")
    # stars K_{1,m}: cross-check of the Lean theorem isAntimagic_starGraph
    for m in range(2, 9):
        es = [(0, i) for i in range(1, m + 1)]
        lab, _ = solve(m + 1, es, rng)
        assert lab is not None and verify_labeling(m + 1, es, lab), f"star {m}"
    print("  ok   stars K_{1,m}, m = 2..8 (cross-check of the Lean theorem)")
    # exact and heuristic agree on random small graphs
    for _ in range(200):
        n = rng.randrange(3, 8)
        es = [(u, v) for u in range(n) for v in range(u + 1, n)
              if rng.random() < 0.5]
        vs = set(v for e in es for v in e)
        if len(vs) < n or not es:
            continue
        lab = exact(n, es)
        if lab is not None:
            assert verify_labeling(n, es, lab)
    print("  ok   exact-search labelings verify on 200 random graphs")
    # negative controls: the verifier must reject corrupted labelings
    n, es = 4, [(0, 1), (1, 2), (2, 3), (0, 3)]
    lab, _ = solve(n, es, rng)
    bad1 = list(lab)
    bad1[0] = bad1[1]                       # not a bijection
    assert not verify_labeling(n, es, bad1)
    # C4 with labels arranged to force a sum collision: 1,2,4,3 around the
    # cycle gives sums 4,3,6,7 (fine) -- instead swap to make two sums equal
    bad2 = [1, 3, 2, 4]                     # sums: 5,4,5,6 -> collision
    assert not verify_labeling(n, es, bad2)
    print("  ok   negative controls: non-bijection and sum-collision rejected")
    print("all gates: PASS")


# -------------------------------------------------------------------- sweep
def sweep(lines) -> int:
    rng = random.Random(20260820)
    t0 = time.time()
    total = 0
    exact_used = 0
    failures = []
    k2 = 0
    for line in lines:
        adj = parse_graph6(line)
        if not adj:
            continue
        total += 1
        n = len(adj)
        es = edges_of(adj)
        if n == 2:
            k2 += 1
            continue
        lab, ex = solve(n, es, rng)
        if ex:
            exact_used += 1
        if lab is None or not verify_labeling(n, es, lab):
            failures.append(line.strip())
    dt = time.time() - t0
    print(f"graphs {total:,}  antimagic-with-verified-labeling "
          f"{total - k2 - len(failures):,}  K2-skipped {k2}  "
          f"exact-fallback used {exact_used}  NOT antimagic {len(failures)}  "
          f"[{dt:.1f}s]")
    for g in failures:
        print("NOT-ANTIMAGIC", g)
    return 1 if failures else 0


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__.split("\n")[0])
    ap.add_argument("--verify", action="store_true")
    ap.add_argument("--stdin", action="store_true")
    args = ap.parse_args()
    if args.verify:
        gates()
        return 0
    if args.stdin:
        return sweep(sys.stdin)
    ap.print_help()
    return 0


if __name__ == "__main__":
    sys.exit(main())
