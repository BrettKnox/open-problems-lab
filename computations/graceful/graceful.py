"""Graceful tree verification: every tree on n vertices has a graceful
labeling (injective f : V -> {0..m}, m = n-1 edges, with edge labels
|f(u)-f(v)| exactly {1..m}).

Trees stream from nauty-gentreeg -p (parent arrays). Per tree: exact
backtracking over vertex labels in BFS order (each new vertex attaches to one
labeled parent; prune on used vertex labels and used edge labels), so a tree
is declared ungraceful only by exhaustion. Every labeling found is re-checked
by an independent verifier. The published record: all trees <= 35 vertices
are graceful (Fang 2010, arXiv:1003.3045).

    python graceful.py --verify
    nauty-gentreeg -p -q 18 | python graceful.py --stdin
"""

from __future__ import annotations

import argparse
import sys
import time


def parse_parents(line: str) -> list[tuple[int, int]] | None:
    """gentreeg -p line: n integers, parent of vertex i (1-based, root 0)."""
    parts = line.split()
    if not parts:
        return None
    par = [int(x) for x in parts]
    return [(i, par[i] - 1) for i in range(1, len(par)) if par[i] >= 1]


def verify_labeling(n: int, edges: list[tuple[int, int]], f: list[int]) -> bool:
    """Independent: f injective into {0..m}, edge labels exactly {1..m}."""
    m = len(edges)
    if len(f) != n or len(set(f)) != n or any(not 0 <= x <= m for x in f):
        return False
    labels = {abs(f[u] - f[v]) for u, v in edges}
    return labels == set(range(1, m + 1))


def bfs_order(n: int, edges: list[tuple[int, int]]):
    """(order, parent_of) with each vertex after its parent."""
    adj = [[] for _ in range(n)]
    for u, v in edges:
        adj[u].append(v)
        adj[v].append(u)
    order = [0]
    parent = [-1] * n
    seen = [False] * n
    seen[0] = True
    qi = 0
    while qi < len(order):
        u = order[qi]
        qi += 1
        for w in adj[u]:
            if not seen[w]:
                seen[w] = True
                parent[w] = u
                order.append(w)
    return order, parent


import random as _random


def _search(n, m, order, parent, label_order, budget) -> list[int] | None:
    """Backtracking with a node budget; None = budget exhausted or no
    labeling in the explored space. budget None = unlimited (exact)."""
    f = [-1] * n
    used_v = [False] * (m + 1)
    used_e = [False] * (m + 1)
    nodes = [0]
    limit = budget if budget is not None else float("inf")

    def rec(k: int) -> bool | None:
        if k == n:
            return True
        if nodes[0] > limit:
            return None
        v = order[k]
        p = f[parent[v]]
        hit_budget = False
        for lab in label_order[k]:
            if used_v[lab]:
                continue
            el = lab - p if lab > p else p - lab
            if el == 0 or used_e[el]:
                continue
            nodes[0] += 1
            used_v[lab] = True
            used_e[el] = True
            f[v] = lab
            r = rec(k + 1)
            if r:
                return True
            if r is None:
                hit_budget = True
            used_v[lab] = False
            used_e[el] = False
        f[v] = -1
        return None if hit_budget else False

    for r0 in label_order[0]:
        used_v[r0] = True
        f[order[0]] = r0
        res = rec(1)
        if res:
            return f
        used_v[r0] = False
        if res is None and budget is not None:
            return None  # budget hit: inconclusive
    return None


def graceful(n: int, edges: list[tuple[int, int]],
             rng: _random.Random | None = None) -> list[int] | None:
    """Randomized budgeted passes, then exhaustive fallback. A labeling is
    proof by itself; 'ungraceful' would only ever be declared by the final
    unbudgeted exhaustive pass (which, per the conjecture and Fang's record,
    should never happen for n <= 35)."""
    m = len(edges)
    if n == 1:
        return [0]
    rng = rng or _random.Random(20260820)
    # Trees have n = m + 1 vertices, so a labeling is a bijection V <-> {0..m}
    # and gracefulness says the m edge labels are pairwise distinct.
    # Hill-climb on the number of duplicated edge labels via label swaps
    # (Aldred-McKay style), with restarts; exact search only as a fallback.
    adj = [[] for _ in range(n)]
    for u, v in edges:
        adj[u].append(v)
        adj[v].append(u)
    for _restart in range(400):
        f = rng.sample(range(m + 1), n)
        cnt = [0] * (m + 1)
        dup = 0
        for u, v in edges:
            el = abs(f[u] - f[v])
            cnt[el] += 1
            if cnt[el] > 1:
                dup += 1
        steps = 0
        while dup and steps < 600:
            steps += 1
            # aim the move at a duplicated edge label: pick an edge whose
            # label collides and swap one endpoint with a random vertex
            a = -1
            for _try in range(8):
                u, v = edges[rng.randrange(m)]
                if cnt[abs(f[u] - f[v])] > 1:
                    a = u if rng.random() < 0.5 else v
                    break
            if a < 0:
                a = rng.randrange(n)
            b = rng.randrange(n)
            if a == b:
                continue
            delta = 0
            touched = []
            for x, y in ((a, b), (b, a)):
                for w in adj[x]:
                    if w == y:
                        continue
                    el = abs(f[x] - f[w])
                    touched.append(el)
                    cnt[el] -= 1
                    if cnt[el] >= 1:
                        delta -= 1
            f[a], f[b] = f[b], f[a]
            newtouched = []
            for x, y in ((a, b), (b, a)):
                for w in adj[x]:
                    if w == y:
                        continue
                    el = abs(f[x] - f[w])
                    newtouched.append(el)
                    if cnt[el] >= 1:
                        delta += 1
                    cnt[el] += 1
            if delta <= 0:
                dup += delta
            else:
                # revert
                for el in newtouched:
                    cnt[el] -= 1
                f[a], f[b] = f[b], f[a]
                for el in touched:
                    cnt[el] += 1
        if dup == 0:
            return f
    # exhaustive (no budget) — the exactness guarantee
    order, parent = bfs_order(n, edges)
    extremes = sorted(range(m + 1), key=lambda r: min(r, m - r))
    lo = [extremes] * n
    return _search(n, m, order, parent, lo, budget=None)


def gates() -> None:
    # paths and stars: classical graceful families
    for n in range(2, 12):
        path = [(i, i + 1) for i in range(n - 1)]
        f = graceful(n, path)
        assert f is not None and verify_labeling(n, path, f), f"path {n}"
        star = [(0, i) for i in range(1, n)]
        f = graceful(n, star)
        assert f is not None and verify_labeling(n, star, f), f"star {n}"
    print("  ok   paths and stars n = 2..11 graceful with verified labelings")
    # verifier negative controls
    path = [(0, 1), (1, 2), (2, 3)]
    assert not verify_labeling(4, path, [0, 3, 1, 1])   # not injective
    assert not verify_labeling(4, path, [0, 1, 2, 3])   # labels 1,1,1 collide
    assert not verify_labeling(4, path, [0, 3, 1, 5])   # out of range
    print("  ok   negative controls: bad labelings rejected by the verifier")
    # parent-array round trip on a known tree
    e = parse_parents("0 1 1 2 2")
    assert e == [(1, 0), (2, 0), (3, 1), (4, 1)], e
    print("  ok   parent-array parsing")
    print("all gates: PASS")


def sweep(lines) -> int:
    t0 = time.time()
    total = 0
    failures = []
    for line in lines:
        edges = parse_parents(line)
        if edges is None:
            continue
        n = len(edges) + 1
        total += 1
        f = graceful(n, edges)
        if f is None or not verify_labeling(n, edges, f):
            failures.append(line.strip())
    dt = time.time() - t0
    print(f"trees {total:,}  graceful-with-verified-labeling "
          f"{total - len(failures):,}  UNGRACEFUL {len(failures)}  [{dt:.1f}s]")
    for t in failures:
        print("UNGRACEFUL", t)
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
