# Antimagic sweep log

Machine: Ryzen 7 7840HS, Python 3.14, single-threaded; graphs from geng
(nauty 2.8.9 under WSL).

## Headline

**The Hartsfield–Ringel conjecture is verified for every connected graph on
at most 11 vertices.** All 1,018,690,328 connected graphs on 1–11 vertices
(counts match OEIS A001349: 1, 1, 2, 6, 21, 112, 853, 11117, 261080,
11716571, 1006700565) were given an explicit antimagic labeling, each one re-checked by an
independent verifier (bijection onto {1..m} plus pairwise-distinct vertex
sums, recomputed from scratch) — except `K₂`, which the exact search **proves
not antimagic** by exhaustion, exactly as the conjecture's lone exception
requires.

| n | connected graphs | verified antimagic | time |
|---|---|---|---|
| 1–7 | 996 | 996 (K₂ refuted) | < 1 s |
| 8 | 11,117 | 11,117 | 0.2 s |
| 9 | 261,080 | 261,080 | 5.0 s |
| 10 | 11,716,571 | 11,716,571 | 272 s |
| 11 | 1,006,700,565 | 1,006,700,565 | 28,541 s (7.9 h) |

The randomized hill-climber found a labeling for **every single graph** — the
exact branch-and-prune fallback was never needed above `K₂`. Antimagic
labelings are extremely plentiful at this scale; the conjecture's difficulty
is asymptotic, not small-scale.

## Method

Per graph: randomized labeling + hill-climbing on the number of colliding
vertex-sum pairs (label swaps, ≤ 24 restarts); on failure, an exact
branch-and-prune assigning labels edge-by-edge, pruning when two vertices
with all incident edges labeled share a sum — so "not antimagic" is only ever
declared by exhaustion. Every positive answer is certified by the labeling
itself and re-verified independently.

## Gates

`sweep.py --verify`: K₂ refuted by the exact search (the designed negative
instance); K₁ trivial; P₃/C₃/C₄/K₄ classical positives; stars `K_{1,m}`
(m = 2..8) as a cross-check of the Lean theorem `isAntimagic_starGraph`
(OpenProblemsLab/Antimagic.lean); exact-search labelings verified on 200
random graphs; negative controls (a non-bijective labeling and a
sum-colliding labeling) rejected by the verifier. Generator counts gated
against OEIS A001349.

## Literature position, honestly

We could find **no published exhaustive verification of the conjecture over
all connected graphs of a given order** (family results abound — paths,
cycles, wheels, complete graphs from Hartsfield–Ringel themselves; dense
graphs from Alon et al. 2004; regular graphs 2015–16 — and there are
exhaustive sweeps for *variant* notions such as distance antimagic). We do
not claim novelty beyond "we could not find one"; the sweep's value is the
certified baseline plus the harness.

Scaling: n = 11 ran at ~35k graphs/s and took 7.9 h; **n = 12 has ~164
billion connected graphs**, i.e. ~53 days single-threaded here — that is the
barrier, and the unblock is a compiled checker plus res/mod parallelism, not
more wall time on this one.
