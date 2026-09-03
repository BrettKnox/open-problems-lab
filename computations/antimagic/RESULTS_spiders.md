# Antimagic: probing the hard subcase (AM-3)

The Hartsfield-Ringel conjecture is settled for dense graphs (Alon et al.
2004) and regular graphs; the acknowledged hard end is **sparse trees with
many degree-2 vertices** — long paths hanging off a few branch points. This
pass went looking for computational difficulty there.

## Finding: there isn't any, at any size we can reach

Two probes, both using the sweep's hill-climber with an exact
branch-and-prune fallback, every labeling independently re-verified:

**All spider families up to 16 vertices** (3–6 legs, every length
composition — 426 families): all antimagic, and **every single one solved on
the first restart**. The exact fallback was never invoked.

**Subdivided stars S(r × L)**, the extremal shape, pushed far beyond the
exhaustive range:

| legs r | leg length L | vertices | restarts needed | seconds |
|---|---|---|---|---|
| 3 | 40 | 121 | 1 | 0.01 |
| 5 | 40 | 201 | 2 | 0.10 |
| 8 | 20 | 161 | 1 | 0.01 |
| 8 | 40 | 321 | 3 | 0.27 |
| 12 | 20 | 241 | 1 | 0.07 |

At 321 vertices the hardest instance still needs 3 random restarts and a
quarter of a second.

## What this means, and what it does not

It is evidence *for* the conjecture on the subcase where doubt is
concentrated, and it is consistent with the exhaustive sweep, where the
hill-climber found labelings for all 1,018,690,328 connected graphs on ≤ 11
vertices without the exact solver ever being needed.

It is **not** a proof, and the absence of hard instances is not the absence of
counterexamples: the search is heuristic-first, so it can only report that
labelings are easy to *find*, never that none exists. A counterexample, if one
exists, is either much larger than 321 vertices or is not of this shape.

The honest read is that degree-2-heavy trees are hard to prove, not hard to
label — the difficulty is in the mathematics, not the search. That argues for
spending the next pass on `isAntimagic` proofs for these families in Lean
(paths and caterpillars look reachable with the machinery already in
`Antimagic.lean` and `StarFacts.lean`) rather than on more computation.
