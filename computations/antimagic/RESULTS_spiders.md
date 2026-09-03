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


## A construction pinned down for the next Lean pass (AM-4)

Attempting `isAntimagic_pathGraph` surfaced a false start worth recording. The
obvious labeling — edge i (joining vertex i to i+1) gets label i+1, left to
right — gives vertex sums 1, 3, 5, …, 2m−1 in the interior with m at the far
endpoint, and that **collides exactly when m is odd**, at the interior vertex
v = (m−1)/2 where 2v+1 = m. For m = 5 the sums are 1, 3, 5, 7, 9, 5.

So the left-to-right labeling is antimagic **iff m is even** (checked for
every even m ≤ 198, and it fails for every odd m in 3..199). The fix for odd m
is to swap the last two labels, giving 1, 2, …, m−2, m, m−1. The resulting
two-case construction is verified antimagic for **all 2 ≤ m ≤ 400**.

That is the target for AM-4: the Lean proof needs a parity case split plus
path incidence sets (interior vertices carry two edges, endpoints one), which
is why it was queued rather than rushed. The draft was reverted rather than
left with a `sorry` — the falsity showed up precisely at the vertex-sum
obligation, which is the part a `sorry` would have hidden.
