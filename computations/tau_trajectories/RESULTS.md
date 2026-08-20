# EP #414: trajectory census log

Iterate `h(n) = n + τ(n)`. EP #414 asks whether all trajectories eventually
merge. `OpenProblemsLab/TauTrajectories.lean` proves every `2 ≤ m ≤ 30` merges
with the trajectory of 2 (kernel-checked); this census measures the phenomenon
at scale. Machine: Ryzen 7 7840HS, Python 3.14 + numpy 2.5, single-threaded.

## Headline

**Every starting point `2 ≤ m ≤ 10⁸ merges into the single stream containing
2.** No second persistent stream exists in range. The single stream is
achieved at `H* = 100,180,126`, only **+0.18 %** above `M = 10⁸` — and the
relative gap is the same at `M = 10⁷` (`H* = 10,018,018`). Runtime: 92 s at
`M = 10⁸` (100.0 M walker landings), 9.2 s at `M = 10⁷`.

At `M = 10⁷` (full summary retained): 3,311,227 walker births; two-thirds of
all starts lie directly on an earlier trajectory (`P(d1 = 0) = 0.669`, mean
`d1 = 0.944`); the deepest chain needs 21,187 steps to join the stream of 2.
The alive-stream count at any height stays ~15–25 — trajectories are born
constantly and die into each other at the same rate.

Scaling ladder (`--ladder`): `H* − M` = 1,118 / 4,494 / 2,242 / 18,018 at
`M = 10⁴..10⁷` — erratic but tiny relative to `M`.

## Mechanism (the parity story)

`τ(n)` is odd exactly when `n` is a square, so `h` flips the parity of a
trajectory exactly when it steps *from* a square. Between squares, streams of
opposite parity live on disjoint residues and cannot collide. The census
instruments this: most merges are "birth-anchored" (a start born straight
into the phase of its absorber), and the big deferred merges wait for a
square — e.g. at `M = 10⁸` the last holdout stream (carrying 30,228 starts,
depth 21,401) merges 42 steps after passing the square `100,180,081`. The
orbit of 2 itself flips parity only 12 times below `10⁷` (first flips at
4, 9, 64, 81, 784, 1521, …).

Refined empirical conjecture (stronger than EP #414 in range, and the shape a
proof would need): **there is one persistent stream; every trajectory joins it
within o(M) height, with square-adjacent parity flips as the merging
mechanism.**

## Validation

Five gates plus four negative controls, all passing (`census.py --verify
--negative-control`):
(A) sieve τ vs trial-division τ — exhaustive to 2,000 plus 10,000 random n
in windows up to 5×10⁷, and window edges; (B) `τ(n)` odd ⟺ `n` square,
elementwise to 10⁶; (C) the stepper reproduces **all 1,000 terms** of OEIS
A064491 (trajectory of 1); (D) the sweep equals an independent brute force
(explicit orbit sets, trial-division τ) on every start `m ≤ 3,000` in all
four recorded quantities, at a hostile chunk size; (E) results are invariant
across chunk sizes (SHA-256 digest equality); (G) census merge data for
`m ≤ 30` equals the kernel-checked Lean witnesses — the formal and empirical
layers agree exactly. Negative controls: parity-breaking and
parity-preserving τ corruptions, a corrupted A064491 step, and a corrupted
τ inside the sweep — each caught by the designed gate.

Provenance note: the harness was drafted by an agent that died mid-task; the
sweep had a real representation bug (streams and multi-walker slots were both
bare Python lists, indistinguishable), fixed in review — after which the
gates, which had never run, all passed. Digests: `584b34fb7369c189`
(M = 10⁷), `a219928acc9d0bde` (M = 10⁸).

## Honest framing

This is empirical evidence plus machine-checked instances, not a proof of
EP #414. What is *proved* (Lean, kernel, no native_decide): pairwise merging
for all `2 ≤ m, n ≤ 30`. What is *observed*: single-stream merging for all
`m ≤ 10⁸`. The distance between those is the open problem. Next lever: the
τ-parity lemma (`τ(n)` odd ⟺ square) is absent from mathlib — formalizing it
and the between-squares parity invariance would put the mechanism itself on
formal footing.
