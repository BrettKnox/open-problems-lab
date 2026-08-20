# Erdős–Gyárfás: computation log

Machine: AMD Ryzen 7 7840HS, 27.8 GiB RAM, Windows 11; geng from nauty 2.8.9
(user-space Debian package extract under WSL Ubuntu), checker in Python 3.14.
`check.py --verify` runs the gates; sweeps pipe `nauty-geng` (WSL) into
`check.py --stdin` (Windows).

## Gates

- Generator: geng counts match published values exactly — connected graphs on
  8 vertices: 11,117; connected cubic on 8/10 vertices: 5/19 (OEIS A002851);
  connected min-deg-3 on 8/10 vertices: 2,589/5,203,110 (OEIS A007112).
- Checker controls (spectra by an independent networkx cycle enumeration):
  K4 → 4, K3,3 → 4, Petersen → 8, Heawood → 8, C7 → none. Fast checker equals
  the reference on 60 random graphs; a deliberately false verdict is caught.
- **The gate earned its keep on first contact**: the initial cycle-search
  pruning had an off-by-one (a vertex `left` steps from closing the cycle may
  sit at distance `left + 1` from the anchor), which made the fast checker
  miss Petersen's C8. Caught by the control, fixed, re-gated.

## Sweeps (conjecture verification; a counterexample = graph with NO
power-of-two cycle)

General connected min-deg-3, C4-free (the reduction `sweep_reduction` proved
in `OpenProblemsLab/ErdosGyarfas.lean` justifies restricting to C4-free):

| n | C4-free min-deg-3 graphs | counterexamples | time |
|---|---|---|---|
| 12 | 57 | 0 | 1 s |
| 13 | 368 | 0 | ~1 s |
| 14 | 6,059 | 0 | 0.7 s |
| 15 | 91,433 | 0 | 11 s |
| 16 | 1,655,659 | 0 | 184 s |
| 17 | 34,758,006 | 0 | 4,884 s |

With `sweep_reduction` (Lean), the n ≤ 17 sweep verifies the conjecture for **all** graphs
of min degree 3 on ≤ 17 vertices — i.e. any counterexample has ≥ 18 vertices by this
independent method. (The widely copied but never-sourced folklore said "≥ 17"; the current
frontier is Balaji's unrefereed SAT n ≥ 32, of which this re-verifies the low range by a
second method.) n = 18 (~×18 more graphs) needs the forge window with a compiled checker.

Connected **cubic** C4-free (target: Markström's Congr. Numer. 171 (2004)
record — all cubic ≤ 28 verified; exactly 4/23/251 graphs on 24/26/28
vertices have neither C4 nor C8):

| n | C4-free cubic graphs | no C4 & no C8 | counterexamples | time |
|---|---|---|---|---|
| 20 | 36,101 | 0 | 0 | 41 s |
| 22 | 553,227 | 0 | 0 | 894 s |
| 24 | **9,467,449** | **4** ✓ (Markström: 4; all four contain a C16) | 0 | 8×~1h parallel |

The n = 24 line is a full independent reproduction of Markström's hardest
published data point, by different tools (geng vs minibaum, Python bitset DP
vs Fortran) on different hardware, 22 years later.

## Measured scaling and the record frontier

geng's C4-free cubic generation runs at ~880 graphs/s single-core here and the
class grows ~×17 per +2 vertices: n = 26 ≈ 1.6×10⁸ graphs ≈ 19 h 8-way
(overnight/forge), n = 28 ≈ 2.7×10⁹ ≈ two weeks 8-way (forge), n = 30 (the
step past the published record) ≈ 4.6×10¹⁰ ≈ months — **that extension needs
a compiled filter + wider parallelism (forge window), or a generator that
prunes C8 during generation**. The general-graph lane past n ≈ 17 belongs to
SAT (Balaji 2026 reached 31, unrefereed); our sweep independently re-verifies
the low range with a second method.

Barrier statement (per campaign rules): plain geng-based enumeration cannot
reach cubic n = 30 on this machine; unblock = forge-window res/mod farm with
a C filter, or C8-aware pruned generation.
