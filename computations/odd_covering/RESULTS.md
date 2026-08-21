# Odd covering systems: computation log

Erdős problem #7: is there a covering system of ℤ with all moduli odd,
distinct and > 1? ($25 from Erdős for "no", $2000 from Selfridge for an
explicit example.) Known: no odd *squarefree* covering exists, and any odd
covering has lcm divisible by 9 or 15 (Balister–Bollobás–Morris–
Sahasrabudhe–Tiba 2022).

Every verification here uses the finite-period criterion proved in
`OpenProblemsLab/OddCovering.lean` as `isCovering_of_covers_period`: moduli
dividing L cover ℤ iff they cover {0,…,L−1}.

## Rigorous: the density screen

A covering needs Σ 1/mᵢ ≥ 1. For a shape (an lcm L), the best possible is
`Σ_{m | L, m odd, m ≥ 3} 1/m`, so any L below that threshold is dead with no
search at all. Over the admissible shapes (odd L with 9 | L or 15 | L, per
BBMST):

| L ≤ | admissible shapes | killed by density (proof) | survive |
|---|---|---|---|
| 200,000 | 15,556 | **15,165 (97.5%)** | 391 |

The tightest survivors are remarkably marginal — L = 32,445 clears the bar
with density **1.0002** across 23 odd moduli, and eight shapes sit below
1.002. Odd moduli barely reach the density threshold at all, which is the
quantitative reason odd coverings are hard to build.

## What the density bound is *not*

A gate here corrected a natural guess: the distinct odd moduli 3..15 already
have density **1.0218 > 1** (3..13 gives 0.9551), so density is satisfiable
and is therefore *not* the obstruction. The real obstruction is overlap: for
{3, 5, 15} on L = 15 the naive count 5 + 3 + 1 = 9 is unreachable, because
CRT forces the mod-3 and mod-5 classes to meet in exactly one residue — the
exact maximum is **8**. Both facts are gates in `density.py`, and both were
found by the gates rejecting an assertion I had written the other way round.

## Heuristic: coverage lower bounds per shape

Branch-and-bound over residue choices (best coverage of ℤ/L by one class per
modulus), 25 s budget per shape. These are **lower bounds** — the budget was
hit in every case, so they bound nothing from above:

| shape | L | odd moduli | density | best found | gap |
|---|---|---|---|---|---|
| 9·5·7 | 315 | 11 | 0.9810 | 241 | 74 |
| 27·5·7 | 945 | 15 | 1.0317 | 554 | 391 |
| 9·25·7 | 1575 | 17 | 1.0470 | 909 | 666 |
| 9·5·7·11 | 3465 | 23 | 1.1610 | 2045 | 1420 |
| 9·5·7·13 | 4095 | 23 | 1.1333 | 2387 | 1708 |
| 15·7·11·13 | 15015 | 31 | 1.1483 | 9262 | 5753 |

(9·5·7 has density < 1, so it is dead by the rigorous screen regardless.)

## Barrier

The B&B is far too weak to settle any surviving shape: the search is over
∏ mᵢ residue assignments, and even L = 3465 exhausts a 25 s budget without
closing. Settling one survivor needs a real solver — the natural next step is
a SAT/ILP encoding (one variable per residue class choice, clauses forcing
every residue of ℤ/L covered), which pysat can carry. That is the OC-3 pass;
the density screen above is what makes it worth pointing at the 391 survivors
rather than all 15,556 shapes.
