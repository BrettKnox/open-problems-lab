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

## OC-3: SAT over the survivors

The B&B above is far too weak, so the survivors were handed to CaDiCaL with a
proper encoding (`sat_cover.py`): one variable per (modulus, class),
exactly-one per modulus, and a clause per residue of Z/L demanding some chosen
class hits it. UNSAT at a shape is a *proof* that no odd covering system has
that lcm.

Two engineering facts were load-bearing, both found the hard way:

* **Pairwise at-most-one is unusable.** Modulus 32445 alone would need
  ~5.3e8 clauses; the first run died with `MemoryError`. Replaced by pysat's
  sequential counter (linear in m).
* **Translation symmetry is worth a factor of L.** Shifting every class by a
  common t maps coverings to coverings, so one modulus's class can be fixed
  outright; fixing the largest (L itself, always a divisor) uses the full Z/L
  action. Effect on the smallest survivor L = 945: from *unsolved after 400 s*
  to **UNSAT in 47 s**.

Result over all admissible shapes L <= 20,000, with a 2e6 conflict budget per
shape (3 h 34 m total):

| outcome | shapes |
|---|---|
| killed by the density bound (proof, no search) | **1,513** |
| proved impossible by SAT (L = 945, 2205) | **2** |
| undecided - conflict budget exhausted | 41 |
| **odd covering systems found** | **0** |

So: **any odd covering system with lcm <= 20,000 must have its lcm among 41
specific values** - the admissible space is narrowed from 1,556 shapes to 41,
and none of the 41 yielded a covering within budget. That is a narrowing, not
a resolution, and the log names exactly which shapes remain open.

## Barrier

The budget is the binding constraint, and it binds hard: per-shape time to
*exhaust* 2e6 conflicts grew from 85 s (L = 1575) to 984 s (L = 19845), and
the only two shapes that closed were the two smallest. Raising the budget 10x
puts each undecided shape at roughly 15 min - 3 h, i.e. ~1-2 machine-days for
the 41 - a forge-window job, not a laptop one.

Whether more budget is even the right lever is unclear: these are structured
exact-cover instances, and a CRT-aware search (branching on residues modulo
each prime power in turn) or an ILP formulation may beat generic CDCL by more
than a constant. That is the OC-4 question.
