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

## OC-4: the screen that replaced the search

OC-3 left 41 shapes undecided after 3 h 34 m of CDCL. All 41 are now closed,
along with everything else below 10^6 — **without any search at all**. The
change is not a faster solver; it is a necessary condition with no free
choices left in it.

### Step 1: the lcm must be an odd abundant number

A covering with lcm `L` uses only divisors of `L`, each at most once, and
adding congruences never hurts — so the *maximal* system (one class for every
odd divisor `m > 1` of `L`) is the best possible attempt at that lcm. Its
density is `sum_{m | L, m > 1} 1/m = sigma(L)/L - 1`, so density `>= 1` is
exactly **`sigma(L) >= 2L`**. The lcm of any covering system is therefore an
abundant number, and an odd covering's lcm must be an **odd abundant number**.

That collapses the problem to a short list: **43 candidates below 20,000,
1,996 below 10^6**. (This direction is standard — "covering number" is
established terminology and the recent
[arXiv:2507.23041](https://arxiv.org/abs/2507.23041) studies exactly the
relation `c(n) <= sigma(n)/n`. It is recorded here because it makes the
computation self-contained: no appeal to BBMST's 9-or-15 theorem is needed.)

The counting step is now formal: **`card_le_sum_of_covers_period`** in
[OddCovering.lean](OpenProblemsLab/OddCovering.lean) proves `L <= sum L/m_i`
from a covered period, axiom-clean.

### Step 2: the coprime screen

Let `T` be a set of **pairwise coprime** moduli. By CRT their classes are
independent, so *whatever classes are chosen* they cover exactly
`L(1 - prod_{m in T}(1 - 1/m))` — the choice is irrelevant. Everything else
adds at most `L/m` each. Requiring the total to reach `L` gives

        D  >=  sum_{m in T} 1/m  +  prod_{m in T} (1 - 1/m)

with `D = sum_{m | L, m > 1} 1/m`. `T = {}` returns the abundance test, so
this is a strict strengthening of it, and it has no free variables: a single
`T` that violates it kills the lcm outright.

It is sharper than it looks. Taking `T` to be the primes dividing `L`, the
share of the uncovered region reachable by a modulus `m` is

        f(m)/A = (1/m) * prod_{p | m} p/(p-1) = 1/phi(m)

exactly, so the criterion becomes the clean statement

> **A covering system with lcm `L` needs `sum 1/phi(m) >= 1`, summed over the
> divisors `m > 1` of `L` that are not prime.**

For `L = 945` that sum is 0.5946, less than 1 — dead in one line, where CDCL
needed 47 seconds.

### Step 3: coprime groups

The uncovered region is a product set over the prime coordinates, so a
pairwise coprime *group* of moduli is independent inside it too: the group
covers exactly `A(1 - prod(1 - 1/phi(m)))`, strictly less than the additive
`A * sum 1/phi(m)`. Partitioning the non-`T` moduli into coprime groups and
union-bounding across groups gives

        coverage / A  <=  sum_j [ 1 - prod_{m in G_j} (1 - u(m)) ].

Groups of size 1 recover the additive bound and size 2 recovers a
forced-overlap matching, so this is stronger than both. **Soundness holds for
any partition**, so the greedy grouping used here needs no optimality
argument — a better partition would only close more shapes.

This is what closes the hardest cases: `L = 675675 = 3^3·5^2·7·11·13` has
`sum 1/phi = 1.01268` (survives) but partition bound `0.99219` (dead).

### Result

| bound on lcm | candidates (odd abundant) | closed by the screen | time |
|---|---|---|---|
| 20,000 | 43 | **43** | < 1 s |
| 100,000 | 210 | **210** | 1.6 s |
| 1,000,000 | 1,996 | **1,996** | 49 s |

> **No odd covering system has lcm at most 10^6.**

No search, no SAT solver, no literature input, exact rational arithmetic
throughout. For contrast, OC-3 could not close 41 shapes below 20,000 in
3.5 hours of CDCL.

### The complete search, kept as a fallback

`dfs_cover.py` also contains a complete search, used to gate the screen and to
decide anything the screen misses. It branches on **which modulus covers the
smallest uncovered residue** — assigning that modulus's class completely, so
depth is the number of moduli rather than the number of variables — with a
per-modulus capacity bound (`bincount` of the uncovered set mod `m`) and two
symmetry reductions: WLOG `a_{m_max} = 0` (translation), and WLOG `a_p in
{0,1}` for every prime `p | L` simultaneously (multiplication by units, whose
components are independent across primes by CRT).

It is about 8x faster than CDCL on `L = 945` (5.7 s vs 47 s) — and still not
enough on its own: it timed out at 2e6 nodes from `L = 1575` upward. **The
screen, not the search, is what resolved this problem.**

### Validation

Eight gates (`python dfs_cover.py --verify`).

* **(A)–(C)** The classic 5-congruence covering of `Z/12` is found and
  verified, `{2,3,4,6}` is refuted by search despite density 1.25, and on
  **all 31 subsets of `{2,3,4,6,12}` the search agrees with brute force**.
* **(C2), (H)** The soundness tests. The screen must never fire on a modulus
  set that actually admits a covering — checked on every coverable subset of
  `{2,3,4,6,8,12,24}`, and on **71 coverable modulus sets across 8 lattices**
  (`L = 24 … 180`) with the group correction active, using the complete search
  as the oracle. Zero false fires.
* **(D)** Verdicts are identical with and without symmetry breaking.
* **(E)** The abundance screen reproduces OEIS A005231 exactly.
* **(F)** `L = 945` and `2205`, the only two shapes CDCL closed, come out
  UNSAT here in 0 nodes.

Caveats:

* The screen is one-sided: firing proves impossibility, not firing proves
  nothing. Every claim above is a firing.
* Even moduli are used throughout the gates precisely because coverings there
  exist and can therefore catch an unsound screen; the odd case has no known
  positive instance to test against.
* The greedy partition is not optimal, so the frontier below is an artifact of
  the heuristic as much as of the mathematics.

### Frontier: 10^7

The full sweep to 10^7 finishes in 19 minutes and kills **20,649 of 20,661**
candidates (99.94%), leaving twelve:

| L | factorization |
|---|---|
| 2,027,025 | 3^4·5^2·7·11·13 |
| 3,378,375 | 3^3·5^3·7·11·13 |
| 3,828,825 | 3^2·5^2·7·11·13·17 |
| 4,279,275 | 3^2·5^2·7·11·13·19 |
| 4,729,725 | 3^3·5^2·7^2·11·13 |
| 6,081,075 | 3^5·5^2·7·11·13 |
| 6,185,025 | 3^3·5^2·7^2·11·17 |
| 6,891,885 | 3^4·5·7·11·13·17 |
| 7,432,425 | 3^3·5^2·7·11^2·13 |
| 7,702,695 | 3^4·5·7·11·13·19 |
| 8,783,775 | 3^3·5^2·7·11·13^2 |
| 9,324,315 | 3^4·5·7·11·13·23 |

So: **any odd covering system with lcm at most 10^7 has lcm among those twelve
values.** Every one is `3·5·7·11·13` with extra prime powers or one extra
prime — the numbers where the odd divisors pile up fastest, and the criterion
weakens exactly as `sum 1/phi(m)` clears 1 by more (1.016 to 1.026 on the
partition bound, against the 1.0 it needs to beat).

These will not fall to more of the same. The complete search is far out of
reach (about 10^2 moduli over a period of 2·10^6 to 10^7), and a better
partition cannot help by much: every modulus divisible by 3 must land in a
different coprime group, forcing at least ~70 groups, so the group correction
is second-order however it is chosen. Extending the T family to prime powers
was tried and closes none of the twelve.

What is left is the looseness the criterion still has on *mixed* moduli:
prime-power towers are handled exactly (the classes mod 3, 9, 27, 81 cover
exactly 40/81 of the 3-coordinate at best), but moduli like 15, 45, 105 are
credited `1/phi(m)` each with only coprime-group interactions subtracted.
Capturing the tree structure across coordinates is the next idea, and it is a
different argument rather than a tuning of this one.
