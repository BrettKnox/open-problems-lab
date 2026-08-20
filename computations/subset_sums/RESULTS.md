# Distinct subset sums: computation log

Machine: Ryzen 7 7840HS, 27.8 GiB RAM, Python 3.14 + numpy 2.5.

## Headline

**The Conway–Guy construction is verified exactly for every n ≤ 31**: the
n-element sets built from OEIS A005318 (`a_i = u(n) − u(n−i)`) have all 2ⁿ
subset sums pairwise distinct, with maxima

| n | max = u(n) | max / 2ⁿ | time |
|---|---|---|---|
| 20 | 267,420 | 0.25503 | 0.2 s |
| 24 | 4,172,701 | 0.24871 | 4.7 s |
| 28 | 65,679,652 | 0.24468 | 111 s |
| 29 | 130,828,948 | 0.24369 | 185 s |
| 30 | 261,127,540 | 0.24319 | 387 s |
| 31 | 521,203,175 | 0.24270 | 852 s |

— the ratio marching toward the 0.23513 limit of the Conway–Guy family, the
classical evidence that Erdős's conjectured `c·2ⁿ` lower bound (EP #1, $500)
is within a constant of the truth.

## Method, and why it is exact

Distinctness of all 2ⁿ subset sums is equivalent to every coefficient of
`∏ᵢ (1 + x^{aᵢ})` being ≤ 1. The DP array is uint8 with **saturating**
addition (clipped at 255), processed in 128M-entry blocks walking downward so
a source block is never overwritten before it is read — no overflow can fake
a pass, and the memory high-water mark stays ~1.3× the array. n = 31 needs a
~10.4 GB coefficient array; **n = 32 (~21 GB) is past this machine** — the
barrier; unblock = bitsliced 2-bit counters or an out-of-core pass (forge).

## Gates

`ds.py --verify`: (A) the DP agrees with independent brute-force enumeration
(sort all 2ⁿ sums, scan) on Conway–Guy sets n = 5..20; (B) the colliding set
{1,2,3} is rejected by both methods, and an engineered perturbation keeps the
methods in agreement; (C) the A005318 b-file (3,325 terms) is contiguity- and
head-checked. The u-values are OEIS data (cached, gitignored per CC BY-NC-SA).

## Lean

`OpenProblemsLab/DistinctSubsetSums.lean`: the 16-element set is a formal
witness — distinct subset sums (one `native_decide` counting the 65,536 sums
via image-cardinality) with max 17,305 < 2¹⁵, beating the trivial powers-of-two
construction by ×1.9.

## Literature position

Verifying the defining property of published sets is **validation, not
discovery**: Conway–Guy asserted distinctness (provable by their difference
argument), Lunnon computed the family, Bohman's 0.22002·2ⁿ variant is the
record construction. The value here is the certified harness plus exact
per-n confirmation on this hardware. DS-2 (searching below Bohman's constant)
is the open-ended lane [FORGE].
