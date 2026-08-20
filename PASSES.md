# Campaign ledger

Multi-pass campaign state. Rule: a problem is parked only when its ladder is complete or a
pass ended at a documented barrier (what was tried, measured scaling, what unblocks it).
[FORGE] = deferred to the end-of-month credit window. Full ladder definitions live in the
session plan; criteria are restated here at completion time.

| # | Problem | Pass | Status | Outcome / criterion met |
|---|---------|------|--------|-------------------------|
| 0 | Tooling | P0 | done | networkx 3.6.1 ✓ (trees(7)=11); pysat+cadical153 ✓ UNSAT+proofs; nauty 2.8.9 via WSL user-space deb extract, geng gated (conn8=11117, cubic8=5, cubic10=19) |
| 1 | Integer complexity | IC-1 statement+proofs | done | Selfridge, n ≤ 9, defect layer, axiom-clean |
| 1 | Integer complexity | IC-2 table | done | exact to 2^32, k ≤ 32, 4 gates, reproduced |
| 1 | Integer complexity | IC-3 defect API | queued | — |
| 1 | Integer complexity | IC-4 Altman k≤48 repro | queued | — |
| 1 | Integer complexity | IC-5 k=49+ [FORGE] | queued | — |
| 2 | Separating words | SW-1 Lean reduction | done | accept-set irrelevance, sep≤n+2, sep≥2 |
| 2 | Separating words | SW-2 exact table | done | n ≤ 30, Tran reproduced, √-law killed at 28 |
| 2 | Separating words | SW-3 OEIS package | queued | — |
| 2 | Separating words | SW-4 formal sep values | queued | — |
| 2 | Separating words | SW-5 n=31+ wall | queued | — |
| 3 | Erdős–Gyárfás | EG-1 source-verify records | in progress | — |
| 3 | Erdős–Gyárfás | EG-2 baseline repro | queued | — |
| 3 | Erdős–Gyárfás | EG-3 extension [FORGE] | queued | — |
| 3 | Erdős–Gyárfás | EG-4 Lean lemmas | queued | — |
| 4 | EP #414 | TT-1 stream census | queued | — |
| 4 | EP #414 | TT-2 Lean structure | queued | — |
| 4 | EP #414 | TT-3 merge theorems | queued | — |
| 5 | Superpermutations | SP-1 Egan word in Lean | queued | — |
| 5 | Superpermutations | SP-2 SAT calibration n=5 | queued | — |
| 5 | Superpermutations | SP-3 871 verdict [FORGE] | queued | — |
| 6 | Antimagic | AM-1 sweep | queued | — |
| 6 | Antimagic | AM-2 Lean families | queued | — |
| 6 | Antimagic | AM-3 hard subcase | queued | — |
| 7 | Graceful | GT-1 repro | queued | — |
| 7 | Graceful | GT-2 feasibility [FORGE] | queued | — |
| 7 | Graceful | GT-3 Lean families | queued | — |
| 8 | W(2,7) | VW-1 Lean certificates | queued | — |
| 8 | W(2,7) | VW-2 record attempt | queued | — |
| 9 | Odd covering | OC-1 Lean API | queued | — |
| 9 | Odd covering | OC-2 shape search | queued | — |
| 10 | Subset sums | DS-1 repro | queued | — |
| 10 | Subset sums | DS-2 search | queued | — |
| 10 | Subset sums | DS-3 Lean witness | queued | — |
| 11 | Erdős–Moser | EM-1 Moser odd-k in Lean | queued | — |
| 11 | Erdős–Moser | EM-2 GMZ repro | queued | — |
| 11 | Erdős–Moser | EM-3 record [FORGE] | queued | — |
| 12 | Lehmer | LT-1 Lean lemmas | queued | — |
| 12 | Lehmer | LT-2 sweep | queued | — |
| 12 | Lehmer | LT-3 ω bound [FORGE] | queued | — |

Cycle 1 order: 3 → 4 → 5 → 8 → 6 → 7 → 12 → 9 → 10 → 11, IC/SW passes interleaved as
background permits. Cycle 2 = all [FORGE] under credits. Cycle 3 = re-verify, promote, repeat.
