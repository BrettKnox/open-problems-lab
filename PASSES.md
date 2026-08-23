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
| 1 | Integer complexity | IC-3 defect API | done | defect_mul_le subadditivity + Altman's k≤48 stability theorem stated verbatim (altmanStability); criterion met |
| 1 | Integer complexity | IC-4 Altman k≤48 repro | queued | — |
| 1 | Integer complexity | IC-5 k=49+ [FORGE] | queued | — |
| 2 | Separating words | SW-1 Lean reduction | done | accept-set irrelevance, sep≤n+2, sep≥2 |
| 2 | Separating words | SW-2 exact table | done | n ≤ 30, Tran reproduced, √-law killed at 28 |
| 2 | Separating words | SW-3 OEIS package | done | oeis_draft.txt + oeis_b_draft.txt in computations/separating_words; submission itself is a user action (needs an OEIS account) |
| 2 | Separating words | SW-4 formal sep values | done | sep 1 = 2 and sep 4 = 3 kernel-proved (no native_decide) via a second reduction eliminating the Set accept field; first formal sep values as far as determinable |
| 2 | Separating words | SW-5 n=31+ wall | queued | — |
| 3 | Erdős–Gyárfás | EG-1 source-verify records | done | folklore-17 debunked (no primary source; Royle checked ≤ 15); real records: general ≥ 32 (Balaji 2026 unrefereed), cubic ≥ 30 (Markström 2004), cubic bipartite ≥ 60 (Tranquilli 2026); README table sourced |
| 3 | Erdős–Gyárfás | EG-2 baseline repro | done | Markström n=24 reproduced exactly (4 no-C4-no-C8 among 9,467,449 C4-free cubic; 0 cex); general lane verified through n=17 (34.7M graphs at 17, 0 cex) ⇒ counterexample ≥ 18 by our method; curves measured, barriers documented |
| 3 | Erdős–Gyárfás | EG-3 extension [FORGE] | queued | target: cubic n = 30 via res/mod-parallel geng (beats peer-reviewed record) |
| 3 | Erdős–Gyárfás | EG-4 Lean lemmas | done | sweep_reduction (C4-free restriction justified) + exists_cycle_of_two_le_degree; axiom-clean; criterion (≥ 2 real lemmas) met |
| 4 | EP #414 | TT-1 stream census | done | ALL starts ≤ 10^8 merge into the single stream of 2 (H* = M + 0.18%); parity mechanism instrumented; 5 gates + 4 negative controls; census m ≤ 30 equals Lean witnesses exactly |
| 4 | EP #414 | TT-2 Lean structure | done | lt_step, step_add_two_le, merged_of_eq; τ odd ⟺ square proved (odd_card_divisors_iff_isSquare, absent from mathlib — upstreamable) + step parity preserved off squares / flipped at squares; axiom-clean |
| 4 | EP #414 | TT-3 merge theorems | done | merge_pairs_upTo30: all pairs 2 ≤ m,n ≤ 30 merge, kernel decide, no native_decide; first machine-checked EP #414 instances as far as determinable |
| 5 | Superpermutations | SP-1 Houston word in Lean | done | L 6 ≤ 872 proved; single native_decide axiom (720-perm check), length kernel-checked, word independently Python-verified |
| 5 | Superpermutations | SP-2 SAT calibration n=5 | done (barrier) | encoder gated on L(1..3) ± sym + negative control; reproduces L(4)=33 (UNSAT@32 54 s). n=5 L=149 (easiest rung) abandoned after 22.6 CPU-hours at 99.5% — a >1500x jump from n=4. Curve is a wall |
| 5 | Superpermutations | SP-3 871 verdict [FORGE] | DROPPED | dead by this route: if the easiest n=5 UNSAT is unreachable, n=6/871 is not a compute-budget problem. Reopen only with a Chaffin/TSP-style encoding, not a bigger machine |
| 6 | Antimagic | AM-1 sweep | done | conjecture verified for ALL connected graphs ≤ **11** vertices (1,018,690,328 graphs; 1,006,700,565 at n=11 alone in 7.9 h; labelings independently verified; K₂ refuted by exhaustion); no published sweep found; n=12 (164 bn) needs a compiled checker |
| 6 | Antimagic | AM-2 Lean families | done (stars) | isAntimagic_starGraph, m ≥ 2, axiom-clean; m=1 failure = the K₂ exception; paths/cycles remain as stretch |
| 6 | Antimagic | AM-3 hard subcase | queued | — |
| 7 | Graceful | GT-1 repro | done | all trees ≤ 18 vertices verified graceful (123,867 at n=18; A000055 gate; independent verifier; exact fallback never needed); curve measured — mid-20s need compiled climber [FORGE]; Fang's 35 stands |
| 7 | Graceful | GT-2 feasibility [FORGE] | scoped | C port of the ~60-line climber is the unblock; cost memo in RESULTS.md |
| 7 | Graceful | GT-3 Lean families | done (stars) | starGraph_isTree_and_graceful axiom-clean; star machinery shared with antimagic via StarFacts.lean; paths next |
| 8 | W(2,7) | VW-1 Lean certificates | done | ¬HasVdW 2 7 3703 and ¬HasVdW 2 6 1131 machine-checked (one native_decide each); Heule's public certs found one cell short of published records, full-length reconstructed via phase+boundary-flip and independently verified; conditional W-bounds pending vdW theorem (absent from mathlib) |
| 8 | W(2,7) | VW-2 record attempt | queued | — |
| 9 | Odd covering | OC-1 Lean API | done | IsCovering + finite-check reduction (period lemma) + classic 5-congruence system verified by decide + not-odd sanity; axiom-clean; density lemma deferred to OC-2 |
| 9 | Odd covering | OC-2 shape search | done | rigorous density screen kills 97.5% of admissible shapes L ≤ 200k (15,165 of 15,556) with no search; 391 survivors, tightest at density 1.0002; gates corrected two of my own wrong assertions (density IS satisfiable; CRT overlap is the obstruction); B&B barrier documented → OC-3 = SAT/ILP on survivors |
| 10 | Subset sums | DS-1 repro | done | Conway–Guy verified distinct exactly for ALL n ≤ 31 (blocked saturating DP, 10.4 GB at 31; n=32 barrier documented); gated vs brute force + negative controls; ratios 0.255→0.2427 reproduce the 0.23513 march |
| 10 | Subset sums | DS-2 search | queued [FORGE] | beat Bohman 0.22002 |
| 10 | Subset sums | DS-3 Lean witness | done | conwayGuy16: distinct subset sums, max 17305 < 2^15 (one native_decide, Python-cross-verified) |
| 11 | Erdős–Moser | EM-1 Moser odd-k in Lean | in progress | k=1 complete; chain formal through mod-m² (pairing → binomial → dvd_of_solution) AND power sums mod p (sum_pow_range_mod: ∑_{i<p} i^j ≡ −1 iff (p−1)∣j, bridging range-sums to ZMod p). Remaining: assemble into the odd-k contradiction |
| 11 | Erdős–Moser | EM-2 GMZ repro | queued | — |
| 11 | Erdős–Moser | EM-3 record [FORGE] | queued | — |
| 12 | Lehmer | LT-1 Lean lemmas | done | 4 lemmas axiom-clean: odd, squarefree, no-semiprime, ω ≥ 3 for composite solutions (Lehmer 1932's first bound); criterion (≥ 3 lemmas) exceeded |
| 12 | Lehmer | LT-2 sweep | done | no composite solution below 10^9 (7 h); the 50,847,535 solutions found equal π(10^9)+1 exactly — an independent confirmation that only 1 and the primes qualify |
| 12 | Lehmer | LT-3 ω bound [FORGE] | queued | — |

Cycle 1 order: 3 → 4 → 5 → 8 → 6 → 7 → 12 → 9 → 10 → 11, IC/SW passes interleaved as
background permits. Cycle 2 = all [FORGE] under credits. Cycle 3 = re-verify, promote, repeat.
