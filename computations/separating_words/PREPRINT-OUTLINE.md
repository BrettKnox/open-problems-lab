# Separating words: formalization note outline

Written 2026-09-12 as a preprint outline. Corrected and re-scoped on 2026-09-13, after an
independent verifier's review, from a combinatorics preprint to a formalization note: what is
formally proved in Lean, what is certified computation, and the combinatorics credited to
Bulatov, Karpova, Shur and Startsev (BKSS) and to Tran. Nothing committed.

## 0. Read this first: the literature search killed the headline

The SW-5 conjecture `N(k) = 2k - 3 + lcm(1..k)`, "so N(5) = 67", is **false**, and the
counterexample has been in print since 2017.

Bulatov, Karpova, Shur and Startsev (Electron. J. Combin. 24(3) (2017) #P3.35,
doi:10.37236/6450, arXiv:1609.03199), Theorem 8, verbatim (extracted text of the E-JC PDF):

> Semigroup Tk satisfies the following identity of length 2lcm(k-1)+6(k-1):
> (xy)^(k-2+lcm(k-1)) (yx)^k (xy)^(k-1) ≡k (xy)^(k-2) (yx)^k (xy)^(k-1+lcm(k-1))

Their Fact 1 says `u ≡k v` holds iff no k-state DFA separates u and v, and they define
"the length of the identity (u,v)" as max(|u|,|v|). At k = 5, lcm(1..4) = 12, so both sides
have length 48: no 5-state DFA separates two distinct words of length 48, so sep(48) >= 6
and **N(5) <= 47**, not 67. Their Proposition 14 states "Sep(15) = ... = Sep(40) = 5;
Sep(48) > 5", with Sep(n) taken over words of length at most n. Their Remark 7 says an
exhaustive computer search shows identities (4), of length lcm(k) + 2k - 2, are the
shortest binary identities in T_k for k <= 4. That is the "exact for k <= 4" observation
SW-5 called new. It was preempted a second way too: Tran's Table 1 (jumps at n = 4, 10, 18)
gives N(1..4) = 0, 3, 9, 17, and DESW Theorem 1 gives N(k) <= 2k - 3 + lcm(1..k), which
equals those four values. Their Conjecture 10 is that identity (5) is the shortest identity
of T_5, which would give N(5) = 47.

Checked here, independently of their proof:
`C:/Users/bman0/Code/OpenProblemsLab/computations/separating_words/bkss_identity.py`,
output in `C:/Users/bman0/Code/OpenProblemsLab/computations/separating_words/bkss_identity.log`
(`python bkss_identity.py`, 0.7 s): 0 of 166,152 canonical transition functions on <= 5
states separate the length-48 pair, and 0 of 1,000,000 random raw (function, start state)
pairs do. Controls: with L = 11, 56,382 functions separate; 199 of 200,000 random 6-state
functions separate the length-48 pair; the DESW n = 18 pair has 0 separators on <= 4 states
and 9,738 on <= 5.

This is the third time this lane nearly claimed a result that was already published
(Tran's table, DESW Theorem 1, now BKSS). The repo files that carried the false conjecture
were corrected on 2026-09-13 (section 7).

**Consequence for the paper.** It cannot be about the N(k) formula, or about new values.
What survives is formalization (Lean) plus an independent, certificate-backed reproduction
of exact values. That is a formalization note. It is not a result on the open problem.

## 1. Working title and venue

**Separating words in Lean: accept-set elimination, kernel-checked small values, and the
block-shift lower bound, with certified computation**

Venue: a formalization note (ITP or CPP short paper, or an arXiv cs.FL / cs.LO note). The
combinatorics is prior work and is credited as such (section 3c).

Alternative, if the BKSS length-48 identity is formalized first (section 8, item 1):
*Formalizing lower bounds for separating words, from the block shift to a length-48 identity
in T_5*.

## 2. Abstract draft (about 170 words)

We formalize the basic machinery of the separating words problem in Lean 4 with Mathlib.
The separating words function sep(n) is the least number of DFA states that distinguishes
every pair of distinct binary words of length n; its growth lies between Omega(log n) and
O(n^{1/3} log^7 n), and this note does not narrow that gap. Formally proved: accept sets are
irrelevant to separation; sep(n) <= n + 2, so sep is well defined; sep(1) = 2 and
sep(4) = 3, kernel-checked without native_decide; and Theorem 1 of Demaine, Eisenstat,
Shallit and Wilson, that a k-state automaton cannot see a block shifted by lcm(1..k), with
the instance that five states fail at length 68. Separately, as certified computation
outside the kernel, an exhaustive search over canonical transition functions, with saved
certificates and negative controls, reproduces sep(n) for n <= 30. The values themselves
are prior work: Tran (2023) for n <= 18, and Bulatov, Karpova, Shur and Startsev (2017) for
sep(n) = 5 through n = 40, the shortest identities for k <= 4, and a length-48 identity
giving sep(48) >= 6, which the length-68 instance does not reach.

## 3. What is formally proved, what is certified computation, what is credited

Lean file: `C:/Users/bman0/Code/OpenProblemsLab/OpenProblemsLab/SeparatingWords.lean` (line
numbers as of commit a9d82fb; the 2026-09-13 docstring corrections shift them in the working
tree). Build status: GitHub Actions CI (`leanprover/lean-action`) passed on a9d82fb
(`gh run list`, run created 2026-09-04T21:36:42Z, conclusion success). After the 2026-09-13
docstring-only edits: `lake build OpenProblemsLab.SeparatingWords` locally, exit 0, 1047 jobs.
`#print axioms` for all 15 public theorems is saved in
`C:/Users/bman0/Code/OpenProblemsLab/computations/separating_words/axioms.txt`
(`lake env lean SWAxioms.lean`, file content recorded in the header): every theorem depends
only on propext, Classical.choice and Quot.sound or a subset; none on sorryAx or
Lean.ofReduceBool.

### 3a. Formally proved (Lean)

**C1. Accept-set elimination, formal.** `exists_separates_iff_exists_eval_ne` (line 65)
and `exists_eval_ne_iff_exists_step` (line 212). A k-state separating DFA exists iff some
k-state transition function and start state send the two words to different states.
*Literature:* stated informally by Tran 2023 ("It is clearly equivalent to the definition
of separation stated initially in [4] that does not involve accepting states") and in
BKSS 2017 Fact 1. **Status: formalization only.** No formal version found in the places
searched (section 6).

**C2. `sep` is well defined.** `suffStates_add_two` (line 147), `sep_le` (line 176),
`two_le_sep` (line 180). *Literature:* DESW Proposition 4 gives the informal d + 2 bound.
**Status: formalization only.**

**C3. Kernel-checked exact values.** `sep_one` (line 250) and `sep_four` (line 265), via
`suffStates_three_four` (line 235) and `not_suffStates_two_four` (line 243), both `decide`
with no `native_decide`. *Literature:* the values are in Tran 2023 Table 1 and DESW
("sep(1000, 0010) = 3"). **Status: formalization only.** No earlier formal separating-words
values turned up in the three places searched (section 6); that is the scope, not a
priority claim.

**C4. The block-shift lower bound, formal.** `iterate_eq_add_of_card_le` (line 338),
`not_separates_block_shift` (line 373), `not_suffStates_block_shift` (line 390),
`not_suffStates_five_68` (line 412). *Literature:* DESW 2011 Theorem 1; BKSS 2017
Proposition 5 proves this pair is the unique shortest uniform unbalanced identity.
**WEAKENED:** "5 states fail at length 68" is not the best known bound; BKSS Theorem 8
gives 48. **Gap:** no Lean lemma turns `¬ SuffStates k n` into `k < sep n`. That needs
monotonicity of `SuffStates` in k (add a dead state), and no such lemma is in the file,
so the Lean file does not yet state `6 <= sep 68`.

### 3b. Certified computation (outside the kernel)

**C5. Independent exact table, equal-length convention, n <= 30.** Artefacts:
`C:/Users/bman0/Code/OpenProblemsLab/computations/separating_words/run30.log`
(line 110 sequence; N(1..4) = 0, 3, 9, 17 at lines 9, 14, 25, 44; "N(5) >= 30" at line 75),
`C:/Users/bman0/Code/OpenProblemsLab/computations/separating_words/cert_k5_n30.npy`
(74-function certificate, line 77),
`C:/Users/bman0/Code/OpenProblemsLab/computations/separating_words/verify.log` ("all gates:
PASS", line 126; the n = 18 lower bound from 1,566,711,930 literal DFAs, line 119),
`C:/Users/bman0/Code/OpenProblemsLab/computations/separating_words/separate.py`.
**Reproduction, not new values:** n <= 18 is Tran 2023. For n = 19..30 the values follow from
BKSS Proposition 14 (Sep(n) <= 5 for all words of length <= 40, computer-assisted, in the
"length at most n" convention) plus the n = 18 lower bound. So these are an independent
reproduction in a different convention, with certificates. The "round(sqrt(n+3)) fails at
n = 28" remark is implied too. The certificate re-check ("VERIFIED [276.2s]") is reported in
RESULTS.md, but no log of it is in the repo.

**C6. Complete extremal-pair census at n = 4, 10, 18.** Artefact: the census lists in
`C:/Users/bman0/Code/OpenProblemsLab/computations/separating_words/RESULTS.md` (section
"Every extremal pair"), command `python separate.py --kmax 4 --census 18`. **WEAKENED:** at
n = 10 and n = 18 the two families found are BKSS identities (3) and (4) (their
Propositions 5 and 6). The n = 4 census (8 pairs) contains other shapes and is not covered
by that sentence. What is left is completeness of the lists at these three lengths. **No
log artefact:** the census output exists only inside RESULTS.md and must be regenerated into
a log before it can be cited.

Related work on certificates for this kind of claim: Kupferman, Lavee and Sickert (ATVA
2021, section 4) generate game-based certificates for DFA state bounds, including separation
by a DFA of a given size. The certificates here are simpler (a list of transition functions
whose joint signature is injective, and single unseparable pairs); the note should say how
they relate.

### 3c. Credited, not claimed

* **BKSS 2017:** sep(n) = 5 for 18 <= n <= 40 (Proposition 14 with the n = 18 lower bound);
  the lcm(1..k) + 2k - 2 identities are shortest for k <= 4 (Remark 7); uniqueness of the
  DESW pair among uniform unbalanced identities (Proposition 5); the length-48 identity of
  T_5, so N(5) <= 47 (Theorem 8); N(5) = 47 conjectured via Conjecture 10.
* **Tran 2023:** sep(n) for n <= 18 (Table 1). With DESW Theorem 1 it also gives exactness of
  2k - 3 + lcm(1..k) for k <= 4.
* **DESW 2011:** Theorem 1, the block shift, which C4 formalizes.

**Dropped as contributions** (kept as record, cite only as checks):

* SW-5 family scans: "2-block and 3-block families first collide at exactly n = 68",
  `C:/Users/bman0/Code/OpenProblemsLab/computations/separating_words/blocks.py`, no log
  artefact. The 2-block collision is DESW/BKSS identity (3). The 3-block collision
  `1^3 0 1^64 / 1^63 0 1^4` is BKSS identity (4). The shorter identity at 48 lies outside both
  families. This scan measured where two families collide, not N(5).
* The N(k) formula and "N(5) = 67": false (section 0). Retracted in the repo 2026-09-13.
* OEIS package:
  `C:/Users/bman0/Code/OpenProblemsLab/computations/separating_words/oeis_draft.txt`.
  The sequence is still absent from OEIS (section 6). The draft now cites BKSS Proposition
  14 and states that the values through n = 40 follow from it.

## 4. Related work (verified citations only)

Each entry was checked at source. The method is in brackets.

* **Goralcik and Koubek**, On discerning words by automata, ICALP 1986, LNCS 226, 116-122,
  doi:10.1007/3-540-16761-7_61 [Crossref]. Origin of the problem and S(n) = o(n). Cited
  by Chase for the Omega(log n) lower bound ("An easy example [3] shows f(n) = Omega(log n)",
  [3] being Goralcik and Koubek) and by BKSS ("presented already in [5]").
* **Robson**, Separating strings with small automata, IPL 30(4) (1989) 209-214,
  doi:10.1016/0020-0190(89)90215-9 [Crossref]. O(n^{2/5} log^{3/5} n).
* **Demaine, Eisenstat, Shallit, Wilson**, Remarks on separating words, DCFS 2011, LNCS 6808,
  147-157, doi:10.1007/978-3-642-22600-7_12 [Crossref]; arXiv:1103.4513v1 [PDF text].
  Theorem 1 verbatim: "No DFA of at most n states can separate the equal-length binary words
  w = 0^(n-1) 1^(n-1+lcm(1,2,...,n)) and x = 0^(n-1+lcm(1,2,...,n)) 1^(n-1)." The sentence
  before it: "This does not appear to have been known previously." They redefine S(n) with
  |w| = |x| = n. There is no table. Theorem numbering was checked in arXiv v1 only; the LNCS
  version is paywalled and unchecked. Consequence used here: the pair has length
  2n - 2 + lcm(1..n), so N(k) <= 2k - 3 + lcm(1..k).
* **Ebrahimnejad**, On the gap between separating words and separating their reversals,
  TCS 711 (2018) 79-91, doi:10.1016/j.tcs.2017.11.012 [Crossref]; arXiv:1605.04835 [PDF
  text: no table, no exhaustive computation, no lcm].
* **Bulatov, Karpova, Shur, Startsev**, Lower bounds on words separation: are there short
  identities in transformation semigroups?, Electron. J. Combin. 24(3) (2017) #P3.35,
  doi:10.37236/6450 [Crossref; E-JC PDF text]; arXiv:1609.03199 [arXiv abstract page, title
  and authors re-checked 2026-09-13]. Fact 1, Propositions 4-6 and 14, Remark 7, Theorem 8,
  Conjecture 10: see sections 0 and 3c. **The key prior work for this note.**
* **Chase**, Separating words and trace reconstruction, STOC 2021, 21-31,
  doi:10.1145/3406325.3451118 [Crossref]; arXiv:2007.12097v3 [PDF text]. Theorem 1
  verbatim: "For any distinct x, y in {0,1}^n, there is a deterministic finite automaton
  with O(n^{1/3} log^7 n) states that accepts x but not y."
* **Tran**, Variations of the separating words problem, CIAA 2022, LNCS 13266, 165-176,
  doi:10.1007/978-3-031-07469-1_13 [Crossref only; closed access, contents NOT checked].
* **Tran**, Separating words from every start state with Horner automata, AFL 2023, EPTCS
  386, 243-252, doi:10.4204/EPTCS.386.19 [Crossref]; arXiv:2309.02766 [PDF text]. The
  definition: separation "if it ends in different states after reading the strings for some
  (common) start state", with D∃(n) "between two distinct strings of length n". Table 1,
  "Values of D∃(n) and D∀(n) for 1 ≤ n ≤ 18", "obtained via exhaustive search", row
  D∃(n) = 2 2 2 3 3 3 3 3 3 4 4 4 4 4 4 4 4 5. All 18 terms equal run30.log line 110.
* **Kupferman, Lavee, Sickert**, Certifying DFA bounds for recognition and separation, ATVA
  2021, doi:10.1007/978-3-030-88885-5_4; arXiv:2107.01566 [arXiv abstract page, 2026-09-13].
  Certificates for the number of DFA states needed to recognize a language, from
  determinacy of a Prover/Refuter game; offline versus online certificates; the approach
  extends to certifying separability of regular languages by a DFA of a given size, which
  they note is NP-complete. Related work on certificates, not on sep(n) values. Full text
  not read.
* **Dumitru**, arXiv:2503.23184, claimed O(log^2 n), **withdrawn** in v2 (2 Apr 2025)
  [arXiv abstract page]. Withdrawal note: an error in the proof of Theorem 1, and
  correcting it gives no improvement.
* **Bathie**, Separating words with automata in the half-adversarial case,
  arXiv:2608.28385v1 (28 Aug 2026) [arXiv HTML]. Random u versus any v:
  O(log^{7/3} n polyloglog n) states with high probability. No exact values, no lcm, no
  formalization.
* **Nicol**, Further remarks on separating words, arXiv:2608.30928v1 (31 Aug 2026) [arXiv
  HTML]. O(d log n) for difference words with d runs, conjugates, NFA order and reversal.
  No exact values, no table, no formalization. lcm appears only in an NFA construction.
* **Xu**, An elementary proof of the O~(n^{1/3}) bound for separating words,
  arXiv:2609.08191v1 (7 Sep 2026 per the arXiv listing) [PDF text]. Theorem 1:
  S(n) = O(n^{1/3} (log n)^{7/3}). Unrefereed. If it holds, it improves the log power in
  Chase's bound. Cite it as a preprint and do not state it as the current best bound.
* **Shallit**, talk slides sep2.pdf (cs.uwaterloo.ca/~shallit/Talks/sep2.pdf), slide 29
  "Some data": S(n) for n <= 18, identical to Tran [PDF text]. Slides, not a publication.

**Current bounds, stated for the note:** Omega(log n) (Goralcik and Koubek; equal-length
version DESW Theorem 1; BKSS improve it by lower-order terms for infinitely many n) and
O(n^{1/3} log^7 n) (Chase, STOC 2021), with an unrefereed O(n^{1/3} (log n)^{7/3}) preprint
(Xu 2026). RESULTS.md attributed the Omega(log n) lower bound to DESW 2011; for words of
unrestricted length it is Goralcik and Koubek, which is how DESW Proposition 1 attributes
it. Corrected in RESULTS.md on 2026-09-13.

## 5. Proved, computed, credited, conjectured

| Statement | Kind | Where |
|---|---|---|
| accept sets irrelevant | proved (Lean) | `exists_separates_iff_exists_eval_ne`, `exists_eval_ne_iff_exists_step` |
| sep(n) <= n + 2; 2 <= sep(n) for n >= 1 | proved (Lean) | `sep_le`, `two_le_sep` |
| sep(1) = 2, sep(4) = 3 | proved (Lean, kernel `decide`) | `sep_one`, `sep_four` |
| no k-state DFA separates 1^a 0^(b+L) / 1^(a+L) 0^b (a, b >= k-1, lcm(1..k) divides L) | proved (Lean); DESW Thm 1 | `not_separates_block_shift` |
| ¬ SuffStates 5 68 | proved (Lean); true, not tight | `not_suffStates_five_68` |
| 6 <= sep 68 | **not in Lean** (needs k-monotonicity) | none |
| ¬ SuffStates 5 48 | **not in Lean**; published (BKSS Thm 8) | section 8, item 1 |
| sep(n) for n <= 18 | certified computation here; published (Tran 2023) | `run30.log`, `verify.log` |
| sep(n) = 5 for 18 <= n <= 30 | certified computation here (exhaustive, certificate); implied by BKSS Prop 14 | `run30.log`, `cert_k5_n30.npy` |
| sep(n) <= 5 for n <= 40 | published claim (BKSS Prop 14, computer-assisted); not checked here past n = 30 | BKSS 2017 |
| sep(48) >= 6, so N(5) <= 47 | published theorem (BKSS Thm 8); computed check here | `bkss_identity.py`, `bkss_identity.log` |
| N(1..4) = 0, 3, 9, 17, equal to 2k - 3 + lcm(1..k) | computed here; published (BKSS Remark 7; also Tran Table 1 with DESW Thm 1) | `run30.log` lines 9-44 |
| sep(n) non-decreasing in n | short proof in RESULTS.md "Method 4"; empirical gate (F); **not in Lean** | `verify.log` |
| extremal pair lists at n = 4, 10, 18 are complete | computed here; **no log artefact** | RESULTS.md census section |
| 40 <= N(5) <= 47 | published (BKSS) | BKSS Prop 14, Thm 8 |
| N(5) = 47 | **conjecture (BKSS Conjecture 10 implies it)** | BKSS 2017 |
| N(k) = 2k - 3 + lcm(1..k) | **false at k = 5**; retracted 2026-09-13 | `bkss_identity.log` |
| sep(n) = O(log n) | open conjecture | `logConjecture` (Lean, statement only) |

## 6. Literature search log (2026-09-12, corrected 2026-09-13)

What was searched, and what came back, including nothing:

* **arXiv site search** `"separating words"`, all fields, newest first
  (`https://arxiv.org/search/?query=%22separating+words%22&searchtype=all&order=-announced_date_first`):
  27 results. Re-fetched 2026-09-13 with curl and parsed from the result page. Eleven carry a
  2024-2026 date (the verifier's count was ten; all eleven from the re-fetch are listed):
  1. 2609.08191, Xu, An elementary proof of the O~(n^{1/3}) bound for separating words:
     relevant, section 4.
  2. 2608.30928, Nicol, Further remarks on separating words: relevant, section 4.
  3. 2608.28385, Bathie, Separating words with automata in the half-adversarial case:
     relevant, section 4.
  4. 2608.22271, Kjos-Hanssen and Rivera Petit, Exact versus unique nondeterministic
     automatic complexity: automatic complexity, not word separation; not read further.
  5. 2608.20186, Marquardt, Alchanat and Jain, Decoding silent reading from non-invasive
     EEG: unrelated (title).
  6. 2608.00979, Nakajima, Passing coarse marginal checks can be cheap (LLM persona panel):
     unrelated (title).
  7. 2605.28269, Gao, Ye, Nie and Qu, Dynamic topic modeling with a higher-order
     hypergraphical representation: unrelated (title).
  8. 2512.06169, Crawford, Morphologically-informed tokenizers for languages with
     non-concatenative morphology (Yoloxóchitl Mixtec ASR): unrelated (title).
  9. 2511.09197, Meyer and Buys, The learning dynamics of subword segmentation for
     morphologically diverse languages: unrelated (title).
  10. 2503.23184, Dumitru, A sharper upper bound for the separating words problem:
      withdrawn, section 4.
  11. 2501.03988, Karthika et al., Semantically cohesive word grouping in Indian languages:
      unrelated (title).
  "Unrelated (title)" means the title and authors show no connection to automata; those
  abstracts were not read. None of the eleven gives exact sep(n) values, the N(k) formula,
  N(5) = 67, or a formalization.
* **Semantic Scholar citations:** 28 papers cite DESW, 5 cite BKSS (2019 survey of small
  semigroups, 2022 twisted Brauer monoids, Martens CSL 2026 "Minimal DFAs witnessing
  language inequivalence" (abstract read: about witnessing DFAs for regular-language
  inequivalence, not word separation), Nicol 2026, Xu 2026). No paper found that settles
  BKSS Conjecture 10 or computes N(5).
* **Web searches:** separating words 2025; exact values 2024-2026; Lean/Isabelle/Coq
  formalization; lcm / 2k-3 / N(5); formal-conjectures; Ebrahimnejad; Tran 2022; Kuntewar,
  Anoop, Sarma (DCFS 2023, groups; not read); shortest identities in T_n; T_5 identity
  follow-ups. Also surfaced Kotemanee and Saengsura, Symmetry 18(8) 1247 (2026),
  "Stabilized identities in finite transformation semigroups" (abstract read: exponents
  and a three-letter identity class, not shortest identities or separation). Nothing
  found for exact values beyond n = 18 in the equal-length convention, or for
  `2k-3+lcm(1..k)` or `N(5) = 67`, other than BKSS as above.
* **OEIS** (oeis.org, fmt=text): `2,2,2,3,3,3,3,3,3,4,4,4,4,4,4,4,4,5` gives 7 hits (A000194,
  A260999, A090532, A168255, A238598, A305025, A003058), none about automata. The 30-term
  sequence: no results. BKSS's at-most-n sequence, 40 terms: no results.
  `0,3,9,17,67`, `3,9,17,67,69`, `0,3,9,17,67,69,431,853`, `4,10,18,68`: no results.
  Keyword queries "separating words automaton", "separating words automata",
  "Demaine Eisenstat Shallit Wilson", "Horner automata", "shortest identity
  transformation semigroup", "Bulatov Karpova Shur Startsev": nothing relevant.
  **Sequence still absent.**
* **Formalizations:** GitHub code search: `SeparatingWords language:Lean` 0 hits;
  `"separating words" language:Lean` (quoted) 0 hits; `separating words language:Lean`
  (unquoted) 73 hits, first page all unrelated (SeparatingDual etc.). The 2026-09-12 draft
  recorded the 73 against the quoted query; the verifier found the quoted query returns 0
  and 73 belongs to the unquoted one. `separating words repo:google-deepmind/formal-conjectures`
  0 hits. The formal-conjectures file tree (1,733 paths) contains
  `FormalConjecturesForMathlib/Computability/DFA.lean`, which defines synchronizing words
  (Cerny), not separation. The local Mathlib `Mathlib/Computability` has no separation
  results (grep "separat": 4 unrelated comments). **No formalization of separating words
  found in these three places** (GitHub code search, formal-conjectures, local Mathlib).
  Nothing wider was searched (no Isabelle AFP, Coq/Rocq or Agda library search beyond the
  web queries above), so no broader "first" claim is made.
* **Not checkable:** Tran CIAA 2022 full text (closed), the DESW LNCS version (closed), and
  the Kuntewar et al. DCFS 2023 full text (not attempted).

## 7. Files that carried the false conjecture (corrected 2026-09-13)

Each correction keeps the history: the retracted wording is quoted or struck, with the date
and the BKSS citation, and git history keeps the original.

* `C:/Users/bman0/Code/OpenProblemsLab/README.md`: table row 2 cites BKSS; results section 2
  retracts "N(k) = 2k-3+lcm(1..k), i.e. N(5) = 67" and "What is new is that it is exact
  wherever anything is known", reframes n = 19..30 as a reproduction, and scopes the two
  "first" claims to the searches actually run.
* `C:/Users/bman0/Code/OpenProblemsLab/computations/separating_words/RESULTS.md`: status
  line, N(k) table, square-root remark, literature comparison (BKSS entry added), the
  Omega(log n) attribution, "So what is actually new here", caveats, and the SW-5 section
  (marked RETRACTED with the original text kept under the notice).
* `C:/Users/bman0/Code/OpenProblemsLab/PASSES.md` rows SW-2 to SW-6.
* `C:/Users/bman0/Code/OpenProblemsLab/OpenProblemsLab/SeparatingWords.lean`: module header
  and the docstrings of the block-shift section, `not_suffStates_block_shift` and
  `not_suffStates_five_68`. Docstrings only; no theorem statement changed.
* `C:/Users/bman0/Code/OpenProblemsLab/computations/separating_words/blocks.py`: module
  docstring and gate (F) message (no longer "predicts N(5) = 67").
* `C:/Users/bman0/Code/OpenProblemsLab/computations/separating_words/oeis_draft.txt` and
  `C:/Users/bman0/Code/OpenProblemsLab/computations/separating_words/oeis_b_draft.txt`: cite
  BKSS Proposition 14 and state that the values through n = 40 follow from it.

## 8. Before the next step

1. Formalize BKSS Theorem 8 at k = 5: `¬ SuffStates 5 48`. The proof is a case split on
   the xy-cycle length and reuses `iterate_eq_add_of_card_le`. It would replace
   `not_suffStates_five_68` as the headline Lean result. No formal statement of any BKSS
   identity turned up in GitHub code search, formal-conjectures or the local Mathlib;
   nothing beyond those three was searched, so claim no more than that.
2. Add `SuffStates k n → SuffStates (k+1) n` and derive `k < sep n` from
   `¬ SuffStates k n`, so the Lean file can state `6 <= sep 48`.
3. Regenerate the census, the family scan, and the certificate re-check as log files, so
   C5 and C6 cite artefacts.
4. Done 2026-09-13: `#print axioms` for every public theorem, saved as
   `C:/Users/bman0/Code/OpenProblemsLab/computations/separating_words/axioms.txt`.
5. Venue decided: a formalization note (section 1), not a combinatorics result.
6. Open, and unreachable by the current exhaustive method (memory wall at n = 31): whether
   N(5) is 47 (BKSS Conjecture 10) or lies in [40, 46].
