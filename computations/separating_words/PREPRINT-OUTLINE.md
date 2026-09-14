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
`#print axioms` for all public theorems (15; 21 after the 2026-09-13 BKSS additions) is saved in
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
*Prior Lean (found 2026-09-13, section 6b):* Nicol's repository `jn1z/FurtherRemarks`
(2026-08-31) already proves the unary lcm periodicity for DFAs
(`dfa_evalFrom_zero_add_lcmUpto`: hypotheses card σ <= stateBound <= base, period
`Nat.lcmUpto stateBound`, where `iterate_eq_add_of_card_le` needs only k <= a + 1) and a
one-marker block-shift non-separation for NFAs (`noNFASeparatorOfSize_asymmetry_fst`, one
orientation, under `UnaryTransferConditions`, a hypothesis quantified over every NFA within
the state bound). C4 is not the first formal lcm periodicity for automata. The two-block DFA
statement `not_separates_block_shift` was not found there (name grep of its 27 Lean files).
**WEAKENED:** "5 states fail at length 68" is not the best known bound; BKSS Theorem 8
gives 48. [Gap closed 2026-09-13: `suffStates_succ` (add an unreachable state),
`suffStates_mono` and `lt_sep_of_not_suffStates` turn `¬ SuffStates k n` into `k < sep n`.]

**C4b. BKSS Theorem 8, formal (added 2026-09-13).** `not_separates_bkss`,
`not_suffStates_five_48`, `six_le_sep_48`. *Literature:* BKSS 2017 Theorem 8 and its proof;
the Lean proof transcribes it. **Status: formalization only.** Checked 2026-09-13 against a
search for earlier formalizations of semigroup identities (sections 6b and 6c): no formal
BKSS identity, and no formal identity of the (xy)^a (yx)^b (xy)^c shape, found in the places
listed there. Do not write "first formal two-letter identity of T_k": this repo's own
`not_separates_block_shift` (C4, a9d82fb, 2026-09-04) already states one in
transition-function form (x^a y^(b+L) = x^(a+L) y^b), and Nicol's `reversalTheorem7` states,
in separation form (`¬HasSeparatorOfSize N x y` for distinct binary x, y of length L), pairs
that by accept-set elimination (C1; BKSS Fact 1) are two-letter identities of T_N. The
closest prior Lean is Nicol's `jn1z/FurtherRemarks` (unary lcm periodicity, an lcm power
acting as the identity on a DFA's transition image, and that separating-words lower bound),
which the note must cite.

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
by that sentence. What is left is completeness of the lists at these three lengths. Log:
`C:/Users/bman0/Code/OpenProblemsLab/computations/separating_words/census.log` (2026-09-14;
`--kmax 2 --census 4`, `--kmax 3 --census 10`, `--kmax 4 --census 18`, each exit 0): 8, 4 and
4 pairs, identical to the RESULTS.md lists.

Related work on certificates for this kind of claim: Kupferman, Lavee and Sickert (ATVA
2021; abstract read, full text not) generate game-based certificates for DFA state bounds, including separation
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
  `C:/Users/bman0/Code/OpenProblemsLab/computations/separating_words/blocks.py`, log
  `C:/Users/bman0/Code/OpenProblemsLab/computations/separating_words/blocks_scan.log`
  (2026-09-14; `python blocks.py --k 5 --nmin 20 --nmax 71` and the same with `--three`:
  no collision for 20 <= n <= 67 in either family, first collision at n = 68 in both, each
  pair needing 6 states by `min_states`). The 2-block collision is DESW/BKSS identity (3). The 3-block collision
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
  No exact values, no table. lcm appears only in an NFA construction. Corrected
  2026-09-13: the paper text does not mention a formalization, but its author's GitHub
  repository `jn1z/FurtherRemarks` (created 2026-08-31) is a Lean formalization of its
  Theorems 6 and 7 [repository files read; not built here]; see section 6b.
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
| k-monotonicity of SuffStates; ¬ SuffStates k n → k < sep n | proved (Lean) | `suffStates_succ`, `suffStates_mono`, `lt_sep_of_not_suffStates` |
| no k-state DFA separates (01)^(k-2+L) (10)^k (01)^(k-1) / (01)^(k-2) (10)^k (01)^(k-1+L) (c ∣ L for c < k) | proved (Lean), following BKSS's proof of their Thm 8 | `not_separates_bkss` |
| ¬ SuffStates 5 48 | proved (Lean); published (BKSS Thm 8) | `not_suffStates_five_48` |
| 6 <= sep 48 | proved (Lean); published (BKSS Thm 8, Prop 14) | `six_le_sep_48` |
| sep(n) for n <= 18 | certified computation here; published (Tran 2023) | `run30.log`, `verify.log` |
| sep(n) = 5 for 18 <= n <= 30 | certified computation here (exhaustive, certificate); implied by BKSS Prop 14 | `run30.log`, `cert_k5_n30.npy` |
| sep(n) <= 5 for n <= 40 | published claim (BKSS Prop 14, computer-assisted); not checked here past n = 30 | BKSS 2017 |
| sep(48) >= 6, so N(5) <= 47 | published theorem (BKSS Thm 8); computed check here | `bkss_identity.py`, `bkss_identity.log` |
| N(1..4) = 0, 3, 9, 17, equal to 2k - 3 + lcm(1..k) | computed here; published (BKSS Remark 7; also Tran Table 1 with DESW Thm 1) | `run30.log` lines 9-44 |
| sep(n) non-decreasing in n | short proof in RESULTS.md "Method 4"; empirical gate (F); **not in Lean** | `verify.log` |
| extremal pair lists at n = 4, 10, 18 are complete | computed here | `census.log` |
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
  web queries above), so no broader "first" claim is made. [2026-09-13: these GitHub queries
  used `language:Lean` only, while GitHub tags Lean 4 files `language:"Lean 4"`, and the
  code-search index turned out to contain neither this repository nor Nicol's Lean
  separating-words repository. The bullet stays true of the queries it ran, but its zeros are
  weak; see section 6b.]
* **Not checkable:** Tran CIAA 2022 full text (closed), the DESW LNCS version (closed), and
  the Kuntewar et al. DCFS 2023 full text (not attempted).

### 6b. Identity-formalization search (2026-09-13)

Question from section 8, item 1: has any identity of the full transformation semigroup T_n,
any BKSS identity, or a separating-words lower bound via identities been formalized in a
proof assistant? Every query is listed with its result, including nothing. Tools: GitHub REST
code search (`gh api -X GET search/code -f q=<query>`, 7 s apart, two batch scripts kept in
the session scratchpad, not in the repo), GitHub repository search
(`gh api -X GET search/repositories -f q=<query>`), `gh api` trees and raw contents, `curl`,
ripgrep on the local Mathlib checkout (d77ef0741c), and a web-search tool whose results come
back summarized by a model, so its "nothing found" is weak.

**Found: prior Lean work by Nicol.** `github.com/jn1z/FurtherRemarks`; account name John
Nicol (`gh api users/jn1z`); created 2026-08-31T16:07:43Z, one commit a4f77cb; description:
supporting files for arXiv:2608.30928. Found by repository search `"separating words"` (121
repositories, the only Lean one) and `"separating words" language:Lean` (1). Its README is
titled "Lean formalization of Theorems 6 and 7". All 28 files were downloaded (8,440 Lean
lines, `cat $(find . -name '*.lean') | wc -l`) and read in part:
* `NondeterministicPaper.lean`, `dfa_evalFrom_zero_add_lcmUpto`: for `D : DFA Bool σ` with
  `Fintype.card σ ≤ stateBound ≤ base`, reading `base + Nat.lcmUpto stateBound` zeros from
  any state ends where `base` zeros do. This is the unary identity x^b = x^(b + lcm(1..k)) of
  T_k for b >= k, in DFA form, four days before this repo's `iterate_eq_add_of_card_le`
  (commit a9d82fb, 2026-09-04, threshold b >= k - 1).
* `Nondeterministic.lean`, `noNFASeparatorOfSize_asymmetry_fst`: under unary pump and period
  conditions, no NFA with at most `bound` states accepts `0^bound 1 0^(tail+period)` and
  rejects `0^(bound+period) 1 0^tail` (one orientation, NFAs).
* `ReversalsPaperCommonPower.lean`, `transitionImagePerm_pow_lcmUpto_eq_one`,
  `evalFrom_repeatWord_lcmUpto_eq`, `eval_common_lcm_power_eq`: if a word permutes the image
  of a DFA with at most N states, its `Nat.lcmUpto N`-th power is the identity on that image,
  so two such words have indistinguishable lcm powers after a common prefix. A group-exponent
  law used inside T_N, conditional on the permutation hypothesis.
* `ReversalsPaper.lean`, `reversalTheorem7`: there are c0 > 0 and K such that for every
  N >= 2 and every L >= N^(c0 N) there are distinct binary words of length L that no DFA with
  at most N states separates, while their reversals have a separator with K * clog2(N + 2)
  states. A formal separating-words lower bound, sep(L) > N once L >= N^(c0 N), weaker than
  Omega(log n).
* `DFA.lean`, `HasSeparatorOfSize.mono`: monotonicity in the state count.
* `grep -rniE 'Bulatov|BKSS|Karpova|Shur|Startsev|Demaine|DESW|semigroup|T_k|identit'`: 7
  lines, all "identity" in the permutation or list-bookkeeping sense. No BKSS citation, no
  two-letter identity of the `(xy)^a (yx)^b` shape, no DESW two-block pair for DFAs.
* `grep -rnwE 'sorry|axiom|native_decide|admit'`: no matches. The repository has no lakefile
  or lean-toolchain, and `Nat.lcmUpto` is absent from the local Mathlib (which has
  `Chebyshev.lcmUpto`), so it targets a newer Mathlib. **Not built here.**
* The arXiv HTML of 2608.30928v1 (`curl`, then grep for lean, github, formaliz, proof
  assistant, mechani): no mention of Lean or the repository outside arXiv's page chrome. It
  cites BKSS once, for the link between lower bounds and identities in transformation
  semigroups.

The 2026-09-12 formalization bullet above was scoped to its queries and stays true of them,
but those queries missed a Lean separating-words formalization that was already public.

**GitHub code search control: failed.** `not_suffStates_five_68`, which is in the public
`OpenProblemsLab/SeparatingWords.lean` of BrettKnox/open-problems-lab (`gh api .../contents`
then `grep -c`: 1): total_count 0. `nondeterministicAsymmetryTheorem6` (in jn1z): 0.
`repo:jn1z/FurtherRemarks lcm` and `repo:BrettKnox/open-problems-lab lcm`: 0, with
incomplete_results true. `SuffStates`: 39, all brad-ross/apm. Neither formalization is in the
index, so every code-search zero below is weak evidence.

GitHub code search, Lean (`language:Lean` count / `language:"Lean 4"` count):
* `"transformation semigroup"`: 0 / 6 (the-omega-institute/automath, 3 files;
  paulklemstine/Lean `Catalog/Tropical/MagmaMonoid/Transformation.lean` in 3 copies, fetched:
  a magma-monoid construction, no identity of T_n).
* `"transformation monoid"`: 1 (yihuang/lean-cordix, effect tracking) / 45 (first 15 by path;
  fetched wsollers/lra-lean `TransformationMonoid.lean`, 65 lines, defines the full
  transformation monoid with instances and no theorems, and alok/cordis-lean
  `Cordis/Transformation.lean`, effect independence).
* `"full transformation"`: 1 (kim-em/hex-dev, unrelated) / 25 (the same repositories plus
  unrelated paths).
* `"semigroup identity"`: 3 (quantum channels) / 30 (first 15: heat, Markov and quantum
  semigroups; TheLanguageGamer/R1Undecidable `SemigroupModel.lean`, fetched: word-problem
  soundness, no identity of T_n).
* `"semigroup identities"`: 0 / 2 (oflatt/lean-decomp, kaplan196883/QIQT-H; unrelated by
  path).
* `Bulatov`: 1 (GrigoryEvko/FX `PostCloneLattice.lean`, fetched: the Bulatov-Zhuk CSP
  dichotomy, stated as not proven) / 25 (adrianioancozma/cubegraph and GrigoryEvko/FX, CSP).
* `Karpova`: 0 / 2 (RadixExperiment slides). `Startsev`: 0 / 2 (VladimirReshetnikov/ProveIt,
  Ramsey).
* `"separating words" language:"Lean 4"`: 3 (crypto, tensor networks, trominoes, by path).
  `"separating word" language:"Lean 4"`: 21 (first 15 by path: group theory, surfaces, tensor
  networks; no automata). `"separating words" language:Lean`, rerun: 0.

GitHub code search, other languages and all of GitHub:
* Isabelle: `"transformation semigroup"` 5, all copies of AFP `Kleene_Algebra/Dioid.thy`
  (fetched: a remark that near-semirings are influenced by partial transformation
  semigroups); `"transformation monoid"` 7, copies of `Group_Theory.thy` (AFP
  Jacobson_Basic_Algebra and HOL/New_Algebra; fetched: a comment on translations);
  `"full transformation"` 2 (IsaFoL); `"semigroup identity"` 0; `"semigroup identities"` 0;
  `"separating words"` 0. With `repo:isabelle-prover/mirror-afp-devel`:
  `"semigroup identities"` 0, `"separating words"` 0, `"full transformation"` 0.
* Coq (`language:Coq`): `"transformation semigroup"` 0; `"transformation monoid"` 1
  (tushar-dadlani/theory, geometry); `"full transformation"` 4 (why3-semantics, VeLLVM,
  yijing: unrelated by path); `"semigroup identity"` 3 (kim-em/proof `coq/groups.v`, fetched:
  monoid unit axioms; two Principia-Fractalis files); `"separating words"` 0.
  `language:"Rocq Prover"`: `"transformation semigroup"` 0, `"semigroup identity"` 3 (the
  same files), `"separating words"` 0. `repo:math-comp/math-comp "transformation monoid"`: 0.
* Agda: `"transformation semigroup"` 1, miking-lang/dppl-formalization
  `FullTransformationSemigroup.agda` (fetched: commented-out code adapted from Pitts, Locally
  Nameless Sets, POPL 2023, on actions of T_S for an infinite S; no identities of T_n);
  `"transformation monoid"` 10 and `"full transformation"` 5 (that file plus unrelated
  paths); `"semigroup identity"` 0; `"separating words"` 2
  (avikj/metacircular-interaction-prototype, unrelated by path).
* Mathlib on GitHub: `repo:leanprover-community/mathlib4 "transformation monoid"` 0,
  `"semigroup identity"` 0.
* No language filter: `"1609.03199"` 5 (photonics data files, a digit collision);
  `"37236/6450"` 0; `"Karpova" "Startsev"` 45 (name lists); `"words separation"` 180,
  `"shortest identity"` 91, `"short identities"` 238, `"separating words"` 12,185: the first
  15 of each unrelated by path.

GitHub repository search: `"transformation semigroup"` 4 and `"transformation semigroups"` 4
(gap-packages/sgpdec, GAP; markuspf/idris-trans, Idris, empty apart from LICENSE and README,
last push 2014-05-05; two Python packages); `transformation-semigroup` 5 (adds a TeX repo);
`"semigroup identities"` 0; `separating words automata` 2 (a Java lexer;
KaiyangTeng/Summer-Research, C++, separating three words by finite automata);
`semigroup lean` 10 (numerical, Markov and C0 semigroups; lean-summer-research/lean-semigroup,
file list read: Green's relations and Rees matrices; timharv4755-crypto/SemigroupsLean,
empty); `semigroup isabelle` 1 (Hoare semigroups); `semigroup coq` 2 (numerical semigroups,
inverse semigroups).

Local Mathlib (ripgrep):
* All of `Mathlib/`, pattern
  `transformation (semigroup|monoid)|full transformation|semigroup identit|monoid identit|satisf(y|ies) the identity|separating word|separat(es|ion) (of )?words`:
  1 line, `Algebra/NonAssoc/LieAdmissible/Defs.lean:15` (Lie-admissible, unrelated). The same
  pattern plus `Krohn|aperiodic monoid|syntactic (semigroup|monoid)` over all of
  `.lake/packages`: 0.
* `Mathlib/Algebra/Group`: `Function.End` (`End.lean:48`, the monoid of maps α → α) and its
  action lemmas; no identities.
* `Mathlib/GroupTheory`: `lcm_cycleType` (`Perm/Cycle/Type.lean:181`) and `Exponent.lean`:
  group facts about S_n, not identities of T_n.
* `Mathlib/Computability`, pattern `semigroup|monoid|identit|separat|transformation|lcm|period`:
  21 lines, none about identities or separation.
* `Mathlib/Dynamics/PeriodicPts/Lemmas.lean`: `minimalPeriod_le_card` (line 79) and
  `isPeriodicPt_factorial_card_of_mem_periodicPts` (line 83), reusable infrastructure.
  `Chebyshev.lcmUpto` (`NumberTheory/Chebyshev.lean:213`) is lcm(1..n).

formal-conjectures (pushed 2026-09-12T21:27:52Z): recursive tree, 1,733 paths, not
truncated; grep `semigroup|monoid|transform|identit|separat|automat|DFA|word|variet`: 4 paths
(two GCDMonoid files, `Computability/DFA.lean`, `MetricSeparated.lean`). Code search in the
repo: `Semigroup` 2 (Erdős 481, affine-map semigroups; Erdős 435, numerical semigroups;
fetched), `"Function.End"` 0, `separating` 1 (Erdős 789, subset sums), `transformation` 4
(Green problem 19 on commuting transformations, Hilbert 5, square packing, LICENSE).

Isabelle AFP: `https://www.isa-afp.org/topics/`, then the topic pages
`computer-science/automata-and-formal-languages/` (81 entry links) and `mathematics/algebra/`
(107): entry names read, none on transformation semigroups, semigroup identities or word
separation. The nearest are Combinatorics_Words (with its Graph_Lemma and Lyndon entries),
Two_Generated_Word_Monoids_Intersection, Myhill-Nerode, Functional-Automata,
Finite_Automata_HF, Regular-Sets, Free-Groups and PSemigroupsConvolution. All entry names:
`thys/` of isabelle-prover/mirror-afp-devel, 1,029 directories; grep
`semigroup|monoid|transform|identit|word|automat|variet|universal_alg|equation|birkhoff|krohn`:
30 names, none on these topics. The AFP search page is client-side (`/index.json`,
`/search/index.json`, `/entries/index.html`: HTTP 404), so no AFP full-text search ran apart
from the mirror code search above. Entry abstracts were not read.

Rocq/Coq: `rocq-prover.org/packages` and `coq.inria.fr/opam/www/` both return the same
80,543-byte page with no package names in the HTML. Instead, `released/packages` of
rocq-prover/opam: 590 names; grep
`semigroup|monoid|automat|transform|word|regular|lang|algebra|univers|variet|kleene|combi`
gives coq-algebra, coq-automata, coq-coalgebras, coq-functional-algebra,
coq-geocoq-algebraic, coq-geometric-algebra, coq-iris-heap-lang,
coq-mathcomp-algebra-tactics, coq-mathcomp-algebra, coq-mathcomp-word, coq-pautomata,
coq-reglang, coq-relation-algebra, coq-tree-automata, coq-universe-comparator and their
rocq- renames. No name mentions semigroups, transformations or identities. Package contents
were not searched.

Citations of BKSS: Semantic Scholar API (`/graph/v1/paper/DOI:10.37236/6450/citations`):
citationCount 5, the same five as on 2026-09-12. OpenAlex (`/works?filter=cites:W2520022270`):
2 (the small-semigroups survey, twisted Brauer monoids). Crossref `is-referenced-by-count`:
1. zbMATH API: the record, Zbl 1372.68156, was found; its citing documents were not
retrieved. Google Scholar, fetched as a keyword search for the title: the summary listed 2
results (Nicol 2026, Xu 2026) and not the BKSS record or its cited-by list, so no citation
count from it. None of the citing papers is itself a formalization; Nicol's repository
belongs to one of them and is not mentioned in it.

arXiv: the API (`export.arxiv.org/api/query`) gave HTTP 301 over http and HTTP 429 "Rate
exceeded." over https, so no API results. Site search, all fields:
`"transformation semigroup" Lean` "produced no results"; `"separating words" Lean`: no
results.

Web searches (summarized results):
1. `formalization "transformation semigroup" identities Lean OR Isabelle OR Coq`: no T_n
   identities (a CMU ITP course page, Lean-Auto, constructive semigroups with apartness
   arXiv:2008.11008).
2. `"separating words" automata formalized Lean OR Isabelle OR Coq OR Agda`: grammar
   formalizations (arXiv:2302.06420, arXiv:2602.12891) and DESW; nothing on separation.
3. `"semigroup identities" formal verification proof assistant`: Stein, arXiv:1201.3943
   (abstract read: two-variable identities, no proof assistant, not T_n); Litterick,
   Vernitski and Woods, arXiv:2511.13304, Capturing properties of planar diagrams in Lean
   proof assistant software (abstract read: orientation-preserving mappings formalized in
   Lean; no identities in the abstract). Full text checked by the verifier, section 6c: no
   occurrence of "identit".
4. `"full transformation monoid" Lean OR Isabelle OR Coq formalization`: Alonzo monoid theory
   arXiv:2312.05658 (defines transformation monoids in Alonzo; no identities).
5. `Bulatov Karpova Shur Startsev "short identities" transformation semigroups`: BKSS itself
   (arXiv, E-JC, dblp, author pages); nothing formal.
6. `site:leanprover-community.github.io "transformation semigroup" OR "transformation monoid" OR "semigroup identity"`:
   nothing from that domain.
7. `Equational Theories Project Lean semigroup identities transformation semigroup finite`:
   Tao's Equational Theories Project post (magma laws, twisting semigroups); nothing on T_n.
8. `agda-algebras equational logic varieties identities Agda formalization semigroup`: the
   Agda Universal Algebra Library (arXiv:2103.05581, arXiv:2103.09092; Birkhoff's HSP
   theorem): general equational logic, no identities of T_n.
9. `"identities" "full transformation semigroup" shortest identity T_n 2020 2024 2025`:
   mathematics only (Identities in full transformation semigroups on academia.edu; Kotemanee
   and Saengsura 2026; BKSS).
10. `Isabelle OR Coq "transformation semigroups" formalised library Krohn-Rhodes mechanized`:
    nothing formal.
11. `"separating words problem" Lean 4 formalization github 2026`: nothing; it did not
    surface jn1z/FurtherRemarks.
12. `"identity" "transformation semigroup" "lcm" automata lower bound formally verified proof`:
    BKSS and unrelated semigroup papers.
13. `"John Nicol" "separating words" Lean`: the arXiv abstract page only.

**What these searches support.** Prior Lean work exists in this lane: Nicol's repository
(2026-08-31) formalizes the unary identity of T_k for DFAs, an lcm power acting as the
identity on a DFA's transition image, an NFA block-shift non-separation, and a
separating-words lower bound (`reversalTheorem7`) whose DFA non-separation pairs are, by
accept-set elimination, two-letter identities of T_N. So two-letter identities of T_k were
already formal before BKSS Theorem 8 went in: Nicol's (separation form, 2026-08-31) and this
repo's `not_separates_block_shift` (2026-09-04). In the places above and in section 6c
(GitHub code and repository search, cloned Lean automata and semigroup repositories, local
Mathlib and mathlib4 master Computability, cslib, formal-conjectures, the Lean Zulip public
archive to 2026-08-25, AFP entry names, eight AFP abstracts and mirror code search, Rocq opam
package names, BKSS citation lists, arXiv site search and full text of five recent papers,
OpenAlex full-text filters, the listed web searches), nothing outside this repository was
found that formalizes BKSS Theorem 8 (their identity (5)), an identity of the
(xy)^a (yx)^b (xy)^c shape, a length-48 pair that no 5-state DFA separates, or DESW's
two-block DFA theorem. This is not "no BKSS identity": BKSS's identity (1), the unary lcm
identity, was already formal in Nicol's `dfa_evalFrom_zero_add_lcmUpto` (exponents >= k), and
their identity (3), the block shift, in this repo's `not_separates_block_shift` (corrected
2026-09-13 after the NOTE.md review). Limits: GitHub code search misses both known Lean separating-words
repositories; AFP and Rocq were checked by name (plus eight AFP abstracts); the arXiv API,
Semantic Scholar keyword search and dblp returned no results (HTTP 429, 429, bot check); the
Zulip archive is a snapshot of public streams only. Nothing else was searched.

### 6c. Verifier re-run and extra searches (2026-09-13)

Re-run of a sample of 6b, same day, same tools (`gh api`, `curl`, ripgrep), counts matched:
repository search `"separating words" language:Lean` 1 (jn1z/FurtherRemarks) and
`"separating words"` 121; `"transformation semigroup"` 4; `separating words automata` 2;
code search `not_suffStates_five_68` 0, `"transformation semigroup" language:"Lean 4"` 6 (the
same six paths), `"semigroup identities" language:"Lean 4"` 2 (same repositories); Semantic
Scholar citations of DOI:10.37236/6450: 5 (same five); OpenAlex `cites:W2520022270`: 2;
arXiv API: HTTP 429 again; local Mathlib d77ef0741c, the 6b pattern: 1 line
(`LieAdmissible/Defs.lean:15`); AFP `thys/` tree: 1,029 directories (the contents API
lists only 996, its 1,000-entry cap); jn1z/FurtherRemarks: one commit a4f77cb, 8,440 Lean
lines, 0 matches for `sorry|admit|native_decide`, `dfa_evalFrom_zero_add_lcmUpto` with
hypotheses `Fintype.card σ ≤ stateBound` and `stateBound ≤ base` (read in the clone).
This repo's a9d82fb: 2026-09-04T17:36:34-04:00 (`git show -s`), so four days after Nicol's.

New searches, each with its result:
* Lean automata repositories (repository search `automata language:Lean` 23,
  `DFA language:Lean` 5), shallow-cloned and grepped
  (`lcm|separat|semigroup|Bulatov|Shur|Startsev|Demaine|minimalPeriod`, `*.lean`):
  leanprover/cslib (237 formal files), ctchou/AutomataTheory, okinealb/verified-automata,
  fgdorais/lean4-automata, mperlade/automato_ketchup, AydenLamp/FinDFA,
  atarnoam/lean-automata, Lino5000/TwoWayAutomata, NaveenMaurya749/AutomataLean. Every hit is
  the ordinary word "separate" or a semigroup action in cslib's modal logic; no lcm, no
  identity, no word separation.
* Finite-semigroup Lean work. Lean Zulip public archive (leanprover-community/archive, HEAD
  ff5c7d69, 2026-08-25, 61,331 files under `zulip_json`; `git grep -i -F -c` for twelve
  patterns including `transformation semigroup`, `semigroup identit`, `separating words`,
  `Bulatov`, `Krohn`, `lcmUpto`; run at BelowNormal): 5 threads. The relevant one, #mathlib4
  "Formalization of algebraic theory of finite semigroups" (Howard Straubing, 2026-04-23):
  idempotents, ideals, Green's relations, Rees-Suschkewitsch, with Krohn-Rhodes as future
  work. Its repositories, cloned and grepped for identities, lcm, transformation monoids,
  varieties and separation: AydenLamp/thesis (26 Lean files, 6,481 lines; "identity" means
  identity element), lean-summer-research/lean-semigroup (28 files, 9,780 lines: no hits),
  AydenLamp/StableSemigroup (2 lines), plus timharv4755-crypto/Semigroup and b-mehta/Alien.
  Mathlib PRs by AydenLamp: #39048 and #40241 (positive powers, idempotent powers in finite
  semigroups), open, titles only. `exists_idempotent_pow` in AydenLamp/thesis is the generic
  finite-semigroup idempotent power, not a statement about T_k. The other four Zulip threads
  are unrelated (magma laws in the Equational stream, program synthesis, Option.map,
  Physlib). Zulip's own search API needs login (`"code":"UNAUTHORIZED"`, "Not logged in"), so
  it was not used.
* juanbono/krohn-rhodes-theory (repository search `krohn-rhodes`, 3; created 2026-08-18): two
  design documents, 0 Lean files.
* Kjos-Hanssen's Lean repositories on automatic complexity and CS theory (`user:bjoernkjoshanssen`,
  32): cstheory, ac-exercises, bay, pathvsword, pfa, qac, marginis cloned (200 Lean files,
  `find -name '*.lean' | wc -l` per repository: 9 + 40 + 10 + 30 + 1 + 34 + 76) and grepped
  for separation, lcm, transformation semigroups and Bulatov/Demaine/Shallit: two mentions of
  Shallit in ac-exercises comments, nothing on separation or identities.
* mathlib4 master 55a449c5f2 (2026-09-13T02:55:56Z): 29 Lean files of `Mathlib/Computability`
  fetched (top level and one subdirectory level), grep
  `separat|identit|semigroup|lcm|transformation`: 16 lines, none about word separation or
  semigroup identities.
* Isabelle AFP abstracts read (isa-afp.org entry pages): PSemigroupsConvolution,
  Two_Generated_Word_Monoids_Intersection, Combinatorics_Words,
  Transition_Systems_and_Automata, Finite_Automata_HF, Functional-Automata, Myhill-Nerode,
  Regular-Sets. None on transformation semigroup identities or word separation. AFP names
  matching `semigroup|monoid|transformation|identit|variet|separat` in the 1,029-name tree:
  MonoidalCategory, PSemigroupsConvolution, Two_Generated_Word_Monoids_Intersection and four
  separation-logic entries.
* Full text of recent papers, grepped for `lean|mathlib|formaliz|proof assistant|isabelle|coq|agda|github`:
  Kjos-Hanssen and Rivera Petit arXiv:2608.22271 (HTML; one "formalize", in the informal
  sense), Bathie arXiv:2608.28385 (HTML; none), Xu arXiv:2609.08191 (PDF via `pdftotext`,
  3,680 words; none), Dumitru arXiv:2503.23184v1 (PDF, 2,723 words; none). Litterick,
  Vernitski and Woods arXiv:2511.13304 (HTML): 0 occurrences of "identit"; "semigroup" only
  in a definition remark and two Semigroup Forum citations.
* OpenAlex full-text filters (`fulltext.search`): "separating words" with "Mathlib" 0,
  "semigroup identities" with "Mathlib" 0, "transformation semigroup" with "Mathlib" 0,
  "separating words" with "proof assistant" 4 (unrelated titles), "transformation semigroup"
  with "proof assistant" 3 (Locally Nameless Sets, ProverX, constructive semigroups),
  "transformation semigroup" with "Isabelle" 4 (unrelated), "separating words" with
  "Isabelle" 111 and with "Lean" 582 (first pages linguistics and lean manufacturing).
* GitHub code search, new: `lcmUpto DFA language:"Lean 4"` 9 (Erdős problem files, a
  portfolio file), `evalFrom lcm language:"Lean 4"` 0, `Bulatov Shur language:"Lean 4"` 0,
  `"separates" DFA language:"Lean 4"` 489 and `"Function.End" identity language:"Lean 4"` 127
  (first 20 of each unrelated by path), `repo:leanprover-community/archive` with
  `"transformation semigroup"` 0 and `"separating words"` 0 (git grep does find the first
  phrase there, in a 5.3 MB file, so this is another weak zero).
* Repository search, new: `semigroup identities` 2 (a Rust congruence-lattice tool, a GAP
  SONATA mirror), `semigroup language:Lean` 12 (Markov, C0, numerical, ordered semigroups and
  the repositories above), `finite semigroups language:Lean` 0, `transformation semigroup lean` 0.
* Web searches (summarized results, weak): Lean Zulip "transformation semigroup" or
  "transformation monoid" identity; `site:leanprover-community.github.io/archive` with
  "separating words", "semigroup identities" or "transformation semigroup"; Krohn-Rhodes
  formalized in Lean, Coq or Isabelle; "separating words" Lean formalization DFA lcm identity
  2026; "transformation semigroup" identity formalized Lean 4, Mathlib or proof assistant
  2025-2026. None surfaced a formalization of a semigroup identity of T_n.
* Not formal work, recorded because it turned up: CsanyiDavid/separating_words (C++,
  2023-11-28, "Calculate the S(n) function of the separating words problem for small n
  values"; read 2026-09-13 via `gh api`: 4 commits to 2023-12-27, files automata_gen.cc/.h,
  a Catch2 test and a main.cc whose `main` only returns 0, no output, table or README, so no
  computed S(n) values are published there and it does not preempt C5); sttawm/separating-words
  (2022, a PDF its README calls a flawed proof of a logarithmic bound).

One Python one-liner (JSON parsing of Semantic Scholar output, well under a second) ran at
normal priority; no other Python or Lean job ran for 6c.

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

1. Done 2026-09-13: BKSS Theorem 8 in Lean. `not_separates_bkss` (every k >= 2, any L
   divisible by 1..k-1) and `not_suffStates_five_48` (k = 5, L = 12). The proof uses
   BKSS's three arguments (f^(k-1) constant; all xy-cycles shorter than k; xy a k-cycle, so
   (yx)^k = 1), selected by a split on whether some state has k distinct xy-iterates rather
   than on the cycle through s.(xy)^(k-2); the section docstring gives the correspondence.
   It uses a new private period lemma instead of `iterate_eq_add_of_card_le`, whose
   hypothesis (every c <= k divides L) fails for L = lcm(1..k-1). No transformation is
   enumerated; `decide` only checks c | 12 for c < 5 and the lengths and distinctness of the
   two fixed words.
   Searched 2026-09-13 (sections 6b and 6c): no formalization of BKSS Theorem 8 (identity
   (5)), or of any identity of the (xy)^a (yx)^b (xy)^c shape, turned up in the places
   listed there. BKSS identities (1) and (3) were already formal (Nicol; this repo).
   Two-letter identities of T_k in general were already formal: this repo's
   `not_separates_block_shift` (2026-09-04) and, in separation form, Nicol's
   `reversalTheorem7`. The same search found that prior Lean work,
   Nicol's `jn1z/FurtherRemarks` (2026-08-31: the unary identity of T_k for DFAs, lcm powers
   acting as the identity on a DFA's transition image, and a separating-words lower bound),
   which GitHub code search does not index. So `not_separates_bkss` may be described only as
   "no earlier formalization of BKSS Theorem 8 found in these places", and the note must
   cite Nicol's repository as prior Lean formalization.
2. Done 2026-09-13: `suffStates_succ`, `suffStates_mono`, `lt_sep_of_not_suffStates`, and
   `six_le_sep_48 : 6 ≤ sep 48`. Build: full `lake build`, exit 0, 2404 jobs (verifier
   re-run; the exit code is recorded by the batch file itself, because the first wrapper,
   `cmd /c start /wait`, returns 0 whatever the job returns). Axioms: see `axioms.txt`
   (21 public theorems).
3. Done 2026-09-14 for the census and the family scans: `census.log` (C6), `families.log`
   (`separate.py --families 30` and `--families 34`), `blocks_scan.log` (two-block and
   three-block scans). Still to do: the certificate re-check as a log file, so C5 cites an
   artefact.
4. Done 2026-09-13: `#print axioms` for every public theorem, saved as
   `C:/Users/bman0/Code/OpenProblemsLab/computations/separating_words/axioms.txt`.
5. Venue decided: a formalization note (section 1), not a combinatorics result.
6. Open, and unreachable by the current exhaustive method (memory wall at n = 31): whether
   N(5) is 47 (BKSS Conjecture 10) or lies in [40, 46].
