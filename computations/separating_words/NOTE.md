# Separating words in Lean 4: accept sets, small values, the block shift, and a length-48 identity of $T_5$

Draft formalization note, 2026-09-13. Not submitted, not pushed. The author line and an
AI-assistance disclosure must be written before any submission.

<!-- Convention for this draft: every numeric claim is followed by a hidden comment naming the
repository file it comes from. Paths are relative to the repository root. Lean line numbers are
for OpenProblemsLab/SeparatingWords.lean as of commit 1ef7417 (unchanged at 6ba38e9). -->

## Abstract

We describe a Lean 4 formalization, on Mathlib, of basic facts about the separating words
problem. Its central result is Theorem 8 of Bulatov, Karpova, Shur and Startsev [BKSS]: for
every $k \ge 2$ and every $L$ divisible by all $c < k$, no DFA with $k$ states separates
$(01)^{k-2+L}(10)^k(01)^{k-1}$ from $(01)^{k-2}(10)^k(01)^{k-1+L}$, which at $k = 5$ gives
$\mathrm{sep}(48) \ge 6$. <!-- src: OpenProblemsLab/SeparatingWords.lean (not_separates_bkss, six_le_sep_48) -->
The mathematics of that theorem and of every other formalized statement here is prior work
(BKSS; Demaine, Eisenstat, Shallit and Wilson [DESW]; Tran [Tran]), and the Lean proof of
Theorem 8 follows the BKSS proof. Also formalized: accept sets are irrelevant to separation,
$\mathrm{sep}(n) \le n + 2$, $\mathrm{sep}(1) = 2$ and $\mathrm{sep}(4) = 3$ by kernel
evaluation, and the DESW block-shift theorem. <!-- src: OpenProblemsLab/SeparatingWords.lean (sep_le, sep_one, sep_four) -->
Separately, outside the kernel, an exhaustive search with a saved certificate reproduces the
published values of $\mathrm{sep}(n)$ for $n \le 30$. <!-- src: computations/separating_words/run30.log line 110 -->
Nothing here narrows the gap between the $\Omega(\log n)$ lower bound and the
$O(n^{1/3}\log^7 n)$ upper bound. <!-- src: computations/separating_words/PREPRINT-OUTLINE.md section 4 (Chase Theorem 1) -->

## 1. Introduction

A deterministic finite automaton (DFA) *separates* two words if it accepts exactly one of
them. For $n \ge 1$ let $\mathrm{sep}(n)$ be the least $k$ such that every pair of distinct
binary words of length exactly $n$ is separated by some DFA with $k$ states. The problem goes
back to Goralčík and Koubek [GK], as both [BKSS] and [Chase] cite it. Two conventions are in
use: [BKSS] define $\mathrm{Sep}(n)$ over words of length *at most* $n$, while [DESW] and
[Tran] use length *exactly* $n$. This note, the Lean code and the computation use length
exactly $n$. The at-most maximum ranges over more pairs, so $\mathrm{sep}(n) \le
\mathrm{Sep}(n)$, and the two functions differ: $\mathrm{Sep}(3) = 3$ ([BKSS] Proposition 14)
while $\mathrm{sep}(3) = 2$ ([Tran] Table 1).

**Bounds.** The lower bound $\mathrm{sep}(n) = \Omega(\log n)$ is classical ([GK], as [Chase]
cites it; the equal-length form is [DESW] Theorem 1). The best refereed upper bound we found is Chase's
Theorem 1: any two distinct words in $\{0,1\}^n$ are separated by a DFA with
$O(n^{1/3}\log^7 n)$ states [Chase]. <!-- src: computations/separating_words/PREPRINT-OUTLINE.md section 4 -->
An unrefereed preprint [Xu] claims an elementary proof of an $\tilde O(n^{1/3})$ bound; we do
not use it.

**What is known exactly.**

* [Tran], Table 1, computed by exhaustive search: $D_\exists(n)$ for $1 \le n \le 18$ is
  `2 2 2 3 3 3 3 3 3 4 4 4 4 4 4 4 4 5`. <!-- src: computations/separating_words/RESULTS.md lines 488-491 -->
  Tran's $D_\exists$ uses separation by end states from a common start state over two distinct
  strings of length $n$, so it is $\mathrm{sep}$ in the equal-length convention.
* [BKSS] Proposition 14 (computer-assisted): $\mathrm{Sep}(15) = \dots = \mathrm{Sep}(40) = 5$
  and $\mathrm{Sep}(48) > 5$. <!-- src: computations/separating_words/PREPRINT-OUTLINE.md section 0 -->
  Hence $\mathrm{sep}(n) \le 5$ for $n \le 40$, and with $\mathrm{sep}(18) = 5$ and
  monotonicity of $\mathrm{sep}$ in $n$ (below), $\mathrm{sep}(n) = 5$ for $18 \le n \le 40$. <!-- src: computations/separating_words/RESULTS.md lines 10-13 -->
* [BKSS] Theorem 8: the full transformation semigroup $T_k$ satisfies
  $$(xy)^{k-2+\ell}\,(yx)^k\,(xy)^{k-1} \;\equiv_k\; (xy)^{k-2}\,(yx)^k\,(xy)^{k-1+\ell},
  \qquad \ell = \operatorname{lcm}(1,\dots,k-1),$$
  an identity of length $2\ell + 6(k-1)$. By their Fact 1 ($u \equiv_k v$ iff no $k$-state DFA
  separates $u$ and $v$), at $k = 5$, $\ell = 12$ this is a pair of distinct words of length 48
  that no 5-state DFA separates, so $\mathrm{sep}(48) \ge 6$. <!-- src: computations/separating_words/PREPRINT-OUTLINE.md section 0 -->
* [BKSS] Remark 7: an exhaustive search shows that their identities (4), of length
  $\operatorname{lcm}(1,\dots,k) + 2k - 2$, are the shortest binary identities of $T_k$ for
  $k \le 4$. <!-- src: computations/separating_words/PREPRINT-OUTLINE.md section 0 -->

Write $N(k) = \max\{n : \mathrm{sep}(n) \le k\}$. Then $N(1), \dots, N(4) = 0, 3, 9, 17$ and
$40 \le N(5) \le 47$. <!-- src: computations/separating_words/RESULTS.md lines 136-147 -->
The upper bound uses monotonicity: if a transition function sends $u$ and $v$ to the same
state, it sends $ub$ and $vb$ to the same state, so $\mathrm{sep}(n+1) \ge \mathrm{sep}(n)$
(proof in `RESULTS.md`, Method 4; **not in Lean**).

**This note.** Section 2 gives the definitions as formalized. Section 3 lists the formalized
results with their Lean names and axioms. Section 4 describes a certified reproduction of
$\mathrm{sep}(n)$ for $n \le 30$. Section 5 says explicitly what is not new, including a false
conjecture this project published and retracted. Section 6 covers related formal work and the
scope of the one novelty statement we make. Section 7 lists what is open.

## 2. Definitions as formalized

File: `OpenProblemsLab/SeparatingWords.lean`. Toolchain `leanprover/lean4:v4.34.0-rc1`,
Mathlib revision `d77ef0741c`. <!-- src: lean-toolchain; lake-manifest.json; computations/separating_words/axioms.txt line 2 -->
Words are `List (Fin 2)`. Automata are Mathlib's `DFA α σ`, a structure with fields `step`,
`start` and `accept : Set σ`. The code blocks in this note are quoted from the file with
docstrings shortened and proofs omitted.

```lean
/-- `M` separates `u` and `v` iff it accepts exactly one of them. -/
def Separates {σ : Type} (M : DFA (Fin 2) σ) (u v : List (Fin 2)) : Prop :=
  ¬(u ∈ M.accepts ↔ v ∈ M.accepts)

/-- `k` states suffice for length `n`. -/
def SuffStates (k n : ℕ) : Prop :=
  ∀ u v : List (Fin 2), u.length = n → v.length = n → u ≠ v →
    ∃ M : DFA (Fin 2) (Fin k), Separates M u v

noncomputable def sep (n : ℕ) : ℕ := sInf {k | SuffStates k n}
```

Three remarks on these definitions.

1. The state set is exactly `Fin k`. Automata with fewer states are covered by
   `suffStates_succ` (section 3.5), which adds an unreachable state.
2. `sInf` of the empty set of naturals is `0`, so `sep` would be a junk value without an upper
   bound. `sep_le` (section 3.1) supplies one, and every theorem about `sep` goes through it.
3. $N(k)$ is **not** defined in Lean. Statements about $N(5)$ in this note are informal.

**Accept-set elimination.** The first formal step removes accept sets:

```lean
theorem exists_separates_iff_exists_eval_ne {k : ℕ} (u v : List (Fin 2)) :
    (∃ M : DFA (Fin 2) (Fin k), Separates M u v) ↔
      (∃ M : DFA (Fin 2) (Fin k), M.eval u ≠ M.eval v)

theorem exists_eval_ne_iff_exists_step {k : ℕ} (u v : List (Fin 2)) :
    (∃ M : DFA (Fin 2) (Fin k), M.eval u ≠ M.eval v) ↔
      ∃ (δ : Fin k → Fin 2 → Fin k) (s : Fin k), u.foldl δ s ≠ v.foldl δ s
```

Forward: acceptance depends only on the final state, so equal final states cannot separate.
Backward: take the accept set to be the singleton containing the state that $u$ reaches. The
second theorem removes the `accept : Set` field, which is not decidable, so that statements
about a fixed finite set of transition functions reduce to `foldl` computations that the
kernel can evaluate. In Mathlib `M.eval w` unfolds to `w.foldl M.step M.start` (`DFA.eval` is
`M.evalFrom M.start` and `DFA.evalFrom` is `List.foldl M.step`), so the forward direction of the
second theorem is the term `⟨M.step, M.start, hM⟩`; the backward direction takes the DFA
`⟨δ, s, ∅⟩`.

Together these say that `¬ SuffStates k n` holds exactly when there are two distinct words of
length $n$ that every $k$-state transition function, from every start state, sends to the
same state. By [BKSS] Fact 1 that is a pair of distinct words of length $n$ forming an identity
of $T_k$. **Dictionary to [BKSS]:** $x = 0$, $y = 1$, and their $q.w$ (the state reached from
$q$ reading $w$ left to right) is `w.foldl δ q`. The identity length of [BKSS] is
$\max(|u|,|v|)$; every pair used here has $|u| = |v|$, so no conversion is needed.

## 3. Results formalized

**Build and axiom evidence.** A full `lake build` of the repository finished with exit code 0,
2404 jobs, run at BelowNormal priority. The exit code was recorded by a batch file's
`%ERRORLEVEL%`, because `cmd /c start /wait` returns 0 whatever the child returns. <!-- src: computations/separating_words/RESULTS.md lines 30-33 -->
`#print axioms` for all 21 public theorems (`lake env lean SWAxioms.lean`; the file's
`#print` lines are recorded in the header of `axioms.txt`) was re-run after the last edit: exit
0, 8.4 s, output identical to the saved block. <!-- src: computations/separating_words/axioms.txt lines 42-79 -->
Every theorem depends on `propext`, `Classical.choice` and `Quot.sound` or a subset of them.
None depends on `sorryAx`, and none uses `native_decide` (so none depends on
`Lean.ofReduceBool`). <!-- src: computations/separating_words/axioms.txt lines 53-73 -->

Axiom sets below are abbreviated: **S** = `[propext, Classical.choice, Quot.sound]`,
**P** = `[propext]`.

### 3.1 Reduction and well-definedness

| Lean name | line | statement | axioms | mathematics from |
|---|---|---|---|---|
| `eval_ne_of_separates` | 71 | separation forces different end states | P | folklore |
| `exists_separates_iff_exists_eval_ne` | 79 | section 2 | P | [Tran] (stated as clearly equivalent), [BKSS] Fact 1 and the definition before it |
| `exists_eval_ne_iff_exists_step` | 226 | section 2 | none | same |
| `posDFA_evalFrom_val` | 106 | state of the counter-and-latch automaton after a prefix | `[propext, Quot.sound]` | helper |
| `suffStates_add_two` | 161 | `SuffStates (n + 2) n` | S | [DESW] Proposition 4 ($d + 2$ states when the words differ $d$ positions from the start) |
| `sep_le` | 190 | `sep n ≤ n + 2` | S | same |
| `two_le_sep` | 194 | `1 ≤ n → 2 ≤ sep n` | S | folklore |

<!-- src: line numbers and statements from OpenProblemsLab/SeparatingWords.lean; axioms from computations/separating_words/axioms.txt lines 53-59 -->

### 3.2 Kernel-checked small values

`sep_one : sep 1 = 2` (line 264) and `sep_four : sep 4 = 3` (line 279), through
`suffStates_three_four : SuffStates 3 4` (line 249) and
`not_suffStates_two_four : ¬ SuffStates 2 4` (line 257). All four have axioms S. The finite
cores are private lemmas proved by `decide`: every two distinct 4-letter words are separated
by some 3-state transition function, and no 2-state transition function separates `0110` from
`1010`. <!-- src: OpenProblemsLab/SeparatingWords.lean lines 237-291; computations/separating_words/axioms.txt lines 60-63 -->
The values are in [Tran] Table 1.

### 3.3 The block shift ([DESW] Theorem 1)

```lean
theorem iterate_eq_add_of_card_le {α : Type*} [Fintype α] {k : ℕ}
    (hcard : Fintype.card α ≤ k) (f : α → α) {a L : ℕ} (ha : k ≤ a + 1)
    (hL : ∀ c, 0 < c → c ≤ k → c ∣ L) : f^[a] = f^[a + L]

theorem not_separates_block_shift {k a b L : ℕ}
    (ha : k ≤ a + 1) (hb : k ≤ b + 1)
    (hL : ∀ c, 0 < c → c ≤ k → c ∣ L)
    (δ : Fin k → Fin 2 → Fin k) (s : Fin k) :
    (List.replicate a (1 : Fin 2) ++ List.replicate (b + L) 0).foldl δ s
      = (List.replicate (a + L) (1 : Fin 2) ++ List.replicate b 0).foldl δ s

theorem not_suffStates_block_shift {k L : ℕ} (hk : 1 ≤ k) (hL0 : 0 < L)
    (hL : ∀ c, 0 < c → c ≤ k → c ∣ L) :
    ¬ SuffStates k ((k - 1) + (k - 1) + L)

theorem not_suffStates_five_68 : ¬ SuffStates 5 68
```

Lines 362, 397, 417 and 446; axioms S for all four. <!-- src: OpenProblemsLab/SeparatingWords.lean; computations/separating_words/axioms.txt lines 64-67 -->
In words: iterating a map of a $k$-element set is eventually periodic with preperiod at most
$k - 1$ and period at most $k$, so a block of one letter that is at least $k - 1$ long can be
lengthened by $\operatorname{lcm}(1,\dots,k)$ without any $k$-state automaton noticing. [DESW]
Theorem 1 states this for $0^{n-1}1^{n-1+\operatorname{lcm}(1,\dots,n)}$ versus
$0^{n-1+\operatorname{lcm}(1,\dots,n)}1^{n-1}$; the Lean statement swaps the letters and allows
any block lengths $a, b \ge k - 1$. [BKSS] Proposition 5 shows this is the unique shortest
binary uniform unbalanced identity (their identity (3)). With $k = 5$ and $L = 60$ the pair has
length $4 + 4 + 60 = 68$. <!-- src: OpenProblemsLab/SeparatingWords.lean lines 434-451 -->
That bound is true and not tight: section 3.4 gives 48.

### 3.4 [BKSS] Theorem 8

```lean
theorem not_separates_bkss {k L : ℕ} (hk : 2 ≤ k) (hL : ∀ c, 0 < c → c < k → c ∣ L)
    (δ : Fin k → Fin 2 → Fin k) (s : Fin k) :
    ((List.replicate (k - 2 + L) [0, 1]).flatten ++ (List.replicate k [1, 0]).flatten
        ++ (List.replicate (k - 1) [0, 1]).flatten : List (Fin 2)).foldl δ s
      = ((List.replicate (k - 2) [0, 1]).flatten ++ (List.replicate k [1, 0]).flatten
        ++ (List.replicate (k - 1 + L) [0, 1]).flatten : List (Fin 2)).foldl δ s

theorem not_suffStates_five_48 : ¬ SuffStates 5 48
```

Lines 618 and 636; axioms S for both. <!-- src: OpenProblemsLab/SeparatingWords.lean; computations/separating_words/axioms.txt lines 68-69 -->
In the notation of [BKSS], for every $k \ge 2$, every $L$ with $c \mid L$ for all $0 < c < k$,
every transition function $\delta$ on $k$ states and every start state $s$:
$$s.(xy)^{k-2+L}(yx)^k(xy)^{k-1} \;=\; s.(xy)^{k-2}(yx)^k(xy)^{k-1+L}.$$
Taking $L = \operatorname{lcm}(1,\dots,k-1)$ recovers their Theorem 8. Both sides have length
$2L + 6(k-1)$; at $k = 5$, $L = 12$ that is 48, so `¬ SuffStates 5 48` is their statement at
$k = 5$ with no change of length convention. <!-- src: OpenProblemsLab/SeparatingWords.lean lines 467-476 -->
The two words are $(01)^{15}(10)^5(01)^4$ and $(01)^3(10)^5(01)^{16}$, the same 48-letter
strings that `bkss_identity.py` checks numerically (section 4.5). <!-- src: computations/separating_words/bkss_identity.log lines 3-4 -->

**Proof as formalized.** Let $f$ be the map of $xy$ and $g$ the map of $yx$ on the $k$ states.
The two sides send $s$ to $f^{k-1}(g^k(f^{k-2+L}s))$ and $f^{k-1+L}(g^k(f^{k-2}s))$. The BKSS
proof splits on the $f$-cycle through $s.(xy)^{k-2}$: (i) that state is on no cycle, and then
$f^{k-1}$ is a constant map; (ii) it is on a cycle of length $m < k$, so every $f$-cycle is
shorter than $k$ and has length dividing $L$, hence $f^{k-2+L}s = f^{k-2}s$, and
$f^{k-1+L}q = f^{k-1}q$ for every state $q$ because $f^{k-1}q$ lies on a cycle; (iii) $m = k$,
so $f$ is a $k$-cycle, $x$, $y$ and $yx$ act as permutations and $(yx)^k = 1$, after which the
two sides are the same word. The private
lemma `bkss_core` uses the same three arguments, chosen by a split that is simpler to state in
Lean:

* Some state $q$ has $k$ distinct iterates $q, fq, \dots, f^{k-1}q$. These are then all the
  states, and $f^k q = f^r q$ for some $r < k$. If $r = 0$, $f^k = \mathrm{id}$ and case (iii)
  applies. If $r = k - 1$, case (i). If $1 \le r \le k - 2$, the only cycle has length
  $k - r < k$ and the tail has length $r \le k - 2$, which is case (ii).
* No state has $k$ distinct iterates. Then every orbit repeats at indices $t_1 < t_2 \le k - 1$,
  so the tail is at most $k - 2$ and the period is less than $k$: case (ii).

The step $f^k = \mathrm{id} \Rightarrow g^k = \mathrm{id}$ is the private lemma `bkss_perm`.
If $f^k = \mathrm{id}$, reading $x$ is injective (equal images under $x$ give equal images
under $xy$, and $f$ is invertible), hence bijective on a finite set, and it semiconjugates $f$
to $g$ (Mathlib's `Semiconj.iterate_right`). The lemma `iterate_eq_add_of_card_le` of section
3.3 is not reused here: it needs every $c \le k$ to divide $L$, and $5 \nmid 12$. A private
period lemma, `iterate_add_eq_of_period`, replaces it. <!-- src: OpenProblemsLab/SeparatingWords.lean lines 478-490, 501-625 -->

Nothing enumerates transformations. In `not_suffStates_five_48`, `decide` checks only that
$c \mid 12$ for $c < 5$ (after `interval_cases`) and the lengths and distinctness of the two
fixed 48-letter lists. <!-- src: OpenProblemsLab/SeparatingWords.lean lines 627-648 -->

### 3.5 Monotonicity in the number of states

| Lean name | line | statement | axioms |
|---|---|---|---|
| `suffStates_succ` | 654 | `SuffStates k n → SuffStates (k + 1) n` | P |
| `suffStates_mono` | 674 | `k ≤ k' → SuffStates k n → SuffStates k' n` | P |
| `lt_sep_of_not_suffStates` | 681 | `¬ SuffStates k n → k < sep n` | S |
| `six_le_sep_48` | 691 | `6 ≤ sep 48` | S |

<!-- src: OpenProblemsLab/SeparatingWords.lean; computations/separating_words/axioms.txt lines 70-73 -->

`suffStates_succ` embeds `Fin k` into `Fin (k + 1)` by `Fin.castSucc` and sends the new state
to itself. `six_le_sep_48` is `lt_sep_of_not_suffStates not_suffStates_five_48`, the equal-length
form of $\mathrm{Sep}(48) > 5$ in [BKSS] Proposition 14, which they derive from Theorem 8. It
implies their at-most statement, since $\mathrm{sep}(48) \le \mathrm{Sep}(48)$.

### 3.6 Stated, not proved

`logConjecture` (line 214) is the open conjecture $\exists C\ \forall n \ge 2,\
\mathrm{sep}(n) \le C \log_2 n$, as a `def`. Nothing is proved about it. <!-- src: OpenProblemsLab/SeparatingWords.lean line 214 -->

### 3.7 Not in Lean

* `SuffStates k (n + 1) → SuffStates k n` (prefix both words with one letter), equivalently
  monotonicity of `sep` in $n$ (given `suffStates_mono`). Without it $N(5) \le 47$ is not
  formal, and `not_suffStates_five_68` cannot be derived from `not_suffStates_five_48`; it is
  proved separately, from the block shift.
* $N(k)$ itself.
* `¬ SuffStates k (2L + 6(k - 1))` for general $k$. It would also need a proof that the two
  words differ for every $k$; only $k = 5$ is done.
* The corollary `6 ≤ sep 68` from `not_suffStates_five_68`. It is one line and was not added.
* Any value of `sep n` other than $n = 1$ and $n = 4$.
* A line-by-line transcription of the BKSS case split (the correspondence is in the section
  docstring and in section 3.4 above).

## 4. Computation: a certified reproduction of $\mathrm{sep}(n)$ for $n \le 30$

This section is a reproduction of published values (section 5), run outside the kernel. It
adds no new values.

### 4.1 Method

1. **End states, not accept sets.** By the reduction of section 2 the search enumerates
   transition functions only. Gate (B) below re-tests this reduction exhaustively against
   literal DFAs.
2. **Canonical transition functions.** Unreachable states are deleted and states are numbered
   in breadth-first order from start state 0, letter 0 before letter 1. Counts for
   $k = 1, \dots, 5$: 1, 12, 216, 5,248 and 160,675, against $k^{2k}$ = 1, 16, 729, 65,536 and
   9,765,625 raw functions. <!-- src: computations/separating_words/run30.log lines 2-6 -->
   Gate (A) checks the list against brute-force canonicalization of all raw functions for
   $k \le 4$ only. <!-- src: computations/separating_words/verify.log line 93 -->
3. **Signatures.** For a set $S$ of transition functions, $\mathrm{sig}_S(w) =
   (\delta^*(0,w))_{\delta \in S}$. The signatures of all $2^{t+1}$ words of length $t+1$ are
   one array gather away from those of length $t$. *Upper bound:* if $\mathrm{sig}_S$ is
   injective on $\{0,1\}^n$ for some set $S$ of $k$-state functions, then $\mathrm{sep}(n) \le
   k$, and $S$ is a certificate that can be re-checked without the search. *Lower bound:* grow
   $S$ until the collision groups are small, then run every canonical function on the surviving
   words; a group that no function splits is unseparable.
4. **Interpolation** uses $\mathrm{sep}(n+1) \ge \mathrm{sep}(n)$ (section 1; not in Lean).

Commands, from `computations/separating_words`: <!-- src: computations/separating_words/RESULTS.md "What was run"; --seed 7 from computations/separating_words/seed_probe_n22.log (seed 7 reproduces the run30.log certificate sizes 45, 47, 49, 52, 55 at n = 18..22; the default seed gives 44, 46, 49, 51, 54) -->

```
python separate.py --nmax 30 --kmax 5 --seed 7 --save-cert cert_k5_n30.npy
python separate.py --check-cert cert_k5_n30.npy --nmax 30
python separate.py --verify --deep --negative-control --nmax 18 --kmax 5
```

Machine: AMD Ryzen 7 7840HS, 27.8 GiB RAM, Windows 11, CPython 3.14.3, numpy 2.5.0, one
thread. <!-- src: computations/separating_words/RESULTS.md lines 105-112 -->
Peak memory is about 9 GiB at $n = 30$ and doubles with each further $n$. <!-- src: computations/separating_words/RESULTS.md lines 114-116 -->

### 4.2 Values

Output of the first command, `run30.log`:

$$\mathrm{sep}(1..30) = 2, 2, 2, 3, 3, 3, 3, 3, 3, 4, 4, 4, 4, 4, 4, 4, 4, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5.$$
<!-- src: computations/separating_words/run30.log line 110 -->

$N(1) = 0$, $N(2) = 3$, $N(3) = 9$ and $N(4) = 17$ are exact. $N(1) = 0$ because one state
separates nothing. For $k = 2, 3, 4$, at $n = 4$, $10$ and $18$ respectively, every canonical
function on at most $k$ states was run on the surviving words, and none separates the pairs
`0110 / 1010`, `1100000000 / 1111111100` and `111000000000000000 / 111111111111111000`. <!-- src: computations/separating_words/run30.log lines 8-9, 13-14, 24-25, 43-44; the exhaustive final step is described in computations/separating_words/RESULTS.md lines 142-145 and 331-338 -->
For $k = 5$ the search stopped at $n = 30$ because of memory, not because it found a hard pair:
it reports $N(5) \ge 30$ after 639.3 s, with a certificate of 74 five-state transition
functions saved as `cert_k5_n30.npy`. Total wall time 640.4 s. <!-- src: computations/separating_words/run30.log lines 75, 77, 111 -->

### 4.3 Certificate re-check

The second command re-reads `cert_k5_n30.npy` and checks that the signatures of all
1,073,741,824 words of length 30 are distinct, which gives $\mathrm{sep}(30) \le 5$; it
reported `VERIFIED` in 276.2 s. <!-- src: computations/separating_words/RESULTS.md lines 90-93 -->
Appending a common suffix preserves equal end states, so the same certificate gives
$\mathrm{sep}(n) \le 5$ for every $n \le 30$. **Caveat:** that run's output is recorded only
inside `RESULTS.md`; no log file of it is in the repository. The certificate file is. The
re-check must be regenerated as a log before this note cites it as an artefact. <!-- src: computations/separating_words/PREPRINT-OUTLINE.md section 3b (C5) and section 8 item 3 -->

### 4.4 Validation gates and negative controls

Output of the third command, `verify.log`:

* (A) canonical enumeration equals brute-force canonicalization for $k \le 4$. <!-- src: computations/separating_words/verify.log line 93 -->
* (B) accept-set reduction, tested on every pair of words of length $n \le 8$ against every
  literal DFA (transition function, start state and accept set) on 4 states: at $n = 8$,
  32,640 pairs against 4,194,304 literal DFAs. <!-- src: computations/separating_words/verify.log line 110 -->
* (C, D) fast and literal computations agree on random pairs, and on $\mathrm{sep}(n)$ for
  $n \le 7$.
* (E) the hard pair at $n = 18$ re-derived from the literal definition by enumerating
  1,566,711,930 DFAs on at most 5 states. <!-- src: computations/separating_words/verify.log line 119 -->
* (F) structural checks, including monotonicity over the computed range.
* `all gates: PASS`, then four negative controls (a flipped transition, deleted separating
  functions, an understated $\min k$, a false $\mathrm{sep}(4) \le 2$), each caught:
  `negative controls: PASS`. <!-- src: computations/separating_words/verify.log lines 126-142 -->

### 4.5 A numerical check of [BKSS] Theorem 8 at $k = 5$

`python bkss_identity.py` (log `bkss_identity.log`), independent of both the BKSS proof and
the Lean proof: <!-- src: computations/separating_words/bkss_identity.log -->

* 0 of 166,152 canonical transition functions on at most 5 states separate the length-48
  pair;
* 0 of 1,000,000 random raw (function, start state) pairs on 5 states separate it, which does
  not depend on the canonical enumeration (gate (A) covers only $k \le 4$);
* controls: with $L = 11$ (length 46), 56,382 functions on at most 5 states separate; 199 of
  200,000 random 6-state functions separate the length-48 pair; the $n = 18$ block-shift pair
  has 0 separators on at most 4 states and 9,738 on at most 5.

This is a sanity check. The proof is the Lean theorem of section 3.4.

### 4.6 Comparison with the literature

The first 18 terms of section 4.2 equal the $D_\exists$ row of [Tran] Table 1 term by term. <!-- src: computations/separating_words/RESULTS.md lines 488-493; computations/separating_words/run30.log line 110 -->
Terms 19 to 30 follow from [BKSS] Proposition 14 with $\mathrm{sep}(18) = 5$ and monotonicity. <!-- src: computations/separating_words/RESULTS.md lines 10-13 -->
So section 4 reproduces, in the equal-length convention and with a saved certificate, values
that were already in print or implied by print.

## 5. What is not new

* **The mathematics of every formalized statement.** Accept-set elimination: [Tran], and
  the definition of separation that precedes [BKSS] Fact 1. The $n + 2$ bound: [DESW] Proposition 4. $\mathrm{sep}(1) = 2$,
  $\mathrm{sep}(4) = 3$: [Tran] Table 1. The block shift: [DESW] Theorem 1 and [BKSS]
  Proposition 5. The length-48 identity and $\mathrm{sep}(48) \ge 6$: [BKSS] Theorem 8 and
  Proposition 14. The Lean proof of Theorem 8 uses the BKSS arguments.
* **Several formal results.** Nicol's Lean repository [Nicol-Lean], committed 2026-08-31,
  already proves the unary lcm identity for DFAs, monotonicity of separability in the state
  bound, and a separating-words lower bound, all before this repository's block-shift commit of
  2026-09-04 (section 6). <!-- src: computations/separating_words/PREPRINT-OUTLINE.md sections 6b and 6c -->
* **All computed values.** $\mathrm{sep}(n)$ for $n \le 18$ is [Tran]; $n = 19$ to $30$ is
  implied by [BKSS] Proposition 14. Exactness of $\mathrm{lcm}(1,\dots,k) + 2k - 2$ for
  $k \le 4$, that is $N(1..4) = 0, 3, 9, 17$, is [BKSS] Remark 7, and also follows from [Tran]
  Table 1 with [DESW] Theorem 1. The bounds $40 \le N(5) \le 47$ are [BKSS]. The observation
  that $\operatorname{round}(\sqrt{n+3})$ matches $\mathrm{sep}(n)$ up to $n = 27$ and fails at
  $n = 28$ is implied by [BKSS] Proposition 14. <!-- src: computations/separating_words/RESULTS.md lines 151-161 and 540-556 -->
* **The extremal-pair census** at $n = 10$ and $n = 18$ consists of [BKSS] identities (3) and
  (4). The complete lists (8, 4 and 4 pairs at $n = 4, 10, 18$) are computed, not claimed as
  new. <!-- src: computations/separating_words/census.log (python separate.py --kmax 2 --census 4; --kmax 3 --census 10; --kmax 4 --census 18) -->
* **A retracted conjecture.** On 2026-09-04 (commit `cbb5ed5`) this project published, in its
  public repository, the conjecture $N(k) = 2k - 3 + \operatorname{lcm}(1,\dots,k)$, so
  $N(5) = 67$, and called exactness of that formula for $k \le 4$ new. Both were wrong in the
  same way: [BKSS] had published the refutation in 2017. Their Theorem 8 gives $N(5) \le 47$,
  and their Remark 7 records the exactness for $k \le 4$. The conjecture was retracted on
  2026-09-13 in commits `b8322c6` and `2cbb438`; the original text is kept in `RESULTS.md`
  under a retraction notice. **As of this draft the retraction is local only:** the public
  `main` is `582601d`, which contains `cbb5ed5` but neither retraction commit, so the public
  repository still shows the false conjecture. The evidence offered for it was that two-block and three-block
  word families first collide at $n = 68$. That measured only those families: the collisions
  are [BKSS] identities (3) and (4), and the length-48 identity lies in neither family. <!-- src: computations/separating_words/RESULTS.md lines 622-667 and 714; git log of commits cbb5ed5, b8322c6, 2cbb438; public main from `git ls-remote origin refs/heads/main` and `git merge-base --is-ancestor <commit> origin/main`, run 2026-09-13 -->

## 6. Related work and the scope of novelty

**Nicol's Lean formalization.** [Nicol-Lean] (Lean 4, single commit `a4f77cb`) is the Lean
companion of [Nicol]; its README describes it as a formalization of that paper's Theorems 6
and 7. We cloned it and read the statements below; we did not build it (it has no lakefile or
toolchain file and uses `Nat.lcmUpto`, which our Mathlib revision lacks). <!-- src: computations/separating_words/PREPRINT-OUTLINE.md section 6b -->

* `dfa_evalFrom_zero_add_lcmUpto`: for `D : DFA Bool σ` with `Fintype.card σ ≤ stateBound` and
  `stateBound ≤ base`, reading `base + Nat.lcmUpto stateBound` zeros ends where `base` zeros
  do. This is the unary identity of $T_k$ in DFA form, for exponents at least $k$. [BKSS]
  identity (1), $x^{k-1} = x^{k-1+\operatorname{lcm}(1,\dots,k)}$, is the exponent $k - 1$ case,
  and Nicol's statement follows from it by multiplying both sides by a power of $x$. Our
  `iterate_eq_add_of_card_le` needs only $k \le a + 1$, so it contains identity (1) itself, but
  the unary fact was formal first in [Nicol-Lean].
* `HasSeparatorOfSize.mono`: separability by at most $k$ states implies separability by at most
  $l \ge k$. Our `suffStates_mono` is the analogue for state sets of exactly `Fin k`.
* `reversalTheorem7`: there are $c_0 > 0$ and $K$ such that for every $N \ge 2$ and every
  $L \ge N^{c_0 N}$ there are distinct binary words $x, y$ of length $L$ with
  `¬HasSeparatorOfSize N x y` whose reversals are separated with $K \lceil \log_2(N+2) \rceil$
  states. This is a formal separating-words lower bound, weaker than $\Omega(\log n)$. By
  accept-set elimination its pairs are two-letter identities of $T_N$, stated in separation
  form.
* Also `eval_common_lcm_power_eq` (if two words each permute a DFA's transition image after a
  common prefix `base`, their `Nat.lcmUpto N`-th powers after `base` reach the same state) and
  `noNFASeparatorOfSize_asymmetry_fst` (no NFA with at most `bound` states separates
  $0^{\mathit{bound}}\,1\,0^{\mathit{tail}+\mathit{period}}$ from
  $0^{\mathit{bound}+\mathit{period}}\,1\,0^{\mathit{tail}}$, under a hypothesis quantified over
  every such NFA; the words have the shape of [BKSS] identity (4), but the statement is about
  NFAs and conditional, so we do not count it as a formalization of that identity).

According to the search log, the repository has no BKSS citation and no identity of the
$(xy)^a(yx)^b$ shape, and the arXiv HTML of [Nicol] does not mention Lean or the repository
(the paper cites BKSS once, for the link between lower bounds and identities). For this review,
`grep -rniE 'Bulatov|BKSS|Karpova|Shur|Startsev|semigroup' --include=*.lean` on a fresh clone at
`a4f77cb` returned no matches. <!-- src: computations/separating_words/PREPRINT-OUTLINE.md section 6b -->

**Other formal work.** Mathlib has the monoid of endofunctions (`Function.End`) and periodic
point lemmas such as `minimalPeriod_le_card`, but no identities of $T_n$ and no word
separation, according to the search log. <!-- src: computations/separating_words/PREPRINT-OUTLINE.md section 6b, Local Mathlib -->

**Scope of the novelty statement.** This is the only novelty statement in the note, and it is
a report on searches, not a priority claim:

> In the places searched on 2026-09-13 and listed in `PREPRINT-OUTLINE.md` sections 6b and 6c
> (GitHub code and repository search; cloned Lean automata and semigroup repositories; the
> local Mathlib `d77ef0741c` and mathlib4 master `Mathlib/Computability`; cslib;
> formal-conjectures; the Lean Zulip public archive to 2026-08-25; Isabelle AFP entry names,
> eight AFP abstracts and mirror code search; Rocq opam package names; lists of papers citing
> BKSS; arXiv site search and the full text of five recent papers; OpenAlex full-text filters;
> web searches), we found no formalization outside this repository of [BKSS] Theorem 8 (their
> identity (5)), of any identity of the shape $(xy)^a(yx)^b(xy)^c$, or of a length-48 pair of
> binary words that no 5-state DFA separates.

The statement is deliberately narrower than "no earlier formal BKSS identity". [BKSS] number
the unary identity (1) and the block-shift identity (3), and both were formal before Theorem 8
was added: in this repository (`iterate_eq_add_of_card_le` at $a = k - 1$ and
`not_separates_block_shift`, commit `a9d82fb`, 2026-09-04) and, for the unary identity with
exponents at least $k$, in [Nicol-Lean] (2026-08-31).

<!-- src: computations/separating_words/PREPRINT-OUTLINE.md sections 6b ("What these searches support"), 6c, and section 8 item 1 -->

Limits of those searches, also from the log: GitHub code search did not index either known Lean
separating-words repository, so its zeros are weak; AFP and Rocq packages were checked by name
(plus eight AFP abstracts); the arXiv API and Semantic Scholar keyword search returned HTTP 429
and dblp served a bot check; the Zulip archive covers public streams only. We do **not** claim
a first formal BKSS identity in general, a first formal two-letter identity of $T_k$ ([Nicol-Lean] has one in separation form, and
this repository's `not_separates_block_shift` is another), a first formal unary lcm identity,
or a first formal separating-words result of any kind.

## 7. Open

* **$N(5)$.** In the equal-length convention $40 \le N(5) \le 47$: the lower bound is [BKSS]
  Proposition 14, the upper bound is [BKSS] Theorem 8 with monotonicity. Equivalently, it is
  open whether $\mathrm{sep}(n) = 5$ for $41 \le n \le 47$. "Open" here means that the searches
  logged in `PREPRINT-OUTLINE.md` section 6 found no paper settling [BKSS] Conjecture 10 or
  computing $N(5)$. <!-- src: computations/separating_words/RESULTS.md lines 144-147; computations/separating_words/PREPRINT-OUTLINE.md section 8 item 6 -->
* **[BKSS] Conjecture 10:** identity (5) at $k = 5$, of length 48, is the shortest identity of
  $T_5$. It would give $N(5) = 47$: a pair of distinct words of equal length at most 47 that no
  5-state DFA separates would be a shorter identity. BKSS report a search, built from the short
  positive identities of $S_5$ they list, that found exactly this one identity of $T_5$; that
  supports the conjecture but does not prove it. <!-- src: computations/separating_words/PREPRINT-OUTLINE.md section 0 -->
* **Out of reach for the method of section 4.** $n = 31$ would need about 17 GiB, and each
  further $n$ doubles time and memory, so $n = 41$ is far past this machine. <!-- src: computations/separating_words/RESULTS.md lines 260-262 -->
* **Formal gaps** listed in section 3.7, first among them antitonicity of `SuffStates` in $n$,
  which would make $N(5) \le 47$ formal once $N$ is defined.
* **Artefact gaps.** Regenerate the certificate re-check as a log file.
  `CsanyiDavid/separating_words` (C++, 2023), which turned up in the search as possible prior
  computation of small $S(n)$, was checked: an automaton generator and a test, an empty
  `main`, and no published values. <!-- src: computations/separating_words/PREPRINT-OUTLINE.md section 6c and section 8 item 3 -->

## References

Each entry says what was opened or read for this draft.

* **[BKSS]** A. A. Bulatov, O. Karpova, A. M. Shur, K. Startsev. Lower bounds on words
  separation: are there short identities in transformation semigroups? *Electron. J. Combin.*
  24(3) (2017), #P3.35. doi:10.37236/6450. arXiv:1609.03199. [Read: arXiv source
  `ShortIdentities.tex`, Facts 1 to 3, Propositions 4 to 6 and 14, Remark 7, Theorem 8 with its
  proof, Conjecture 10, and the section 3 search remark; Crossref record for the journal
  metadata. Review re-check: arXiv lists only v1 (11 Sep 2016); the E-JC PDF text of Remark 7,
  Theorem 8 with its proof, Conjecture 10, Proposition 14 with its proof and the $T_5$ search
  remark agrees with that source, with the same numbering of results and of identities (1) to
  (5).]
* **[Chase]** Z. Chase. Separating words and trace reconstruction. *STOC 2021*, 21-31.
  doi:10.1145/3406325.3451118. arXiv:2007.12097v3, titled there "A new upper bound for
  separating words". [Read: arXiv v3 PDF text of Theorem 1 and its reference [3]; Crossref
  record for the STOC title and pages. The STOC version was not read.]
* **[DESW]** E. D. Demaine, S. Eisenstat, J. Shallit, D. A. Wilson. Remarks on separating
  words. *DCFS 2011*, Lecture Notes in Computer Science, 147-157.
  doi:10.1007/978-3-642-22600-7_12. arXiv:1103.4513v1. [Read: arXiv v1 PDF text of
  Propositions 1 and 4 and Theorem 1; Crossref record. The LNCS version was not read.]
* **[GK]** P. Goralčík, V. Koubek. On discerning words by automata. *ICALP 1986*, Lecture Notes
  in Computer Science 226, 116-122. doi:10.1007/3-540-16761-7_61. [Crossref record opened
  (title, authors, pages 116-122); the volume number 226 is taken from [Chase]'s reference [3];
  the paper was not read. Cited only for the origin of the problem and the logarithmic lower bound,
  as [Chase] and [BKSS] cite it.]
* **[Nicol]** J. Nicol. Further remarks on separating words. arXiv:2608.30928v1 (2026). [arXiv
  abstract page opened for this draft; the full-text check for mentions of Lean is in
  `PREPRINT-OUTLINE.md` section 6b.]
* **[Nicol-Lean]** J. Nicol. FurtherRemarks: Lean formalization of Theorems 6 and 7.
  github.com/jn1z/FurtherRemarks, commit `a4f77cb`. [Cloned; README and the statements of
  `dfa_evalFrom_zero_add_lcmUpto`, `HasSeparatorOfSize.mono` and `reversalTheorem7` read, and
  the other two named theorems located; not built.]
* **[Tran]** N. Tran. Separating words from every start state with Horner automata. *AFL 2023*,
  EPTCS 386, 243-252. doi:10.4204/EPTCS.386.19. arXiv:2309.02766. [Read: PDF text of the
  introduction and Table 1; Crossref record.]
* **[Xu]** C. Xu. An elementary proof of the $\tilde O(n^{1/3})$ bound for separating words.
  arXiv:2609.08191v1 (2026). [arXiv abstract page opened; unrefereed, not used.]
