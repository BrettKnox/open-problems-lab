import Mathlib.Computability.DFA
import Mathlib.Order.Lattice.Nat
import Mathlib.Data.Nat.Log
import Mathlib.Data.Fintype.Pi
import Mathlib.Combinatorics.Pigeonhole
import Mathlib.Tactic.IntervalCases

/-!
# The separating words problem

`sep n` is the least number of DFA states sufficient to distinguish any two
distinct binary words of length `n` (some DFA of that size accepts one and
rejects the other). Known: `sep n = Ω(log n)` (Goralčík and Koubek, ICALP
1986) and `sep n = O(n^{1/3} log^7 n)` (Chase, STOC 2021). The conjecture is
that `O(log n)` states suffice.

Status 2026-08-19: OPEN. A claimed `O(log² n)` improvement (arXiv:2503.23184)
was withdrawn in April 2025. Quiet since Chase. Not in formal-conjectures.

Exact small values are in print (added 2026-09-13): Tran (AFL 2023, Table 1)
for `n ≤ 18`, and Bulatov, Karpova, Shur and Startsev (Electron. J. Combin.
24(3) (2017) #P3.35, arXiv:1609.03199), whose Proposition 14 gives `sep n ≤ 5`
for `n ≤ 40` and whose Theorem 8 gives `sep 48 ≥ 6`.

## What is proved here

* `exists_separates_iff_exists_eval_ne` — **the accept set is irrelevant**: a
  `k`-state DFA separating `u` from `v` exists exactly when some `k`-state
  transition function sends them to *different states*. (Given that, accept
  exactly the state `u` lands in.) This collapses the search space, and is what
  makes the exhaustive computation in `computations/separating_words` feasible:
  one enumerates transition functions, never accept sets.
* `sep_le` — `sep n ≤ n + 2`, via a counter that latches on the symbol at the
  first position where the words differ. Weak as a bound, but it is what makes
  `sep` *well defined*: without it the infimum is over an empty set and `sep n`
  would silently be the junk value `0`.
* `two_le_sep` — `2 ≤ sep n` for `n ≥ 1`: one state cannot tell anything apart.
* `not_separates_bkss`, `not_suffStates_five_48` (added 2026-09-13): Theorem 8
  of Bulatov, Karpova, Shur and Startsev, whose mathematics this transcribes:
  no `k`-state DFA separates `(01)^(k-2+L) (10)^k (01)^(k-1)` from
  `(01)^(k-2) (10)^k (01)^(k-1+L)` when every `c < k` divides `L`. At `k = 5`,
  `L = 12` these are distinct words of length 48, so 5 states do not suffice.
* `suffStates_succ`, `suffStates_mono`, `lt_sep_of_not_suffStates` and
  `six_le_sep_48` (added 2026-09-13): `SuffStates` is monotone in the number of
  states, so a failure at `k` states gives `k < sep n`; in particular
  `6 ≤ sep 48`.

Attack lanes: exact values of `sep n` for small `n` by exhaustive/SAT search;
improved constructions for special word classes.
-/

namespace OpenProblems.SeparatingWords

/-- `M` separates `u` and `v` iff it accepts exactly one of them. -/
def Separates {σ : Type} (M : DFA (Fin 2) σ) (u v : List (Fin 2)) : Prop :=
  ¬(u ∈ M.accepts ↔ v ∈ M.accepts)

/-- `k` states suffice for length `n`: every pair of distinct binary words of
length `n` is separated by some DFA with state set `Fin k`. -/
def SuffStates (k n : ℕ) : Prop :=
  ∀ u v : List (Fin 2), u.length = n → v.length = n → u ≠ v →
    ∃ M : DFA (Fin 2) (Fin k), Separates M u v

/-- The separation number `sep n`: the least `k` such that `k` states suffice
to separate any two distinct binary words of length `n`. -/
noncomputable def sep (n : ℕ) : ℕ := sInf {k | SuffStates k n}

/-! ### The accept set is irrelevant -/

/-- Separation forces the two runs to end in different states. -/
theorem eval_ne_of_separates {σ : Type} {M : DFA (Fin 2) σ} {u v : List (Fin 2)}
    (h : Separates M u v) : M.eval u ≠ M.eval v := by
  intro hEq
  exact h (by simp only [DFA.mem_accepts, hEq])

/-- **The reduction**: a separating `k`-state DFA exists iff some `k`-state
transition function sends `u` and `v` to different states. The accept set costs
nothing — take exactly the state `u` lands in. -/
theorem exists_separates_iff_exists_eval_ne {k : ℕ} (u v : List (Fin 2)) :
    (∃ M : DFA (Fin 2) (Fin k), Separates M u v) ↔
      (∃ M : DFA (Fin 2) (Fin k), M.eval u ≠ M.eval v) := by
  constructor
  · rintro ⟨M, hM⟩
    exact ⟨M, eval_ne_of_separates hM⟩
  · rintro ⟨M, hM⟩
    refine ⟨⟨M.step, M.start, {M.eval u}⟩, ?_⟩
    intro h
    exact hM (h.mp rfl).symm

/-! ### `sep` is well defined: `sep n ≤ n + 2` -/

/-- Counter-and-latch automaton for position `i`: it counts positions up to
`n`, and jumps to an absorbing state the moment it reads a `1` at position `i`.
Its final state therefore records the symbol at position `i`. -/
def posDFA (n i : ℕ) : DFA (Fin 2) (Fin (n + 2)) where
  step q a :=
    if q.val = i ∧ a = 1 then ⟨n + 1, by omega⟩
    else if h : n ≤ q.val then q
    else ⟨q.val + 1, by omega⟩
  start := ⟨0, by omega⟩
  accept := ∅

/-- The state reached after a prefix: the latch state `n + 1` if the prefix has
already passed position `i` carrying a `1` there, and otherwise the position
count. -/
theorem posDFA_evalFrom_val (n i : ℕ) (hi : i < n) :
    ∀ p : List (Fin 2), p.length ≤ n →
      ((posDFA n i).evalFrom (posDFA n i).start p).val =
        if p[i]? = some 1 then n + 1 else p.length := by
  intro p
  induction p using List.reverseRecOn with
  | nil => intro _; simp [posDFA]
  | append_singleton x a ih =>
    intro hp
    simp only [List.length_append, List.length_cons, List.length_nil] at hp
    have hx : x.length ≤ n := by omega
    have hxn : x.length < n := by omega
    rw [DFA.evalFrom_append_singleton]
    set q := (posDFA n i).evalFrom (posDFA n i).start x with hqdef
    have ihx := ih hx
    by_cases hxi : x[i]? = some 1
    · -- already latched: the absorbing state stays put
      have hlt : i < x.length := (List.getElem?_eq_some_iff.mp hxi).1
      rw [ite_eq_left hxi] at ihx
      have hstep : ((posDFA n i).step q a).val = n + 1 := by
        simp only [posDFA]
        rw [ite_eq_right fun hc => absurd hc.1 (by omega), dite_eq_left (by omega)]
        exact ihx
      rw [hstep, List.getElem?_append_left hlt, ite_eq_left hxi]
    · rw [ite_eq_right hxi] at ihx
      by_cases hli : x.length = i
      · -- reading position `i` right now
        rw [List.getElem?_append_right (by omega), hli]
        simp only [Nat.sub_self, List.getElem?_cons_zero, List.length_append,
          List.length_cons, List.length_nil]
        by_cases ha : a = 1
        · have hstep : ((posDFA n i).step q a).val = n + 1 := by
            simp only [posDFA]
            rw [ite_eq_left ⟨by omega, ha⟩]
          rw [hstep, ha, ite_eq_left rfl]
        · have hstep : ((posDFA n i).step q a).val = x.length + 1 := by
            simp only [posDFA]
            rw [ite_eq_right fun hc => ha hc.2, dite_eq_right (by omega)]
            simp only [ihx]
          rw [hstep, ite_eq_right (by simpa using ha)]
      · -- some other position: just count
        have hnone : (x ++ [a])[i]? ≠ some 1 := by
          rcases Nat.lt_or_ge i x.length with h | h
          · rwa [List.getElem?_append_left h]
          · rw [List.getElem?_eq_none (by simp; omega)]
            simp
        have hstep : ((posDFA n i).step q a).val = x.length + 1 := by
          simp only [posDFA]
          rw [ite_eq_right fun hc => hli (by omega), dite_eq_right (by omega)]
          simp only [ihx]
        rw [hstep, ite_eq_right hnone]
        simp

/-- Two distinct words of the same length land in different states of `posDFA`
at their first difference. -/
theorem suffStates_add_two (n : ℕ) : SuffStates (n + 2) n := by
  intro u v hu hv huv
  rw [exists_separates_iff_exists_eval_ne]
  -- pick a position where they differ
  obtain ⟨i, hi, hne⟩ : ∃ i, i < n ∧ u[i]? ≠ v[i]? := by
    by_contra hall
    push Not at hall
    exact huv (List.ext_getElem? fun i => by
      rcases Nat.lt_or_ge i n with h | h
      · exact hall i h
      · rw [List.getElem?_eq_none (by omega), List.getElem?_eq_none (by omega)])
  refine ⟨posDFA n i, ?_⟩
  have hui : i < u.length := by omega
  have hvi : i < v.length := by omega
  have hu' := posDFA_evalFrom_val n i hi u (by omega)
  have hv' := posDFA_evalFrom_val n i hi v (by omega)
  rw [List.getElem?_eq_getElem hui] at hne hu'
  rw [List.getElem?_eq_getElem hvi] at hne hv'
  intro hEq
  have hEq' : (posDFA n i).evalFrom (posDFA n i).start u
      = (posDFA n i).evalFrom (posDFA n i).start v := hEq
  rw [hEq', hv', hu, hv] at hu'
  -- both words have length `n`, so only the latch can differ, and it does
  have hfin : ∀ x : Fin 2, x = 0 ∨ x = 1 := by decide
  rcases hfin (u[i]'hui) with h1 | h1 <;> rcases hfin (v[i]'hvi) with h2 | h2 <;>
    rw [h1, h2] at hu' hne <;> simp at hu' hne

/-- `sep n ≤ n + 2`; in particular the infimum defining `sep` is not over an
empty set, so `sep` means what it should. -/
theorem sep_le (n : ℕ) : sep n ≤ n + 2 := Nat.sInf_le (suffStates_add_two n)

/-- One state separates nothing, so `2 ≤ sep n` once there is anything to
separate. -/
theorem two_le_sep {n : ℕ} (hn : 1 ≤ n) : 2 ≤ sep n := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  have hmem0 : sep (m + 1) ∈ {k | SuffStates k (m + 1)} :=
    Nat.sInf_mem ⟨m + 3, suffStates_add_two (m + 1)⟩
  have hmem : SuffStates (sep (m + 1)) (m + 1) := hmem0
  have hpair := hmem (0 :: List.replicate m 0) (1 :: List.replicate m 0)
    (by simp) (by simp) (by simp)
  by_contra hlt
  push Not at hlt
  have hcases : sep (m + 1) = 0 ∨ sep (m + 1) = 1 := by omega
  rcases hcases with h0 | h1
  · rw [h0] at hpair
    obtain ⟨M, _⟩ := hpair
    exact M.start.elim0
  · rw [h1] at hpair
    obtain ⟨M, hM⟩ := hpair
    exact eval_ne_of_separates hM (Subsingleton.elim _ _)

/-- **Open conjecture**: `O(log n)` states suffice, i.e.
`∃ C, sep n ≤ C · log₂ n` for all `n ≥ 2`. -/
def logConjecture : Prop :=
  ∃ C : ℕ, ∀ n : ℕ, 2 ≤ n → sep n ≤ C * Nat.log 2 n

/-! ### Exact values: `sep 1 = 2` and `sep 4 = 3`

The first jump of the separating-words function, formally verified — the
computational table in `computations/separating_words` starts from these.
Everything here is kernel-checked (`decide`), no `native_decide`. -/

/-- Second reduction: a `k`-state DFA with differing end states exists iff a
bare transition function and start state do — the `accept` field (a `Set`,
not decidable) plays no role in evaluation. -/
theorem exists_eval_ne_iff_exists_step {k : ℕ} (u v : List (Fin 2)) :
    (∃ M : DFA (Fin 2) (Fin k), M.eval u ≠ M.eval v) ↔
      ∃ (δ : Fin k → Fin 2 → Fin k) (s : Fin k), u.foldl δ s ≠ v.foldl δ s := by
  constructor
  · rintro ⟨M, hM⟩
    exact ⟨M.step, M.start, hM⟩
  · rintro ⟨δ, s, h⟩
    exact ⟨⟨δ, s, ∅⟩, h⟩

/-- Kernel-checked core for the upper bound at `n = 4`: any two distinct
4-tuples over `Fin 2` are separated by some 3-state transition function. -/
private theorem core_upper_4 : ∀ a b c d a' b' c' d' : Fin 2,
    ([a, b, c, d] : List (Fin 2)) ≠ [a', b', c', d'] →
      ∃ (δ : Fin 3 → Fin 2 → Fin 3) (s : Fin 3),
        ([a, b, c, d] : List (Fin 2)).foldl δ s ≠ [a', b', c', d'].foldl δ s := by
  decide

/-- Kernel-checked core for the lower bound at `n = 4`: no 2-state transition
function separates `0110` from `1010`. -/
private theorem core_lower_4 : ∀ (δ : Fin 2 → Fin 2 → Fin 2) (s : Fin 2),
    ([0, 1, 1, 0] : List (Fin 2)).foldl δ s = [1, 0, 1, 0].foldl δ s := by
  decide

theorem suffStates_three_four : SuffStates 3 4 := by
  intro u v hu hv huv
  rw [exists_separates_iff_exists_eval_ne, exists_eval_ne_iff_exists_step]
  match u, hu with
  | [a, b, c, d], _ =>
    match v, hv with
    | [a', b', c', d'], _ => exact core_upper_4 a b c d a' b' c' d' huv

theorem not_suffStates_two_four : ¬ SuffStates 2 4 := by
  intro h
  obtain ⟨M, hM⟩ := h [0, 1, 1, 0] [1, 0, 1, 0] rfl rfl (by decide)
  exact eval_ne_of_separates hM (core_lower_4 M.step M.start)

/-- **`sep 1 = 2`**: one state distinguishes nothing; two suffice for single
symbols. -/
theorem sep_one : sep 1 = 2 := by
  refine le_antisymm ?_ (two_le_sep (by omega))
  refine Nat.sInf_le ?_
  intro u v hu hv huv
  rw [exists_separates_iff_exists_eval_ne, exists_eval_ne_iff_exists_step]
  match u, hu with
  | [a], _ =>
    match v, hv with
    | [a'], _ =>
      refine ⟨fun _ x => x, 0, ?_⟩
      simpa using fun h => huv (by rw [h])

/-- **`sep 4 = 3`** — the first jump of the separating-words function,
kernel-verified: three states always suffice at length 4, and `0110` vs
`1010` defeats every two-state automaton. -/
theorem sep_four : sep 4 = 3 := by
  refine le_antisymm (Nat.sInf_le suffStates_three_four) ?_
  refine le_csInf ⟨6, suffStates_add_two 4⟩ ?_
  rintro k hk
  by_contra hlt
  push Not at hlt
  have hcases : k = 0 ∨ k = 1 ∨ k = 2 := by omega
  rcases hcases with rfl | rfl | rfl
  · obtain ⟨M, -⟩ := hk [0, 1, 1, 0] [1, 0, 1, 0] rfl rfl (by decide)
    exact M.start.elim0
  · obtain ⟨M, hM⟩ := hk [0, 1, 1, 0] [1, 0, 1, 0] rfl rfl (by decide)
    exact eval_ne_of_separates hM (Subsingleton.elim _ _)
  · exact not_suffStates_two_four hk

/-! ### The block-shift obstruction (Demaine-Eisenstat-Shallit-Wilson)

The equal-length `Ω(log n)` lower bound rests on one observation: a `k`-state
automaton cannot see a block whose length changes by `lcm(1, ..., k)`.
Iterating any endofunction of a `k`-element type is eventually periodic with
preperiod `≤ k - 1` and period `≤ k`, so once a run is `k - 1` letters into a
block, the block's length matters only modulo that period.

`iterate_eq_add_of_card_le` is that fact, and `not_separates_block_shift` is
Theorem 1 of Demaine, Eisenstat, Shallit and Wilson
([arXiv:1103.4513](https://arxiv.org/abs/1103.4513), 2011), which follows from
it. It gives `N(k) ≤ 2k - 3 + lcm(1, ..., k)`, where `N(k)` is the largest `n`
with `SuffStates k n`.

**Correction, 2026-09-13.** This docstring used to say the bound is exact
wherever exhaustive search reaches and record the conjecture
`N(k) = 2k - 3 + lcm(1, ..., k)`. That conjecture is false. Bulatov, Karpova,
Shur and Startsev (Electron. J. Combin. 24(3) (2017) #P3.35, doi:10.37236/6450,
[arXiv:1609.03199](https://arxiv.org/abs/1609.03199)), Theorem 8, give an
identity of `T_k` of length `2 lcm(1, ..., k-1) + 6(k-1)`: at `k = 5`, two
distinct words of length 48 that no 5-state DFA separates, so `N(5) ≤ 47`, not
67. Their Remark 7 already records that the `lcm(1, ..., k) + 2k - 2`
identities are the shortest for `k ≤ 4`. The theorems below are still true;
the bound they give is not tight at `k = 5`. -/

open Function in
/-- If two iterates of `f` agree at `x`, the orbit of `x` is periodic from
there on, with period dividing any common multiple `L` of `1, ..., k`. -/
private theorem block_shift_aux {α : Type*} {k : ℕ} (f : α → α) (x : α)
    {i j a L : ℕ} (hlt : i < j) (hjk : j ≤ k) (heq : f^[i] x = f^[j] x)
    (ha : k ≤ a + 1) (hL : ∀ c, 0 < c → c ≤ k → c ∣ L) :
    f^[a] x = f^[a + L] x := by
  set c := j - i with hc
  have hc0 : 0 < c := by omega
  have hck : c ≤ k := by omega
  have hia : i ≤ a := by omega
  -- one period step, from any point at or past the preperiod
  have step : ∀ m, i ≤ m → f^[m] x = f^[m + c] x := by
    intro m hm
    have h1 : f^[m] x = f^[m - i] (f^[i] x) := by
      rw [← Function.iterate_add_apply]
      congr 1
      omega
    have h2 : f^[m - i] (f^[j] x) = f^[m + c] x := by
      rw [← Function.iterate_add_apply]
      congr 1
      omega
    rw [h1, heq, h2]
  -- hence any multiple of the period
  have steps : ∀ t m, i ≤ m → f^[m] x = f^[m + c * t] x := by
    intro t
    induction t with
    | zero => intro m _; simp
    | succ t ih =>
        intro m hm
        have := ih m hm
        have h2 := step (m + c * t) (by omega)
        rw [this, h2]
        congr 1
        ring
  obtain ⟨t, ht⟩ := hL c hc0 hck
  rw [ht]
  exact steps t a hia

open Function in
/-- Iterating an endofunction of a type with at most `k` elements is
eventually periodic, with preperiod at most `k - 1` and period at most `k`.
So if `L` is divisible by every `c` with `1 ≤ c ≤ k` — as `lcm(1, ..., k)` is —
then `f^[a] = f^[a + L]` for every `a ≥ k - 1`. -/
theorem iterate_eq_add_of_card_le {α : Type*} [Fintype α] {k : ℕ}
    (hcard : Fintype.card α ≤ k) (f : α → α) {a L : ℕ} (ha : k ≤ a + 1)
    (hL : ∀ c, 0 < c → c ≤ k → c ∣ L) : f^[a] = f^[a + L] := by
  classical
  funext x
  -- two of the k+1 iterates x, f x, ..., f^[k] x must agree
  obtain ⟨i, hi, j, hj, hij, heq⟩ :
      ∃ i ∈ Finset.range (k + 1), ∃ j ∈ Finset.range (k + 1),
        i ≠ j ∧ f^[i] x = f^[j] x := by
    refine Finset.exists_ne_map_eq_of_card_lt_of_maps_to ?_
      (fun y _ => Finset.mem_univ (f^[y] x))
    simpa using Nat.lt_succ_of_le hcard
  simp only [Finset.mem_range] at hi hj
  rcases lt_or_gt_of_ne hij with h | h
  · exact block_shift_aux f x h (by omega) heq ha hL
  · exact block_shift_aux f x h (by omega) heq.symm ha hL

/-- Reading a block of one letter is just iterating that letter's map. -/
private theorem foldl_replicate {σ : Type*} (δ : σ → Fin 2 → σ) (c : Fin 2)
    (n : ℕ) (s : σ) :
    (List.replicate n c).foldl δ s = (fun q => δ q c)^[n] s := by
  induction n generalizing s with
  | zero => rfl
  | succ n ih => rw [List.replicate_succ, List.foldl_cons, ih,
      Function.iterate_succ_apply]

open Function in
/-- **Demaine–Eisenstat–Shallit–Wilson, Theorem 1**
([arXiv:1103.4513](https://arxiv.org/abs/1103.4513)). No `k`-state transition
function separates `1^a 0^(b+L)` from `1^(a+L) 0^b` once both blocks are at
least `k - 1` long and `L` is a common multiple of `1, …, k` (so
`L = lcm(1, …, k)` qualifies). Both words have length `a + b + L`.

Neither run can see the shift: after `k - 1` letters each block's map has
entered its cycle, whose length divides `L`. -/
theorem not_separates_block_shift {k a b L : ℕ}
    (ha : k ≤ a + 1) (hb : k ≤ b + 1)
    (hL : ∀ c, 0 < c → c ≤ k → c ∣ L)
    (δ : Fin k → Fin 2 → Fin k) (s : Fin k) :
    (List.replicate a (1 : Fin 2) ++ List.replicate (b + L) 0).foldl δ s
      = (List.replicate (a + L) (1 : Fin 2) ++ List.replicate b 0).foldl δ s := by
  have hcard : Fintype.card (Fin k) ≤ k := le_of_eq (Fintype.card_fin k)
  have h1 : (fun q => δ q 1)^[a] = (fun q => δ q 1)^[a + L] :=
    iterate_eq_add_of_card_le hcard _ ha hL
  have h0 : (fun q => δ q 0)^[b] = (fun q => δ q 0)^[b + L] :=
    iterate_eq_add_of_card_le hcard _ hb hL
  rw [List.foldl_append, List.foldl_append, foldl_replicate, foldl_replicate,
    foldl_replicate, foldl_replicate, ← h1, ← h0]

/-- The bound it gives: `k` states never suffice at length `2(k-1) + L`, so
`N(k) ≤ 2k - 3 + lcm(1, …, k)`. With `L = lcm(1, …, k)` this equals
`N(1..4) = 0, 3, 9, 17` (Tran 2023, Table 1; Bulatov, Karpova, Shur and
Startsev 2017, Remark 7). It is not tight at `k = 5`: it gives `N(5) ≤ 67`,
and their Theorem 8 gives `N(5) ≤ 47`. (This docstring used to say the bound
"predicts `N(5) = 67`"; retracted 2026-09-13.) -/
theorem not_suffStates_block_shift {k L : ℕ} (hk : 1 ≤ k) (hL0 : 0 < L)
    (hL : ∀ c, 0 < c → c ≤ k → c ∣ L) :
    ¬ SuffStates k ((k - 1) + (k - 1) + L) := by
  intro h
  set a := k - 1 with ha'
  have hak : k ≤ a + 1 := by omega
  have hne : (List.replicate a (1 : Fin 2) ++ List.replicate (a + L) 0)
      ≠ List.replicate (a + L) (1 : Fin 2) ++ List.replicate a 0 := by
    intro hEq
    have := congrArg (fun l => l.count 1) hEq
    simp [List.count_append, List.count_replicate] at this
    omega
  obtain ⟨M, hM⟩ := h _ _ (by simp [List.length_append]; omega)
    (by simp [List.length_append]; omega) hne
  exact (eval_ne_of_separates hM)
    (not_separates_block_shift hak hak hL M.step M.start)

/-- **5 states do not suffice at length 68**, since `lcm(1, …, 5) = 60` and
`4 + 4 + 60 = 68`, so `N(5) ≤ 67`. True, and not tight. Bulatov, Karpova, Shur
and Startsev (Electron. J. Combin. 24(3) (2017) #P3.35, Theorem 8) give a
length-48 pair that no 5-state DFA separates, so `N(5) ≤ 47`, and their
Proposition 14 (computer-assisted) gives `N(5) ≥ 40`. Both steps this
docstring used to list as not yet in Lean are now below (2026-09-13):
`not_suffStates_five_48` is their Theorem 8 at `k = 5`, and
`lt_sep_of_not_suffStates` turns it into `six_le_sep_48`.

Retracted 2026-09-13: this docstring used to bracket `N(5)` in `[30, 67]` and
say the computations "conjecture `N(5) = 67` exactly". That conjecture is
false (BKSS Theorem 8). -/
theorem not_suffStates_five_68 : ¬ SuffStates 5 68 := by
  have h : ∀ c, 0 < c → c ≤ 5 → c ∣ 60 := by
    intro c hc h5
    interval_cases c <;> decide
  simpa using not_suffStates_block_shift (k := 5) (L := 60) (by norm_num)
    (by norm_num) h

/-! ### BKSS Theorem 8: an identity of `T_5` of length 48

The mathematics in this section is due to Bulatov, Karpova, Shur and Startsev,
*Lower bounds on words separation: are there short identities in
transformation semigroups?*, Electron. J. Combin. 24(3) (2017) #P3.35,
doi:10.37236/6450, [arXiv:1609.03199](https://arxiv.org/abs/1609.03199)
(BKSS). Their Theorem 8: the full transformation semigroup `T_k` satisfies

    (xy)^(k-2+lcm(k-1)) (yx)^k (xy)^(k-1)  =  (xy)^(k-2) (yx)^k (xy)^(k-1+lcm(k-1))

where `lcm(k-1) = lcm(1, ..., k-1)`. By their Fact 1, an identity of `T_k` is
exactly a pair that no `k`-state DFA separates. This section transcribes their
proof into Lean.

**Dictionary.** Letters: `x = 0`, `y = 1`, so `xy` is the list `[0, 1]` and
`(xy)^n` is `(List.replicate n [0, 1]).flatten`. BKSS write `q.w` for the state
reached from `q` by reading `w` left to right, which is `w.foldl δ q` here, and
a DFA with start state `s` separates `u` and `v` iff `s.u ≠ s.v`, which is the
condition of `exists_eval_ne_iff_exists_step`. Length: BKSS define the length
of an identity as `max(|u|, |v|)`; here both sides have length exactly
`2 lcm(1, ..., k-1) + 6(k-1)`. At `k = 5`, `lcm(1, 2, 3, 4) = 12` and
`2·15 + 2·5 + 2·4 = 48`, so `¬ SuffStates 5 48` is their statement at `k = 5`
with no change of length convention. These are the words checked numerically
by `computations/separating_words/bkss_identity.py`.

**Proof structure.** Write `f` for the map of `xy` and `g` for the map of `yx`.
The two sides send `s` to `f^(k-1) (g^k (f^(k-2+L) s))` and
`f^(k-1+L) (g^k (f^(k-2) s))`. BKSS split on the `xy`-cycle through
`s.(xy)^(k-2)`: (i) that state is on no cycle, so `f^(k-1)` is a constant map;
(ii) it is on a cycle of length `m < k`, so every cycle is shorter than `k`, all
cycle lengths divide `L`, and `f^(k-1) = f^(k-1+L)`; (iii) `m = k`, so `f` is a
`k`-cycle, `x` and `y` are permutations and `(yx)^k = 1`. `bkss_core` uses
the same three arguments, selected by a split that is easier to state in Lean:
either some state `q` has `k` distinct iterates `q, f q, ..., f^(k-1) q` (these
are then all the states, and `f^k q = f^r q` with `r < k`: `r = 0` gives (iii),
`r = k-1` gives (i), `1 ≤ r ≤ k-2` gives (ii)), or no state does, and every
orbit repeats within its first `k` iterates, which gives (ii). `bkss_perm` is
the step `(xy)^k = 1 → (yx)^k = 1` of (iii). No transformation is enumerated. -/

/-- Reading `n` copies of a word `w` iterates the map that `w` induces. -/
private theorem foldl_flatten_replicate {σ : Type*} (δ : σ → Fin 2 → σ)
    (w : List (Fin 2)) (n : ℕ) (s : σ) :
    (List.replicate n w).flatten.foldl δ s = (fun q => w.foldl δ q)^[n] s := by
  induction n generalizing s with
  | zero => rfl
  | succ n ih => rw [List.replicate_succ, List.flatten_cons, List.foldl_append, ih,
      Function.iterate_succ_apply]

open Function in
/-- Once the orbit of `x` returns after `c` steps from step `r`, every later
point returns after any multiple `L` of `c`. -/
private theorem iterate_add_eq_of_period {α : Type*} (f : α → α) (x : α)
    {r c a L : ℕ} (h : f^[r + c] x = f^[r] x) (hc : c ∣ L) (hra : r ≤ a) :
    f^[a + L] x = f^[a] x := by
  obtain ⟨t, rfl⟩ := hc
  have steps : ∀ t, f^[r + c * t] x = f^[r] x := by
    intro t
    induction t with
    | zero => simp
    | succ t ih =>
      rw [show r + c * (t + 1) = c + (r + c * t) by ring, iterate_add_apply, ih,
        ← iterate_add_apply, add_comm, h]
  rw [show a + c * t = (a - r) + (r + c * t) by omega, iterate_add_apply, steps,
    ← iterate_add_apply, show a - r + r = a by omega]

open Function in
/-- The case analysis of BKSS Theorem 8, for arbitrary maps `f` (standing for
`xy`) and `g` (standing for `yx`) of a `k`-element set, given that `f^k = id`
forces `g^k = id`. -/
private theorem bkss_core {k L : ℕ} (hk : 2 ≤ k) (hL : ∀ c, 0 < c → c < k → c ∣ L)
    (f g : Fin k → Fin k) (hg : f^[k] = id → g^[k] = id) (s : Fin k) :
    f^[k - 1] (g^[k] (f^[k - 2 + L] s)) = f^[k - 1 + L] (g^[k] (f^[k - 2] s)) := by
  by_cases hinj : ∃ q, Injective (fun t : Fin k => f^[t] q)
  · obtain ⟨q, hq⟩ := hinj
    have hsurj : Surjective (fun t : Fin k => f^[t] q) :=
      Finite.injective_iff_surjective.mp hq
    have horb : ∀ x, ∃ t : ℕ, f^[t] q = x := fun x => by
      obtain ⟨t, ht⟩ := hsurj x
      exact ⟨t, ht⟩
    obtain ⟨⟨r, hr⟩, hrk⟩ := hsurj (f^[k] q)
    simp only at hrk
    rcases (show r = 0 ∨ r = k - 1 ∨ (1 ≤ r ∧ r ≤ k - 2) by omega) with
      rfl | rfl | ⟨h1, h2⟩
    · -- (iii) `f` is a `k`-cycle: `f^k = id`, hence `g^k = id`
      have hfk : f^[k] = id := by
        funext x
        obtain ⟨t, rfl⟩ := horb x
        rw [← iterate_add_apply, add_comm, iterate_add_apply, ← hrk]
        rfl
      rw [hg hfk]
      simp only [id_eq, ← iterate_add_apply]
      congr 1
      omega
    · -- (i) `f^(k-1)` is constant
      have h1 : f^[k - 1 + 1] q = f^[k - 1] q := by
        rw [Nat.sub_add_cancel (by omega : 1 ≤ k)]
        exact hrk.symm
      have hconst : ∀ x, f^[k - 1] x = f^[k - 1] q := by
        intro x
        obtain ⟨t, rfl⟩ := horb x
        rw [← iterate_add_apply]
        exact iterate_add_eq_of_period f q h1 (one_dvd t) le_rfl
      rw [iterate_add_apply f (k - 1) L]
      exact (hconst _).trans (hconst _).symm
    · -- (ii) the only cycle has length `k - r < k`
      have hper : f^[r + (k - r)] q = f^[r] q := by
        rw [show r + (k - r) = k by omega]
        exact hrk.symm
      have hcL : (k - r) ∣ L := hL _ (by omega) (by omega)
      have htail : ∀ x a, r ≤ a → f^[a + L] x = f^[a] x := by
        intro x a ha
        obtain ⟨t, rfl⟩ := horb x
        simp only [← iterate_add_apply]
        rw [show a + L + t = (a + t) + L by omega]
        exact iterate_add_eq_of_period f q hper hcL (by omega)
      rw [htail s (k - 2) (by omega), htail _ (k - 1) (by omega)]
  · -- (ii) every orbit repeats within its first `k` iterates
    have htail : ∀ x a, k - 2 ≤ a → f^[a + L] x = f^[a] x := by
      intro x a ha
      obtain ⟨t1, t2, heq, hne⟩ : ∃ t1 t2 : Fin k, f^[t1] x = f^[t2] x ∧ t1 ≠ t2 := by
        by_contra hc
        push Not at hc
        exact hinj ⟨x, fun t1 t2 h => hc t1 t2 h⟩
      rcases lt_or_gt_of_ne (fun h => hne (Fin.ext h)) with h | h
      · refine iterate_add_eq_of_period f x (r := t1) (c := t2 - t1) ?_
          (hL _ (by omega) (by omega)) (by omega)
        rw [show (t1 : ℕ) + (t2 - t1) = t2 by omega]
        exact heq.symm
      · refine iterate_add_eq_of_period f x (r := t2) (c := t1 - t2) ?_
          (hL _ (by omega) (by omega)) (by omega)
        rw [show (t2 : ℕ) + (t1 - t2) = t1 by omega]
        exact heq
    rw [htail s (k - 2) le_rfl, htail _ (k - 1) (by omega)]

open Function in
/-- Case (iii) of BKSS Theorem 8: if `xy` acts as a map whose `k`-th power is
the identity, so does `yx`. Reading `x` is then injective, hence a bijection,
and it conjugates `xy` to `yx`. -/
private theorem bkss_perm {k : ℕ} (hk : 1 ≤ k) (δ : Fin k → Fin 2 → Fin k)
    (h : (fun q => ([0, 1] : List (Fin 2)).foldl δ q)^[k] = id) :
    (fun q => ([1, 0] : List (Fin 2)).foldl δ q)^[k] = id := by
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  have hsemi : Semiconj (fun q => δ q 0) (fun q => ([0, 1] : List (Fin 2)).foldl δ q)
      (fun q => ([1, 0] : List (Fin 2)).foldl δ q) := fun _ => rfl
  have hinj : Injective (fun q => δ q 0) := by
    intro x y hxy
    have e : ∀ z, (fun q => ([0, 1] : List (Fin 2)).foldl δ q)^[j + 1] z = z :=
      fun z => congrFun h z
    have hf : ([0, 1] : List (Fin 2)).foldl δ x = ([0, 1] : List (Fin 2)).foldl δ y :=
      congrArg (fun z => δ z 1) hxy
    rw [← e x, ← e y, iterate_succ_apply, iterate_succ_apply, hf]
  have hsurj : Surjective (fun q => δ q 0) := Finite.injective_iff_surjective.mp hinj
  funext z
  obtain ⟨x, rfl⟩ := hsurj z
  rw [← hsemi.iterate_right (j + 1) x, h]
  rfl

/-- **Bulatov, Karpova, Shur and Startsev, Theorem 8** (Electron. J. Combin.
24(3) (2017) #P3.35, arXiv:1609.03199), with `x = 0` and `y = 1`: no `k`-state
transition function separates `(01)^(k-2+L) (10)^k (01)^(k-1)` from
`(01)^(k-2) (10)^k (01)^(k-1+L)` when every `c` with `0 < c < k` divides `L`
(so `L = lcm(1, ..., k-1)` qualifies). Both words have length
`2L + 6(k-1)`. The hypothesis `2 ≤ k` only keeps the natural-number
subtractions `k - 2` and `k - 1` honest. The proof follows theirs; see the
section docstring for the case correspondence. -/
theorem not_separates_bkss {k L : ℕ} (hk : 2 ≤ k) (hL : ∀ c, 0 < c → c < k → c ∣ L)
    (δ : Fin k → Fin 2 → Fin k) (s : Fin k) :
    ((List.replicate (k - 2 + L) [0, 1]).flatten ++ (List.replicate k [1, 0]).flatten
        ++ (List.replicate (k - 1) [0, 1]).flatten : List (Fin 2)).foldl δ s
      = ((List.replicate (k - 2) [0, 1]).flatten ++ (List.replicate k [1, 0]).flatten
        ++ (List.replicate (k - 1 + L) [0, 1]).flatten : List (Fin 2)).foldl δ s := by
  simp only [List.foldl_append, foldl_flatten_replicate]
  exact bkss_core hk hL _ _ (bkss_perm (by omega) δ) s

/-- **5 states do not suffice at length 48**: BKSS Theorem 8 at `k = 5`,
`L = lcm(1, 2, 3, 4) = 12`. No 5-state DFA separates
`(01)^15 (10)^5 (01)^4` from `(01)^3 (10)^5 (01)^16`, two distinct words of
length 48; the mathematics is BKSS's. The step to `N(5) ≤ 47`, and to
`not_suffStates_five_68` as a corollary, also uses that `SuffStates k (n + 1)`
implies `SuffStates k n` (prefix both words with one letter), which is not
proved in this file. The `decide` calls only check `c ∣ 12` for `c < 5` and
the lengths and distinctness of two fixed 48-letter lists; nothing enumerates
automata. -/
theorem not_suffStates_five_48 : ¬ SuffStates 5 48 := by
  intro h
  have hL : ∀ c, 0 < c → c < 5 → c ∣ 12 := by
    intro c hc h5
    interval_cases c <;> decide
  obtain ⟨M, hM⟩ := h
    ((List.replicate 15 [0, 1]).flatten ++ (List.replicate 5 [1, 0]).flatten
      ++ (List.replicate 4 [0, 1]).flatten)
    ((List.replicate 3 [0, 1]).flatten ++ (List.replicate 5 [1, 0]).flatten
      ++ (List.replicate 16 [0, 1]).flatten)
    (by decide) (by decide) (by decide)
  exact eval_ne_of_separates hM
    (not_separates_bkss (k := 5) (L := 12) (by norm_num) hL M.step M.start)

/-! ### More states never hurt, so a failure at `k` states bounds `sep` -/

/-- A `k`-state separator is also a `(k + 1)`-state separator: add one state
that the run never reaches. -/
theorem suffStates_succ {k n : ℕ} (h : SuffStates k n) : SuffStates (k + 1) n := by
  intro u v hu hv huv
  obtain ⟨M, hM⟩ := h u v hu hv huv
  rw [exists_separates_iff_exists_eval_ne, exists_eval_ne_iff_exists_step]
  let δ : Fin (k + 1) → Fin 2 → Fin (k + 1) := fun q a =>
    if hq : q.val < k then Fin.castSucc (M.step ⟨q, hq⟩ a) else q
  have key : ∀ (w : List (Fin 2)) (p : Fin k),
      w.foldl δ p.castSucc = (w.foldl M.step p).castSucc := by
    intro w
    induction w with
    | nil => intro p; rfl
    | cons a w ih =>
      intro p
      simp only [List.foldl_cons, δ, Fin.val_castSucc, Fin.is_lt, dite_true, Fin.eta]
      exact ih _
  refine ⟨δ, M.start.castSucc, ?_⟩
  rw [key, key]
  exact fun hEq => eval_ne_of_separates hM (Fin.castSucc_injective k hEq)

/-- `SuffStates k n` is monotone in `k`. -/
theorem suffStates_mono {k k' n : ℕ} (hk : k ≤ k') (h : SuffStates k n) :
    SuffStates k' n := by
  induction hk with
  | refl => exact h
  | step _ ih => exact suffStates_succ ih

/-- If `k` states do not suffice at length `n`, then `k < sep n`. -/
theorem lt_sep_of_not_suffStates {k n : ℕ} (h : ¬ SuffStates k n) : k < sep n := by
  by_contra hle
  push Not at hle
  have hmem0 : sep n ∈ {k | SuffStates k n} := Nat.sInf_mem ⟨n + 2, suffStates_add_two n⟩
  have hmem : SuffStates (sep n) n := hmem0
  exact h (suffStates_mono hle hmem)

/-- **`6 ≤ sep 48`**, from BKSS Theorem 8 (`not_suffStates_five_48`). BKSS
state the same fact as `Sep(48) > 5` in Proposition 14, in their convention of
words of length at most `n`. -/
theorem six_le_sep_48 : 6 ≤ sep 48 := lt_sep_of_not_suffStates not_suffStates_five_48

end OpenProblems.SeparatingWords
