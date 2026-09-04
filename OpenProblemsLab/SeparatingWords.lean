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
rejects the other). Known: `sep n = Ω(log n)` (folklore) and
`sep n = O(n^{1/3} log^7 n)` (Chase, STOC 2021). The conjecture is that
`O(log n)` states suffice.

Status 2026-08-19: OPEN. A claimed `O(log² n)` improvement (arXiv:2503.23184)
was withdrawn in April 2025. Quiet since Chase. Not in formal-conjectures.

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

The classical `Ω(log n)` lower bound rests on one observation: a `k`-state
automaton cannot see a block whose length changes by `lcm(1, ..., k)`.
Iterating any endofunction of a `k`-element type is eventually periodic with
preperiod `≤ k - 1` and period `≤ k`, so once a run is `k - 1` letters into a
block, the block's length matters only modulo that period.

`iterate_eq_add_of_card_le` is that fact, and `not_separates_block_shift` is
Theorem 1 of Demaine, Eisenstat, Shallit and Wilson
([arXiv:1103.4513](https://arxiv.org/abs/1103.4513), 2011), which follows from
it. The computations in `computations/separating_words` find that the bound it
gives is exact wherever exhaustive search reaches, which is the content of the
`N(k) = 2k - 3 + lcm(1, ..., k)` conjecture recorded there. -/

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
`N(k) ≤ 2k - 3 + lcm(1, …, k)`. With `L = lcm(1, …, k)` this is
`N(1..4) = 0, 3, 9, 17` exactly, and predicts `N(5) = 67`. -/
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

/-- The case that matters now: **5 states do not suffice at length 68**, since
`lcm(1, …, 5) = 60` and `4 + 4 + 60 = 68`. Combined with the exhaustive
verification that 5 states *do* suffice for every length up to 30, this
brackets the crossover: `N(5)` lies in `[30, 67]`, and the computations
conjecture `N(5) = 67` exactly. -/
theorem not_suffStates_five_68 : ¬ SuffStates 5 68 := by
  have h : ∀ c, 0 < c → c ≤ 5 → c ∣ 60 := by
    intro c hc h5
    interval_cases c <;> decide
  simpa using not_suffStates_block_shift (k := 5) (L := 60) (by norm_num)
    (by norm_num) h

end OpenProblems.SeparatingWords
