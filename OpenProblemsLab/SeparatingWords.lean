import Mathlib.Computability.DFA
import Mathlib.Order.Lattice.Nat
import Mathlib.Data.Nat.Log

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

end OpenProblems.SeparatingWords
