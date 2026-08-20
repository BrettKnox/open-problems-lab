import Mathlib.NumberTheory.Divisors
import Mathlib.NumberTheory.ArithmeticFunction.Misc
import Mathlib.Data.Nat.Factorization.Defs
import Mathlib.Tactic.IntervalCases

/-!
# Erdős problem #414: trajectories of n ↦ n + τ(n)

Iterate `h(n) = n + τ(n)` where `τ(n)` is the number of divisors of `n`.
Question (Spiro; discussed by Erdős–Graham 1980, who believed yes): do the
trajectories of any two starting points `m, n ≥ 2` eventually merge?

Status 2026-08-20: OPEN. erdosproblems.com/414 — essentially zero literature
since 1980, nobody registered as working on it. OEIS A064491.

## What is proved here

* `lt_step` / `step_add_two_le` — the map strictly increases (by ≥ 2 from
  `n ≥ 2`), so trajectories are strictly increasing and meeting once means
  merged forever (`merged_of_eq`).
* **`merge_upTo30`** — every starting point `2 ≤ m ≤ 30` merges with the
  trajectory of 2, with explicit iterate indices, each instance verified by
  kernel `decide` (no `native_decide`). As far as we could determine, these
  are the first machine-checked instances of EP #414. The full conjecture is
  the statement `trajectoriesMerge` below.

Next lemmas planned: `τ(n)` is odd iff `n` is a square (absent from mathlib —
an upstreamable target), and the induced two-parity-stream structure between
squares that explains the census in `computations/tau_trajectories/`.
-/

namespace OpenProblems.TauTrajectories

/-- One step: `n ↦ n + τ(n)` where `τ` counts divisors. -/
def step (n : ℕ) : ℕ := n + n.divisors.card

/-- **Open question** (EP #414): for all `m, n ≥ 2` the `step`-trajectories
meet, i.e. `step^[i] m = step^[j] n` for some `i, j`. (The map is
deterministic and strictly increasing on `n ≥ 2`, so meeting once means
merged forever.) -/
def trajectoriesMerge : Prop :=
  ∀ m n : ℕ, 2 ≤ m → 2 ≤ n → ∃ i j : ℕ, step^[i] m = step^[j] n

/-- `τ(n) ≥ 1` for `n ≥ 1`, so the map moves: `n < step n`. -/
theorem lt_step {n : ℕ} (hn : 1 ≤ n) : n < step n := by
  have : 1 ∈ n.divisors := Nat.one_mem_divisors.mpr (by omega)
  have : 0 < n.divisors.card := Finset.card_pos.mpr ⟨1, this⟩
  simp only [step]
  omega

/-- `τ(n) ≥ 2` for `n ≥ 2` (both `1` and `n` divide), so `n + 2 ≤ step n`. -/
theorem step_add_two_le {n : ℕ} (hn : 2 ≤ n) : n + 2 ≤ step n := by
  have h1 : 1 ∈ n.divisors := Nat.one_mem_divisors.mpr (by omega)
  have hn' : n ∈ n.divisors := Nat.mem_divisors_self n (by omega)
  have hpair : ({1, n} : Finset ℕ) ⊆ n.divisors := by
    intro x hx
    rcases Finset.mem_insert.mp hx with h | h
    · exact h ▸ h1
    · exact (Finset.mem_singleton.mp h) ▸ hn'
  have hcard : ({1, n} : Finset ℕ).card = 2 := by
    rw [Finset.card_insert_of_notMem (by simp; omega), Finset.card_singleton]
  have := Finset.card_le_card hpair
  simp only [step]
  omega

/-- Once two trajectories meet they agree forever after (determinism). -/
theorem merged_of_eq {m n i j : ℕ} (h : step^[i] m = step^[j] n) :
    ∀ k : ℕ, step^[i + k] m = step^[j + k] n := by
  intro k
  rw [Nat.add_comm i k, Nat.add_comm j k, Function.iterate_add_apply,
    Function.iterate_add_apply, h]

/-- **Machine-checked instances of EP #414**: every starting point
`2 ≤ m ≤ 30` merges with the trajectory of `2`. Indices found by search;
each equality is verified by the kernel. -/
theorem merge_upTo30 : ∀ m : ℕ, 2 ≤ m → m ≤ 30 →
    ∃ i j : ℕ, step^[i] m = step^[j] 2 := by
  intro m h2 h30
  interval_cases m
  · exact ⟨0, 0, by decide⟩
  · exact ⟨2, 2, by decide⟩
  · exact ⟨0, 1, by decide⟩
  · exact ⟨1, 2, by decide⟩
  · exact ⟨3, 5, by decide⟩
  · exact ⟨0, 2, by decide⟩
  · exact ⟨1, 4, by decide⟩
  · exact ⟨0, 3, by decide⟩
  · exact ⟨2, 5, by decide⟩
  · exact ⟨8, 8, by decide⟩
  · exact ⟨0, 4, by decide⟩
  · exact ⟨7, 8, by decide⟩
  · exact ⟨1, 5, by decide⟩
  · exact ⟨6, 8, by decide⟩
  · exact ⟨5, 8, by decide⟩
  · exact ⟨6, 8, by decide⟩
  · exact ⟨0, 5, by decide⟩
  · exact ⟨5, 8, by decide⟩
  · exact ⟨3, 8, by decide⟩
  · exact ⟨4, 8, by decide⟩
  · exact ⟨3, 8, by decide⟩
  · exact ⟨4, 8, by decide⟩
  · exact ⟨0, 6, by decide⟩
  · exact ⟨3, 8, by decide⟩
  · exact ⟨2, 8, by decide⟩
  · exact ⟨13, 14, by decide⟩
  · exact ⟨2, 8, by decide⟩
  · exact ⟨13, 14, by decide⟩
  · exact ⟨1, 8, by decide⟩

/-! ### The parity mechanism

`τ(n)` is odd exactly when `n` is a square (each divisor `d < √n` pairs with
`n/d`; equivalently, all factorization exponents are even). Hence `step`
preserves the parity of a trajectory except exactly when stepping from a
square — the mechanism behind the census structure in
`computations/tau_trajectories/`. The parity criterion itself appears to be
absent from mathlib (an upstreaming candidate). -/

/-- A product of naturals is odd iff every factor is odd. (Not found in
mathlib; proved by induction.) -/
private lemma odd_prod_iff {α : Type} (s : Finset α) (f : α → ℕ) :
    Odd (∏ x ∈ s, f x) ↔ ∀ x ∈ s, Odd (f x) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, Nat.odd_mul, ih]
    constructor
    · rintro ⟨h1, h2⟩ x hx
      rcases Finset.mem_insert.mp hx with rfl | hx'
      · exact h1
      · exact h2 x hx'
    · intro h
      exact ⟨h a (Finset.mem_insert_self a s),
        fun x hx => h x (Finset.mem_insert_of_mem hx)⟩

/-- **`τ(n)` is odd iff `n` is a perfect square** (for `n ≥ 1`). -/
theorem odd_card_divisors_iff_isSquare {n : ℕ} (hn : n ≠ 0) :
    Odd n.divisors.card ↔ IsSquare n := by
  rw [Nat.card_divisors hn, Nat.isSquare_iff_even_factorization, odd_prod_iff]
  constructor
  · intro h p hp
    by_cases hmem : p ∈ n.primeFactors
    · obtain ⟨k, hk⟩ := h p hmem
      exact ⟨k, by omega⟩
    · have h0 : n.factorization p = 0 := by
        rw [← Nat.support_factorization] at hmem
        exact Finsupp.notMem_support_iff.mp hmem
      simp [h0]
  · intro h p hmem
    obtain ⟨k, hk⟩ := h p (Nat.prime_of_mem_primeFactors hmem)
    exact ⟨k, by omega⟩

/-- Off squares, `step` preserves parity. -/
theorem step_parity_of_not_isSquare {n : ℕ} (hn : n ≠ 0) (h : ¬ IsSquare n) :
    step n % 2 = n % 2 := by
  have hev : Even n.divisors.card := by
    rcases Nat.even_or_odd n.divisors.card with he | ho
    · exact he
    · exact absurd ((odd_card_divisors_iff_isSquare hn).mp ho) h
  obtain ⟨k, hk⟩ := hev
  simp only [step]
  omega

/-- At squares, `step` flips parity. -/
theorem step_parity_of_isSquare {n : ℕ} (hn : n ≠ 0) (h : IsSquare n) :
    step n % 2 ≠ n % 2 := by
  have hodd : Odd n.divisors.card := (odd_card_divisors_iff_isSquare hn).mpr h
  obtain ⟨k, hk⟩ := hodd
  simp only [step]
  omega

/-- The pairwise form: any two starting points in `[2, 30]` have merging
trajectories — the EP #414 property, verified on this box. -/
theorem merge_pairs_upTo30 : ∀ m n : ℕ, 2 ≤ m → m ≤ 30 → 2 ≤ n → n ≤ 30 →
    ∃ i j : ℕ, step^[i] m = step^[j] n := by
  intro m n hm2 hm30 hn2 hn30
  obtain ⟨i₁, j₁, h₁⟩ := merge_upTo30 m hm2 hm30
  obtain ⟨i₂, j₂, h₂⟩ := merge_upTo30 n hn2 hn30
  -- meet 2's trajectory at indices j₁, j₂; walk both to max j₁ j₂
  refine ⟨i₁ + (max j₁ j₂ - j₁), i₂ + (max j₁ j₂ - j₂), ?_⟩
  have e₁ := merged_of_eq h₁ (max j₁ j₂ - j₁)
  have e₂ := merged_of_eq h₂ (max j₁ j₂ - j₂)
  rw [e₁, e₂]
  congr 1
  omega

end OpenProblems.TauTrajectories
