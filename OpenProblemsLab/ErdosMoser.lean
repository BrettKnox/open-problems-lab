import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.Ring.GeomSum

/-!
# Erdős–Moser equation

`1^k + 2^k + ⋯ + (m−1)^k = m^k` has only the solution `1 + 2 = 3`
(i.e. `m = 3, k = 1`).

Status 2026-08-19: OPEN. Known: any other solution has `m > 10^(10^9)`
(Gallot–Moree–Zudilin 2011, via continued-fraction expansion of log 2); Moser
(1953) proved odd `k` elementarily. Quiet — the compute lane is unowned. In
formal-conjectures (`Wikipedia/ErdosMoser.lean`); this statement is written
independently.

Attack lanes: extend the GMZ continued-fraction computation past `10^(10^10)`
(mechanical, HPC); formalize Moser's elementary odd-`k` proof.
-/

namespace OpenProblems.ErdosMoser

/-- **Open conjecture** (Erdős–Moser): the only solution of
`∑_{i<m} i^k = m^k` with `m ≥ 2, k ≥ 1` is `1 + 2 = 3`. -/
def conjecture : Prop :=
  ∀ m k : ℕ, 2 ≤ m → 1 ≤ k →
    (∑ i ∈ Finset.range m, i ^ k) = m ^ k → m = 3 ∧ k = 1

/-- **The `k = 1` case, complete**: `1 + 2 + ⋯ + (m−1) = m` only at `m = 3`.
By Gauss, `2·∑ = m(m−1)`, so the equation forces `m − 1 = 2`. The open
content of Erdős–Moser is entirely in `k ≥ 2`. -/
theorem k_eq_one_case :
    ∀ m : ℕ, 2 ≤ m → (∑ i ∈ Finset.range m, i ^ 1) = m ^ 1 → m = 3 := by
  intro m hm hsum
  simp only [pow_one] at hsum
  have hg : (∑ i ∈ Finset.range m, i) * 2 = m * (m - 1) :=
    Finset.sum_range_id_mul_two m
  rw [hsum] at hg
  have hne : 0 < m := by omega
  have h2 : 2 = m - 1 := Nat.eq_of_mul_eq_mul_left hne (by omega)
  omega

/-! ### Moser's pairing step (odd `k`)

Moser's 1953 elementary treatment of odd `k` starts by folding the sum onto
itself: for odd `k`, `i^k + (m-i)^k` is divisible by `m`, so pairing `i` with
`m - i` shows `m ∣ 2·∑_{i<m} i^k`. Combined with the equation this constrains
solutions sharply. Formalized here as the first rung; the full odd-`k`
argument (which continues mod `m^2` and needs power sums mod `m`) is the
remaining EM-1 target. -/

/-- For odd `k`, the pair `{i, m-i}` contributes a multiple of `m`. -/
theorem pair_dvd {m i k : ℕ} (hk : Odd k) (hi : i ≤ m) :
    m ∣ i ^ k + (m - i) ^ k := by
  have h : i + (m - i) = m := by omega
  have := Odd.nat_add_dvd_pow_add_pow (x := i) (y := m - i) hk
  rwa [h] at this

/-- **The pairing step**: for odd `k`, `m` divides twice the power sum
`∑_{i<m} i^k`. Fold `i ↔ m - i` over `1 ≤ i ≤ m-1`; each pair sums to `m`,
and for odd `k` that makes each pair's contribution a multiple of `m`. -/
theorem two_mul_sum_dvd {m k : ℕ} (hm : 1 ≤ m) (hk : Odd k) :
    m ∣ 2 * ∑ i ∈ Finset.range m, i ^ k := by
  obtain ⟨t, rfl⟩ : ∃ t, m = t + 1 := ⟨m - 1, by omega⟩
  have hk1 : 1 ≤ k := by
    obtain ⟨j, hj⟩ := hk
    omega
  -- drop the zero term: ∑_{i<t+1} i^k = ∑_{j<t} (j+1)^k
  have hshift : ∑ i ∈ Finset.range (t + 1), i ^ k
      = ∑ j ∈ Finset.range t, (j + 1) ^ k := by
    rw [Finset.sum_range_succ' (fun i => i ^ k) t, zero_pow (by omega), add_zero]
  -- reflect: ∑_{j<t} (j+1)^k = ∑_{j<t} (t-j)^k, and (j+1) + (t-j) = t+1
  have hrefl : ∑ j ∈ Finset.range t, (j + 1) ^ k
      = ∑ j ∈ Finset.range t, (t - j) ^ k := by
    rw [← Finset.sum_range_reflect (fun j => (j + 1) ^ k) t]
    refine Finset.sum_congr rfl fun j hj => ?_
    have : t - 1 - j + 1 = t - j := by
      have := Finset.mem_range.mp hj; omega
    rw [this]
  have hsum : 2 * ∑ i ∈ Finset.range (t + 1), i ^ k
      = ∑ j ∈ Finset.range t, ((j + 1) ^ k + (t - j) ^ k) := by
    rw [Finset.sum_add_distrib, ← hrefl, hshift, two_mul]
  rw [hsum]
  refine Finset.dvd_sum fun j hj => ?_
  have hjt : j < t := Finset.mem_range.mp hj
  have hpair : (j + 1) + (t - j) = t + 1 := by omega
  have := Odd.nat_add_dvd_pow_add_pow (x := j + 1) (y := t - j) hk
  rwa [hpair] at this

/-- **Moser's constraint for odd `k`**: a solution with odd `k` forces
`m ∣ 2·m^k`, which is automatic — the content only appears one step further,
mod `m^2`. Recorded as the ladder's next target. -/
def moserOddK : Prop :=
  ∀ m k : ℕ, 2 ≤ m → Odd k → 3 ≤ k →
    (∑ i ∈ Finset.range m, i ^ k) ≠ m ^ k

end OpenProblems.ErdosMoser
