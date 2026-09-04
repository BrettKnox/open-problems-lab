import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.Ring.GeomSum
import Mathlib.NumberTheory.Multiplicity
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.Data.ZMod.Basic

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

/-! ### The `k = 3` case, complete

`∑_{i<m} i³ = m³` has no solution with `m ≥ 2`. Squaring Gauss's identity
gives `4·∑_{i≤t} i³ = (t(t+1))²` (proved here — mathlib has the linear Gauss
sum but not the cubic one), and the equation then collapses to `t² = 4t + 4`,
which has no integer root. -/

/-- Sum of cubes, in a subtraction-free form: `4·∑_{i≤t} i³ = (t(t+1))²`. -/
theorem four_mul_sum_cubes (t : ℕ) :
    4 * ∑ i ∈ Finset.range (t + 1), i ^ 3 = (t * (t + 1)) ^ 2 := by
  induction t with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, Nat.mul_add, ih]
    ring

/-- **The `k = 3` case, complete**: `∑_{i<m} i³ = m³` has no solution with
`m ≥ 2`. -/
theorem k_eq_three_case :
    ∀ m : ℕ, 2 ≤ m → (∑ i ∈ Finset.range m, i ^ 3) ≠ m ^ 3 := by
  intro m hm hsol
  obtain ⟨t, rfl⟩ : ∃ t, m = t + 1 := ⟨m - 1, by omega⟩
  have h4 := four_mul_sum_cubes t
  rw [hsol] at h4
  -- (t(t+1))² = 4(t+1)³, i.e. t²(t+1)² = 4(t+1)³, so t² = 4(t+1)
  have ht1 : 0 < (t + 1) ^ 2 := by positivity
  have hkey : t ^ 2 = 4 * (t + 1) := by
    have hexp : 4 * (t + 1) ^ 3 = (4 * (t + 1)) * (t + 1) ^ 2 := by ring
    have hlhs : (t * (t + 1)) ^ 2 = t ^ 2 * (t + 1) ^ 2 := by ring
    rw [hlhs, hexp] at h4
    exact Nat.eq_of_mul_eq_mul_right ht1 h4.symm
  -- t² = 4t + 4 has no natural solution
  rcases Nat.lt_or_ge t 6 with hlt | hge
  · interval_cases t <;> omega
  · nlinarith [hge]

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

/-! ### The mod-`m²` step

The pairing is only the warm-up: modulo `m²` the binomial expansion gives, for
odd `k`,
  `i^k + (m-i)^k ≡ k·m·i^(k-1)  (mod m²)`,
so summing the pairs turns the equation into a congruence on the *lower*
power sum. Since `m² ∣ 2m^k` for `k ≥ 2`, a solution forces `m ∣ k·∑ i^(k-1)`
— Moser's actual lever. Worked in `ℤ` (truncated subtraction in `ℕ` makes the
binomial step unstateable). -/

/-- Binomial step: for odd `k`, `i^k + (m-i)^k ≡ k·m·i^(k-1)` mod `m²`. -/
theorem pair_congr_sq (m i : ℤ) {k : ℕ} (hk : Odd k) :
    (m ^ 2 : ℤ) ∣ (i ^ k + (m - i) ^ k) - k * m * i ^ (k - 1) := by
  have hbase := sq_dvd_add_pow_sub_sub m (-i) k
  -- (-i + m)^k - (-i)^(k-1)*m*k - (-i)^k
  have hneg1 : (-i) ^ k = -(i ^ k) := hk.neg_pow i
  have hk1 : Even (k - 1) := by
    obtain ⟨j, hj⟩ := hk
    exact ⟨j, by omega⟩
  have hneg2 : (-i) ^ (k - 1) = i ^ (k - 1) := hk1.neg_pow i
  rw [hneg1, hneg2] at hbase
  have hcomm : (-i + m) = (m - i) := by ring
  rw [hcomm] at hbase
  have : (m - i) ^ k - i ^ (k - 1) * m * k - -(i ^ k)
      = (i ^ k + (m - i) ^ k) - k * m * i ^ (k - 1) := by ring
  rwa [this] at hbase

/-- Reflection: `∑_{i<m} (m-i)^k = ∑_{i<m} i^k + m^k` (reindex `i ↦ m-1-i`,
then shift). -/
theorem sum_sub_reflect {m k : ℕ} (hk : 1 ≤ k) :
    ∑ i ∈ Finset.range m, ((m : ℤ) - i) ^ k
      = (∑ i ∈ Finset.range m, (i : ℤ) ^ k) + (m : ℤ) ^ k := by
  have h1 : ∑ i ∈ Finset.range m, ((m : ℤ) - i) ^ k
      = ∑ j ∈ Finset.range m, ((j : ℤ) + 1) ^ k := by
    rw [← Finset.sum_range_reflect (fun j => ((m : ℤ) - j) ^ k) m]
    refine Finset.sum_congr rfl fun j hj => ?_
    have hjm : j < m := Finset.mem_range.mp hj
    have : ((m - 1 - j : ℕ) : ℤ) = (m : ℤ) - 1 - j := by
      have : (1 : ℕ) ≤ m := by omega
      push_cast [Nat.cast_sub (by omega : j ≤ m - 1), Nat.cast_sub this]
      ring
    rw [this]
    ring_nf
  rw [h1]
  have h2 : ∑ i ∈ Finset.range (m + 1), (i : ℤ) ^ k
      = ∑ j ∈ Finset.range m, ((j : ℤ) + 1) ^ k := by
    rw [Finset.sum_range_succ' (fun i => (i : ℤ) ^ k) m]
    push_cast
    rw [zero_pow (by omega : k ≠ 0), add_zero]
  rw [← h2, Finset.sum_range_succ]

/-- **Moser's mod-`m²` identity**: for odd `k`, pairing `i ↔ m-i` turns the
power sum into a congruence on the *lower* power sum:
`2·∑ i^k + m^k ≡ k·m·∑ i^(k-1)  (mod m²)`. -/
theorem two_mul_sum_congr_sq {m k : ℕ} (hk : Odd k) :
    ((m : ℤ) ^ 2) ∣ (2 * (∑ i ∈ Finset.range m, (i : ℤ) ^ k) + (m : ℤ) ^ k)
      - k * m * ∑ i ∈ Finset.range m, (i : ℤ) ^ (k - 1) := by
  have hk1 : 1 ≤ k := by obtain ⟨j, hj⟩ := hk; omega
  have hpairs : ∑ i ∈ Finset.range m, ((i : ℤ) ^ k + ((m : ℤ) - i) ^ k)
      = 2 * (∑ i ∈ Finset.range m, (i : ℤ) ^ k) + (m : ℤ) ^ k := by
    rw [Finset.sum_add_distrib, sum_sub_reflect hk1]
    ring
  have hterm : ((m : ℤ) ^ 2) ∣
      ∑ i ∈ Finset.range m, (((i : ℤ) ^ k + ((m : ℤ) - i) ^ k) - k * m * (i : ℤ) ^ (k - 1)) :=
    Finset.dvd_sum fun i _ => pair_congr_sq m i hk
  rw [Finset.sum_sub_distrib, hpairs, ← Finset.mul_sum] at hterm
  exact hterm

/-- For `k ≥ 2` the `m^k` term is itself a multiple of `m²`, leaving
**`m ∣ k·∑_{i<m} i^(k-1)`** whenever `∑_{i<m} i^k = m^k` — Moser's lever. -/
theorem dvd_of_solution {m k : ℕ} (hk : Odd k) (hk2 : 2 ≤ k)
    (hsol : (∑ i ∈ Finset.range m, i ^ k) = m ^ k) :
    (m : ℤ) ∣ k * ∑ i ∈ Finset.range m, (i : ℤ) ^ (k - 1) := by
  have hcong := two_mul_sum_congr_sq (m := m) hk
  have hcast : (∑ i ∈ Finset.range m, (i : ℤ) ^ k) = (m : ℤ) ^ k := by
    have := congrArg (fun n : ℕ => (n : ℤ)) hsol
    push_cast at this
    exact this
  rw [hcast] at hcong
  -- m² ∣ 2m^k + m^k − k·m·S, and m² ∣ 3m^k for k ≥ 2, so m² ∣ k·m·S
  have h3 : ((m : ℤ) ^ 2) ∣ 2 * (m : ℤ) ^ k + (m : ℤ) ^ k := by
    have : ((m : ℤ) ^ 2) ∣ (m : ℤ) ^ k := pow_dvd_pow _ hk2
    exact Dvd.dvd.add (this.mul_left 2) this
  have h4 : ((m : ℤ) ^ 2) ∣ (k : ℤ) * m * ∑ i ∈ Finset.range m, (i : ℤ) ^ (k - 1) := by
    have := dvd_sub h3 hcong
    simpa using this
  obtain ⟨c, hc⟩ := h4
  refine ⟨c, ?_⟩
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · simp
  · have hmz : (m : ℤ) ≠ 0 := by positivity
    have hEq : (m : ℤ) * ((k : ℤ) * ∑ i ∈ Finset.range m, (i : ℤ) ^ (k - 1))
        = (m : ℤ) * ((m : ℤ) * c) := by
      have : (m : ℤ) ^ 2 * c = (m : ℤ) * ((m : ℤ) * c) := by ring
      rw [← this, ← hc]
      ring
    exact mul_left_cancel₀ hmz hEq

/-! ### Power sums modulo a prime

The lever `m ∣ k·∑_{i<m} i^(k-1)` is only useful once the power sum can be
evaluated. Modulo a prime `p` the classical answer is
`∑_{i<p} i^j ≡ -1` when `(p-1) ∣ j` (with `j > 0`), and `≡ 0` otherwise —
mathlib has this for finite fields (`FiniteField.sum_pow_units`); what is
missing is the bridge from a `Finset.range p` sum of naturals, which is what
the Erdős–Moser equation hands us. -/

/-- Range sums push to `ZMod p` termwise. -/
theorem cast_sum_range (p : ℕ) (j : ℕ) :
    ((∑ i ∈ Finset.range p, i ^ j : ℕ) : ZMod p)
      = ∑ i ∈ Finset.range p, (i : ZMod p) ^ j := by
  push_cast
  rfl

/-- **The power sum mod `p`**: `∑_{i<p} i^j ≡ -1 (mod p)` if `(p-1) ∣ j` and
`j > 0`, and `≡ 0` otherwise. Proved by transporting the `Finset.range p` sum
onto `ZMod p` (where the casts enumerate the field exactly once) and applying
the finite-field computation. -/
theorem sum_pow_range_mod (p : ℕ) [hp : Fact p.Prime] {j : ℕ} (hj : 0 < j) :
    ((∑ i ∈ Finset.range p, i ^ j : ℕ) : ZMod p)
      = if (p - 1) ∣ j then -1 else 0 := by
  classical
  rw [cast_sum_range]
  -- the casts of `0, …, p-1` enumerate `ZMod p`
  have hbij : ∑ i ∈ Finset.range p, (i : ZMod p) ^ j = ∑ x : ZMod p, x ^ j := by
    rw [← ZMod.card p] at *
    exact Finset.sum_nbij' (fun i => (i : ZMod p)) (fun x => x.val)
      (fun a _ => Finset.mem_univ _)
      (fun x _ => Finset.mem_range.mpr (ZMod.val_lt x))
      (fun a ha => by
        simp [ZMod.val_natCast_of_lt (Finset.mem_range.mp ha)])
      (fun x _ => by simp [ZMod.natCast_val, ZMod.cast_id])
      (fun a _ => rfl)
  rw [hbij]
  -- split off `x = 0`, then use the finite-field unit sum
  have hzero : (0 : ZMod p) ^ j = 0 := zero_pow (by omega)
  have : ∑ x : ZMod p, x ^ j = ∑ x : (ZMod p)ˣ, ((x : ZMod p) ^ j) := by
    rw [← Finset.sum_subset (Finset.subset_univ (Finset.univ.image
      (fun x : (ZMod p)ˣ => (x : ZMod p))))]
    · rw [Finset.sum_image (fun a _ b _ h => Units.ext h)]
    · intro x _ hx
      have hx0 : x = 0 := by
        by_contra h0
        exact hx (Finset.mem_image.mpr ⟨Units.mk0 x h0, Finset.mem_univ _, rfl⟩)
      rw [hx0, hzero]
  rw [this, FiniteField.sum_pow_units (ZMod p) j, ZMod.card]

/-- **Moser's constraint for odd `k`**: a solution with odd `k` forces
`m ∣ 2·m^k`, which is automatic — the content only appears one step further,
mod `m^2`. Recorded as the ladder's next target. -/
def moserOddK : Prop :=
  ∀ m k : ℕ, 2 ≤ m → Odd k → 3 ≤ k →
    (∑ i ∈ Finset.range m, i ^ k) ≠ m ^ k

/-! ### Moser's odd-`k` theorem, complete

The pairing above gives `m ∣ 2∑`. Pairing the *other* way — `i ↔ (m-1) - i`,
which also maps `range m` to itself — gives `(m-1) ∣ 2∑`. Since consecutive
integers are coprime, `m(m-1) ∣ 2∑`, and on a solution `∑ = m^k` that forces
`m - 1 ∣ 2`. So `m ≤ 3`, and the two survivors are ruled out by hand.

This is the classical fact that for odd `k` the triangular number
`n(n+1)/2` divides `1^k + ⋯ + n^k`, in the form the equation needs. -/

/-- The second pairing: `i ↔ (m-1) - i` over `range m`, giving `(m-1) ∣ 2∑`. -/
theorem two_mul_sum_dvd_pred {m k : ℕ} (hk : Odd k) :
    (m - 1) ∣ 2 * ∑ i ∈ Finset.range m, i ^ k := by
  have hrefl : ∑ i ∈ Finset.range m, i ^ k
      = ∑ i ∈ Finset.range m, (m - 1 - i) ^ k :=
    (Finset.sum_range_reflect (fun i => i ^ k) m).symm
  have hsum : 2 * ∑ i ∈ Finset.range m, i ^ k
      = ∑ i ∈ Finset.range m, (i ^ k + (m - 1 - i) ^ k) := by
    rw [Finset.sum_add_distrib, ← hrefl, two_mul]
  rw [hsum]
  refine Finset.dvd_sum fun i hi => ?_
  have hi' : i ≤ m - 1 := by have := Finset.mem_range.mp hi; omega
  exact pair_dvd hk hi'

private theorem one_add_two_pow_lt : ∀ k : ℕ, 2 ≤ k → 1 + 2 ^ k < 3 ^ k := by
  intro k
  induction k with
  | zero => omega
  | succ n ih =>
      intro h
      rcases Nat.lt_or_ge n 2 with hn | hn
      · interval_cases n
        · omega
        · norm_num
      · have hih := ih (by omega)
        have h2 : (2 : ℕ) ^ (n + 1) = 2 * 2 ^ n := by ring
        have h3 : (3 : ℕ) ^ (n + 1) = 3 * 3 ^ n := by ring
        omega

/-- **Moser's theorem for odd exponents.** For odd `k ≥ 2` the Erdős–Moser
equation `1^k + ⋯ + (m-1)^k = m^k` has no solution with `m ≥ 2`.

Both pairings apply to a solution, so `m(m-1) ∣ 2m^k`; cancelling `m` and
using `gcd(m-1, m) = 1` leaves `m - 1 ∣ 2`. That bounds `m` by 3, and neither
`m = 2` (which needs `2^k = 1`) nor `m = 3` (which needs `3^k = 1 + 2^k`)
survives. Together with `k_eq_one_case` this settles every odd exponent. -/
theorem no_solution_odd {m k : ℕ} (hm : 2 ≤ m) (hk : Odd k) (hk2 : 2 ≤ k) :
    ∑ i ∈ Finset.range m, i ^ k ≠ m ^ k := by
  intro heq
  obtain ⟨t, rfl⟩ : ∃ t, m = t + 1 := ⟨m - 1, by omega⟩
  -- write k = j + 1 up front, so `k - 1` never appears
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  have ht : 1 ≤ t := by omega
  have h1 : (t + 1) ∣ 2 * ∑ i ∈ Finset.range (t + 1), i ^ (j + 1) :=
    two_mul_sum_dvd (by omega) hk
  have h2 : t ∣ 2 * ∑ i ∈ Finset.range (t + 1), i ^ (j + 1) := by
    simpa using two_mul_sum_dvd_pred (m := t + 1) hk
  have hcop : Nat.Coprime t (t + 1) := by simp
  have hmul : t * (t + 1) ∣ 2 * (t + 1) ^ (j + 1) := by
    rw [← heq]
    exact Nat.Coprime.mul_dvd_of_dvd_of_dvd hcop h2 h1
  -- cancel one factor of (t+1)
  have hstep : (t + 1) * t ∣ (t + 1) * (2 * (t + 1) ^ j) := by
    have hre : (t + 1) * (2 * (t + 1) ^ j) = 2 * (t + 1) ^ (j + 1) := by ring
    rw [hre, mul_comm (t + 1) t]
    exact hmul
  have hdvd : t ∣ 2 * (t + 1) ^ j :=
    (mul_dvd_mul_iff_left (a := t + 1) (by omega)).mp hstep
  have ht2 : t ∣ 2 := (Nat.Coprime.dvd_of_dvd_mul_right (hcop.pow_right _)) hdvd
  have htle : t ≤ 2 := Nat.le_of_dvd (by omega) ht2
  have hj : 1 ≤ j := by omega
  interval_cases t
  · -- m = 2: the sum is 1, but 2^k >= 4
    rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_zero] at heq
    have h4 : 2 ^ 2 ≤ 2 ^ (j + 1) := Nat.pow_le_pow_right (by omega) (by omega)
    simp at heq
    omega
  · -- m = 3: the sum is 1 + 2^k, and 1 + 2^k < 3^k
    rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ,
      Finset.sum_range_zero] at heq
    have hlt := one_add_two_pow_lt (j + 1) (by omega)
    simp at heq
    omega

end OpenProblems.ErdosMoser
