import Mathlib.Data.Finset.Basic
import Mathlib.Data.Nat.ModEq
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Set.Function
import Mathlib.Data.Int.Basic
import Mathlib.Algebra.Ring.Parity
import Mathlib.Tactic.Ring

/-!
# Odd covering systems (Erdős–Selfridge; Erdős problem #7)

A covering system is a finite set of congruences `a_i (mod m_i)` whose union
is all of ℤ. Question: does one exist with all moduli odd, distinct, and > 1?
Erdős offered $25 for "no", Selfridge $2000 for an explicit example.

Status 2026-08-19: OPEN. erdosproblems.com/7. Known: no odd *squarefree*
covering exists, and any odd covering has lcm divisible by 9 or 15
(Balister–Bollobás–Morris–Sahasrabudhe–Tiba 2022); some modulus divisible by
2 or 3 in general systems (Hough–Nielsen 2019). In formal-conjectures
(`ErdosProblems/7.lean`); this statement is written independently.

## What is proved here

* `IsCovering` — general covering systems (no oddness restriction).
* **`isCovering_of_covers_period`** — the finite-check reduction: if every
  modulus divides `L > 0` and every residue in `{0, …, L−1}` is covered, the
  system covers all of ℤ. This is the formal warrant for verifying covering
  systems (and for the searches of OC-2) by one finite pass over a period.
* `classic_isCovering` — the textbook system
  `{0 (2), 0 (3), 1 (4), 5 (6), 7 (12)}` covers ℤ, via the reduction plus a
  kernel `decide` over the period 12. The first machine-checked covering
  system in this repository — and `classic_not_odd` notes it is (necessarily,
  if Erdős was right) not an odd system.

Attack lanes: computational search over admissible lcm shapes (the 9-or-15
theorem sharply limits them); LP/density bounds on how close odd moduli can
get to covering.
-/

namespace OpenProblems.OddCovering

/-- `S` is an odd covering system: finitely many residue classes
`a mod m` with all `m` odd, distinct, and ≥ 3, covering every integer. -/
def IsOddCovering (S : Finset (ℕ × ℕ)) : Prop :=
  (∀ p ∈ S, Odd p.2 ∧ 3 ≤ p.2) ∧
  Set.InjOn (fun p : ℕ × ℕ => p.2) ↑S ∧
  ∀ n : ℤ, ∃ p ∈ S, (p.2 : ℤ) ∣ n - (p.1 : ℤ)

/-- **Open problem** (Erdős's side of the bet): no odd covering system
exists. The negation (an explicit example) resolves it the other way. -/
def noOddCovering : Prop := ¬ ∃ S : Finset (ℕ × ℕ), IsOddCovering S

/-! ### Covering systems in general, and the finite-check reduction -/

/-- `S` is a covering system: the residue classes `a mod m` (with `m ≥ 1`)
cover every integer. -/
def IsCovering (S : Finset (ℕ × ℕ)) : Prop :=
  (∀ p ∈ S, 1 ≤ p.2) ∧ ∀ n : ℤ, ∃ p ∈ S, (p.2 : ℤ) ∣ n - (p.1 : ℤ)

/-- **The finite-check reduction**: if every modulus divides a common period
`L > 0` and every integer in `{0, …, L−1}` is covered, then every integer is
covered. Every computational verification of a covering system rests on this. -/
theorem isCovering_of_covers_period (S : Finset (ℕ × ℕ)) (L : ℕ) (hL : 0 < L)
    (hdvd : ∀ p ∈ S, 1 ≤ p.2 ∧ (p.2 : ℤ) ∣ (L : ℤ))
    (hcover : ∀ r : ℕ, r < L → ∃ p ∈ S, (p.2 : ℤ) ∣ (r : ℤ) - (p.1 : ℤ)) :
    IsCovering S := by
  refine ⟨fun p hp => (hdvd p hp).1, fun n => ?_⟩
  -- reduce `n` to its residue `r = n mod L`, which the hypothesis covers
  have hLpos : (0 : ℤ) < (L : ℤ) := by exact_mod_cast hL
  set r : ℤ := n % (L : ℤ) with hr
  have hr0 : 0 ≤ r := Int.emod_nonneg n (by omega)
  have hrL : r < (L : ℤ) := Int.emod_lt_of_pos n hLpos
  obtain ⟨rn, hrn⟩ : ∃ rn : ℕ, r = (rn : ℤ) := ⟨r.toNat, (Int.toNat_of_nonneg hr0).symm⟩
  have hrnL : rn < L := by omega
  obtain ⟨p, hp, hpd⟩ := hcover rn hrnL
  refine ⟨p, hp, ?_⟩
  -- `m ∣ L ∣ n − r` and `m ∣ r − a`, so `m ∣ n − a`
  have h1 : (L : ℤ) ∣ n - r := by
    refine ⟨n / (L : ℤ), ?_⟩
    rw [hr, Int.emod_def]
    ring
  have h2 : (p.2 : ℤ) ∣ n - r := ((hdvd p hp).2).trans h1
  have h3 : (p.2 : ℤ) ∣ r - (p.1 : ℤ) := hrn ▸ hpd
  obtain ⟨c2, hc2⟩ := h2
  obtain ⟨c3, hc3⟩ := h3
  refine ⟨c2 + c3, ?_⟩
  have : n - (p.1 : ℤ) = (n - r) + (r - (p.1 : ℤ)) := by ring
  rw [this, hc2, hc3, mul_add]

/-- The textbook covering system `0 (2), 0 (3), 1 (4), 5 (6), 7 (12)`. -/
def classic : Finset (ℕ × ℕ) := {(0, 2), (0, 3), (1, 4), (5, 6), (7, 12)}

/-- The classic five-congruence system covers ℤ (finite check over the
period 12, justified by `isCovering_of_covers_period`). -/
theorem classic_isCovering : IsCovering classic := by
  apply isCovering_of_covers_period classic 12 (by omega)
  · decide
  · decide

/-- The classic system is not an odd covering system — as Erdős conjectured
none can be, four of its moduli being even. -/
theorem classic_not_odd : ¬ IsOddCovering classic := by
  rintro ⟨hodd, -, -⟩
  have := hodd (0, 2) (by decide)
  simp at this



/-! ### The density bound

The engine behind the abundance screen used by the searches in
`computations/odd_covering`. If the classes cover one full period, the sum of
`L / mᵢ` is at least `L` — i.e. `∑ 1/mᵢ ≥ 1`. Applied to the *maximal* system
at lcm `L` (every divisor `m > 1` used once, which is WLOG optimal) this says
`σ(L) ≥ 2L`: **the lcm of any covering system is an abundant number**, so an
odd covering system's lcm must be an odd abundant number. -/

open Finset in
/-- If every modulus divides `L` and the classes cover `{0, …, L−1}`, then
`L ≤ ∑ L / mᵢ`. Counting: the period is the union of the classes, and the
class of `a mod m` meets a period of length `L` in at most `L / m` points. -/
theorem card_le_sum_of_covers_period {S : Finset (ℕ × ℕ)} {L : ℕ}
    (hdvd : ∀ p ∈ S, p.2 ∣ L)
    (hcov : ∀ n < L, ∃ p ∈ S, (p.2 : ℤ) ∣ (n : ℤ) - (p.1 : ℤ)) :
    L ≤ ∑ p ∈ S, L / p.2 := by
  classical
  set f : ℕ × ℕ → Finset ℕ :=
    fun p => (range L).filter (fun n => n % p.2 = p.1 % p.2) with hf
  have hsub : range L ⊆ S.biUnion f := by
    intro n hn
    obtain ⟨p, hp, hd⟩ := hcov n (mem_range.mp hn)
    exact mem_biUnion.mpr ⟨p, hp, mem_filter.mpr ⟨hn, (Nat.modEq_iff_dvd.mpr hd).symm⟩⟩
  have hcard : ∀ p ∈ S, (f p).card ≤ L / p.2 := by
    intro p hp
    have : (f p).card ≤ (range (L / p.2)).card := by
      refine card_le_card_of_injOn (fun n => n / p.2) ?_ ?_
      · intro n hn
        simp only [hf, coe_filter, Set.mem_ofPred_eq, mem_range] at hn
        exact mem_range.mpr (Nat.div_lt_div_of_lt_of_dvd (hdvd p hp) hn.1)
      · intro a ha b hb hab
        simp only [hf, coe_filter, Set.mem_ofPred_eq, mem_range] at ha hb
        have hab' : a / p.2 = b / p.2 := hab
        have hm : a % p.2 = b % p.2 := by rw [ha.2, hb.2]
        calc a = p.2 * (a / p.2) + a % p.2 := (Nat.div_add_mod a p.2).symm
          _ = p.2 * (b / p.2) + b % p.2 := by rw [hab', hm]
          _ = b := Nat.div_add_mod b p.2
    simpa using this
  calc L = (range L).card := (card_range L).symm
    _ ≤ (S.biUnion f).card := card_le_card hsub
    _ ≤ ∑ p ∈ S, (f p).card := card_biUnion_le
    _ ≤ ∑ p ∈ S, L / p.2 := sum_le_sum hcard

/-! ### Exact class counts, and the forced overlap of coprime moduli

The density bound above throws away the fact that classes with *coprime*
moduli always meet. That overlap is what the computational screen in
`computations/odd_covering` is built on: it is forced by CRT, no matter which
residues the system picks, so it can be subtracted from the density budget
before any search happens. These two lemmas are its formal core. -/

open Finset in
/-- The class `a mod m` meets a period of length `L` in **exactly** `L / m`
points, when `m ∣ L`. (The density bound only needed `≤`.) -/
theorem card_class_eq {L m a : ℕ} (hm : m ∣ L) (hm0 : 0 < m) :
    ((range L).filter (fun n => n % m = a % m)).card = L / m := by
  classical
  have hlt : a % m < m := Nat.mod_lt _ hm0
  refine (card_nbij' (fun n => n / m) (fun k => a % m + m * k) ?_ ?_ ?_ ?_).trans
    (card_range _)
  · intro n hn
    simp only [coe_filter, Set.mem_ofPred_eq, mem_range] at hn
    exact mem_coe.mpr (mem_range.mpr (Nat.div_lt_div_of_lt_of_dvd hm hn.1))
  · intro k hk
    have hk' : k < L / m := mem_range.mp (mem_coe.mp hk)
    refine mem_coe.mpr (mem_filter.mpr ⟨mem_range.mpr ?_, ?_⟩)
    · calc a % m + m * k < m + m * k := by omega
        _ = m * (k + 1) := by ring
        _ ≤ m * (L / m) := Nat.mul_le_mul_left _ hk'
        _ = L := Nat.mul_div_cancel' hm
    · rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hlt]
  · intro n hn
    simp only [coe_filter, Set.mem_ofPred_eq, mem_range] at hn
    calc a % m + m * (n / m) = n % m + m * (n / m) := by rw [hn.2]
      _ = n := Nat.mod_add_div n m
  · intro k hk
    show (a % m + m * k) / m = k
    rw [Nat.add_mul_div_left _ _ hm0, Nat.div_eq_of_lt hlt, Nat.zero_add]

open Finset in
/-- **Forced overlap.** If `m₁` and `m₂` are coprime divisors of `L`, then the
classes `a₁ mod m₁` and `a₂ mod m₂` meet in exactly `L / (m₁ * m₂)` points of
a period — *whatever residues are chosen*. There is no way to place two
coprime congruences disjointly, which is why a system of pairwise coprime
moduli wastes a predictable amount of its density budget. -/
theorem card_inter_coprime {L m₁ m₂ a₁ a₂ : ℕ} (hco : Nat.Coprime m₁ m₂)
    (h₁ : m₁ ∣ L) (h₂ : m₂ ∣ L) (hp₁ : 0 < m₁) (hp₂ : 0 < m₂) :
    ((range L).filter
        (fun n => n % m₁ = a₁ % m₁ ∧ n % m₂ = a₂ % m₂)).card
      = L / (m₁ * m₂) := by
  classical
  obtain ⟨c, hc₁, hc₂⟩ := Nat.chineseRemainder hco a₁ a₂
  have key : ∀ n : ℕ, (n % m₁ = a₁ % m₁ ∧ n % m₂ = a₂ % m₂)
      ↔ n % (m₁ * m₂) = c % (m₁ * m₂) := by
    intro n
    constructor
    · rintro ⟨e₁, e₂⟩
      exact Nat.modEq_and_modEq_iff_modEq_mul hco |>.mp
        ⟨e₁.trans hc₁.symm, e₂.trans hc₂.symm⟩
    · intro e
      have := Nat.modEq_and_modEq_iff_modEq_mul hco |>.mpr e
      exact ⟨this.1.trans hc₁, this.2.trans hc₂⟩
  simp only [key]
  exact card_class_eq (Nat.Coprime.mul_dvd_of_dvd_of_dvd hco h₁ h₂)
    (Nat.mul_pos hp₁ hp₂)

open Finset in
/-- **The screen, formally.** A covering system whose moduli divide `L` and
which contains two *coprime* moduli must pay for their forced overlap: the
density budget `∑ L / mᵢ` has to cover `L` **plus** `L / (m₁ m₂)`.

This is the inequality the computational screen applies (there, summed over a
matching of coprime pairs and iterated into coprime groups). It is strictly
stronger than `card_le_sum_of_covers_period`, and the extra term is not a
choice the system can avoid — `card_inter_coprime` shows the overlap is the
same whatever residues are picked. -/
theorem card_le_sum_sub_overlap {S : Finset (ℕ × ℕ)} {L : ℕ} {p₁ p₂ : ℕ × ℕ}
    (hdvd : ∀ p ∈ S, p.2 ∣ L) (hpos : ∀ p ∈ S, 0 < p.2)
    (h₁ : p₁ ∈ S) (h₂ : p₂ ∈ S) (hne : p₁ ≠ p₂)
    (hco : Nat.Coprime p₁.2 p₂.2)
    (hcov : ∀ n < L, ∃ p ∈ S, (p.2 : ℤ) ∣ (n : ℤ) - (p.1 : ℤ)) :
    L + L / (p₁.2 * p₂.2) ≤ ∑ p ∈ S, L / p.2 := by
  classical
  set f : ℕ × ℕ → Finset ℕ :=
    fun p => (range L).filter (fun n => n % p.2 = p.1 % p.2) with hf
  have hcard : ∀ p ∈ S, (f p).card = L / p.2 :=
    fun p hp => card_class_eq (hdvd p hp) (hpos p hp)
  -- the period is covered
  have hsub : range L ⊆ S.biUnion f := by
    intro n hn
    obtain ⟨p, hp, hd⟩ := hcov n (mem_range.mp hn)
    exact mem_biUnion.mpr ⟨p, hp, mem_filter.mpr ⟨hn, (Nat.modEq_iff_dvd.mpr hd).symm⟩⟩
  -- split off the two coprime moduli
  set R := S \ {p₁, p₂} with hR
  have hpair : ({p₁, p₂} : Finset (ℕ × ℕ)) ⊆ S := by
    intro x hx
    rcases mem_insert.mp hx with rfl | hx
    · exact h₁
    · rw [mem_singleton] at hx; exact hx ▸ h₂
  have hsplit : S.biUnion f ⊆ (f p₁ ∪ f p₂) ∪ R.biUnion f := by
    intro x hx
    obtain ⟨p, hp, hxp⟩ := mem_biUnion.mp hx
    by_cases e₁ : p = p₁
    · exact mem_union_left _ (mem_union_left _ (e₁ ▸ hxp))
    by_cases e₂ : p = p₂
    · exact mem_union_left _ (mem_union_right _ (e₂ ▸ hxp))
    refine mem_union_right _ (mem_biUnion.mpr ⟨p, ?_, hxp⟩)
    simp [hR, hp, e₁, e₂]
  -- the overlap is forced
  have hinter : (f p₁ ∩ f p₂).card = L / (p₁.2 * p₂.2) := by
    have : f p₁ ∩ f p₂ = (range L).filter
        (fun n => n % p₁.2 = p₁.1 % p₁.2 ∧ n % p₂.2 = p₂.1 % p₂.2) := by
      rw [hf]; exact (filter_and _ _ _).symm
    rw [this]
    exact card_inter_coprime hco (hdvd p₁ h₁) (hdvd p₂ h₂) (hpos p₁ h₁) (hpos p₂ h₂)
  -- count
  have hsum : ∑ p ∈ S, L / p.2 = (L / p₁.2 + L / p₂.2) + ∑ p ∈ R, L / p.2 := by
    rw [hR, ← sum_sdiff hpair, sum_pair hne]
    ring
  have hRcard : (R.biUnion f).card ≤ ∑ p ∈ R, L / p.2 :=
    le_trans card_biUnion_le
      (sum_le_sum fun p hp => (hcard p (mem_sdiff.mp hp).1).le)
  have hu : (f p₁ ∪ f p₂).card + (f p₁ ∩ f p₂).card = L / p₁.2 + L / p₂.2 := by
    rw [card_union_add_card_inter, hcard p₁ h₁, hcard p₂ h₂]
  calc L + L / (p₁.2 * p₂.2)
      = (range L).card + (f p₁ ∩ f p₂).card := by rw [card_range, hinter]
    _ ≤ ((f p₁ ∪ f p₂) ∪ R.biUnion f).card + (f p₁ ∩ f p₂).card := by
        exact Nat.add_le_add_right (card_le_card (hsub.trans hsplit)) _
    _ ≤ ((f p₁ ∪ f p₂).card + (R.biUnion f).card) + (f p₁ ∩ f p₂).card := by
        exact Nat.add_le_add_right (card_union_le _ _) _
    _ = ((f p₁ ∪ f p₂).card + (f p₁ ∩ f p₂).card) + (R.biUnion f).card := by ring
    _ = (L / p₁.2 + L / p₂.2) + (R.biUnion f).card := by rw [hu]
    _ ≤ (L / p₁.2 + L / p₂.2) + ∑ p ∈ R, L / p.2 := Nat.add_le_add_left hRcard _
    _ = ∑ p ∈ S, L / p.2 := hsum.symm

open Finset in
/-- The contrapositive, which is the form the computational screen applies: if
the density budget cannot pay for `L` *plus* the forced overlap of one coprime
pair, no such system covers a period.

At `L = 945` (the smallest odd abundant number, and the smallest shape the SAT
search could close — in 47 seconds) the whole budget is `∑ 945/m = 975` over
the fifteen odd divisors `> 1`, while the pair `(3, 5)` alone forces an overlap
of `945/15 = 63`. Since `945 + 63 = 1008 > 975`, no covering exists. One line
of arithmetic, no search. -/
theorem not_covers_of_budget_lt {S : Finset (ℕ × ℕ)} {L : ℕ} {p₁ p₂ : ℕ × ℕ}
    (hdvd : ∀ p ∈ S, p.2 ∣ L) (hpos : ∀ p ∈ S, 0 < p.2)
    (h₁ : p₁ ∈ S) (h₂ : p₂ ∈ S) (hne : p₁ ≠ p₂)
    (hco : Nat.Coprime p₁.2 p₂.2)
    (hbudget : ∑ p ∈ S, L / p.2 < L + L / (p₁.2 * p₂.2)) :
    ¬ ∀ n < L, ∃ p ∈ S, (p.2 : ℤ) ∣ (n : ℤ) - (p.1 : ℤ) := fun hcov =>
  absurd (card_le_sum_sub_overlap hdvd hpos h₁ h₂ hne hco hcov) (not_le.mpr hbudget)

end OpenProblems.OddCovering
