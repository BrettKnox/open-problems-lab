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

end OpenProblems.OddCovering
