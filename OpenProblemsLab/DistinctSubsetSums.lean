import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Real.Basic

/-!
# Erdős distinct subset sums conjecture (Erdős problem #1, $500)

If a finite set `S` of positive integers has all `2^|S|` subset sums
distinct, then `max S ≥ c · 2^|S|` for some absolute `c > 0`.

Status 2026-08-19: OPEN. Best lower bound: `max S ≥ (√(2/π) − o(1)) · 2^n/√n`
(Dubroff–Fox–Xu 2021, matching Elkies–Gleason); nobody has beaten `2^n/√n`
in 70 years. Best construction: `0.22002 · 2^n` (Bohman, refining
Conway–Guy). In formal-conjectures (`ErdosProblems/1.lean`); this statement
is written independently.

Attack lanes: beat Bohman's constant by computer search over Conway–Guy-type
constructions; formalize the short Dubroff–Fox–Xu proof.
-/

namespace OpenProblems.DistinctSubsetSums

/-- All subset sums of `S` are distinct. -/
def HasDistinctSubsetSums (S : Finset ℕ) : Prop :=
  ∀ A B : Finset ℕ, A ⊆ S → B ⊆ S → A.sum id = B.sum id → A = B

/-- **Open conjecture** (Erdős, $500): distinct subset sums force an element
of size `≥ c · 2^|S|` for an absolute constant `c > 0`. -/
def conjecture : Prop :=
  ∃ c : ℝ, 0 < c ∧ ∀ S : Finset ℕ, S.Nonempty → HasDistinctSubsetSums S →
    ∃ x ∈ S, c * 2 ^ S.card ≤ (x : ℝ)

/-! ### The Conway–Guy witness

The 16-element Conway–Guy set (built from OEIS A005318: `a_i = u₁₆ − u₁₆₋ᵢ`),
whose subset sums are pairwise distinct while its maximum is only
`17305 < 2¹⁵ = 32768` — beating the trivial `{2^i}` construction (max
`2¹⁵`) by a factor of ~1.9 and showing why Erdős's conjectured `c·2ⁿ` is the
interesting scale. Distinctness is checked by `native_decide` (flagged; the
set is independently verified, with gates and a negative control, in
`computations/subset_sums/`). -/

/-- The 16-element Conway–Guy set. -/
def conwayGuy16 : Finset ℕ :=
  {8498, 12821, 15021, 16141, 16711, 16996, 17144, 17221, 17261, 17281,
   17292, 17298, 17301, 17303, 17304, 17305}

theorem conwayGuy16_card : conwayGuy16.card = 16 := by decide

theorem conwayGuy16_distinct : HasDistinctSubsetSums conwayGuy16 := by
  -- all 2^16 subset sums are distinct iff the image of `sum` on the powerset
  -- has full cardinality; counting 65536 sums is cheap, comparing all pairs
  -- is not
  have himg : (conwayGuy16.powerset.image (fun A => A.sum id)).card
      = conwayGuy16.powerset.card := by
    unfold conwayGuy16
    native_decide
  have hinj := Finset.injOn_of_card_image_eq himg
  intro A B hA hB hsum
  exact hinj (Finset.mem_coe.mpr (Finset.mem_powerset.mpr hA))
    (Finset.mem_coe.mpr (Finset.mem_powerset.mpr hB)) hsum

/-- The witness statement: a 16-element set with distinct subset sums whose
maximum is below `2^15` — the trivial powers-of-two bound is not optimal. -/
theorem conwayGuy16_beats_powers_of_two :
    HasDistinctSubsetSums conwayGuy16 ∧ conwayGuy16.card = 16 ∧
      ∀ x ∈ conwayGuy16, x < 2 ^ 15 :=
  ⟨conwayGuy16_distinct, conwayGuy16_card, by decide⟩

end OpenProblems.DistinctSubsetSums
