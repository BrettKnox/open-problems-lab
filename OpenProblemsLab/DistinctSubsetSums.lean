import Mathlib.Algebra.BigOperators.Group.Finset.Basic
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

end OpenProblems.DistinctSubsetSums
