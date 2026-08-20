import OpenProblemsLab.IntegerComplexity
import OpenProblemsLab.TauTrajectories
import OpenProblemsLab.Superpermutations
import OpenProblemsLab.DistinctSubsetSums
import OpenProblemsLab.ErdosMoser
import OpenProblemsLab.LehmerTotient
import OpenProblemsLab.VanDerWaerden
import Mathlib.Tactic.NormNum
import Mathlib.Data.Fintype.Perm

/-!
# Sanity checks

A formal statement that compiles can still be vacuous or say the wrong thing.
These are concrete witnesses and small decidable instances that fail loudly if
a definition drifts from its intended meaning. Kept cheap on purpose.
-/

namespace OpenProblems.Sanity

open OpenProblems

/-- `(1+1)·((1+1)+1) = 6` uses five 1s, so `‖6‖ ≤ 5` (in fact `= 5`). -/
example : IntegerComplexity.complexity 6 ≤ 5 :=
  Nat.sInf_le ⟨.mul (.add .one .one) (.add (.add .one .one) .one), rfl, rfl⟩

/-- `τ(6) = 4`, so the Erdős #414 map sends `6 ↦ 10`. -/
example : TauTrajectories.step 6 = 10 := by decide

/-- `[0,1,0]` contains both permutations of `Fin 2` as contiguous blocks. -/
example : Superpermutations.IsSuperperm 2 [0, 1, 0] := by
  intro p
  fin_cases p <;> decide

/-- The subset-sum condition really detects collisions: `{1,2}` and `{3}` both
sum to 3, so `{1,2,3}` does not have distinct subset sums. -/
example : ¬ DistinctSubsetSums.HasDistinctSubsetSums {1, 2, 3} := by
  intro h
  exact absurd (h {1, 2} {3} (by decide) (by decide) (by decide)) (by decide)

/-- The known Erdős–Moser solution `1 + 2 = 3` satisfies the equation, so the
conjecture's hypothesis is satisfiable (it is not vacuously true). -/
example : (∑ i ∈ Finset.range 3, i ^ 1) = 3 ^ 1 := by decide

/-- Lehmer's condition holds for the prime 7 (`φ(7) = 6 ∣ 6`). -/
example : Nat.totient 7 ∣ 7 - 1 := by decide

set_option maxRecDepth 40000 in
/-- Lehmer's conjecture verified on `2 ≤ n ≤ 100`. -/
example : ∀ n ∈ Finset.Icc 2 100, Nat.totient n ∣ n - 1 → Nat.Prime n := by decide

/-- A 1-coloring of `{1,2,3}` has a monochromatic 2-term AP (`a = d = 1`). -/
example : VanDerWaerden.HasVdW 1 2 3 := fun c => ⟨1, 1, by norm_num, by norm_num, by
  norm_num, by intro i _; simp [Fin.ext_iff]⟩

end OpenProblems.Sanity
