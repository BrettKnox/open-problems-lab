import Mathlib.Algebra.BigOperators.Group.Finset.Basic

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

end OpenProblems.ErdosMoser
