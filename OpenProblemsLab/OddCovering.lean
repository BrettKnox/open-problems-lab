import Mathlib.Data.Finset.Basic
import Mathlib.Data.Set.Function
import Mathlib.Data.Int.Basic
import Mathlib.Algebra.Ring.Parity

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

end OpenProblems.OddCovering
