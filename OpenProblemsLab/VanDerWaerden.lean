import Mathlib.Order.Lattice.Nat
import Mathlib.Data.Fintype.Basic

/-!
# Van der Waerden number W(2,7)

`W(r, k)` is the least `N` such that every `r`-coloring of `{1, …, N}`
contains a monochromatic `k`-term arithmetic progression (finite by van der
Waerden's theorem). Exactly six nontrivial 2-color values are known; the last
was `W(2,6) = 1132` (Kouril–Paul 2008, SAT). `W(2,7)` is unknown; best lower
bound `W(2,7) ≥ 3704` (Rabung–Lotts).

Status 2026-08-19: OPEN. Quiet — occasional lower-bound papers. Not in
formal-conjectures.

Attack lanes: lower-bound records via SAT + cyclic-zipper constructions
(cheap, publishable); exact determination is currently infeasible.
-/

namespace OpenProblems.VanDerWaerden

/-- Every `r`-coloring of `{1, …, N}` has a monochromatic `k`-term AP. -/
def HasVdW (r k N : ℕ) : Prop :=
  ∀ c : ℕ → Fin r, ∃ a d : ℕ, 0 < a ∧ 0 < d ∧ a + (k - 1) * d ≤ N ∧
    ∀ i : ℕ, i < k → c (a + i * d) = c a

/-- The van der Waerden number `W(r, k)`. -/
noncomputable def W (r k : ℕ) : ℕ := sInf {N | HasVdW r k N}

/-- Known lower bound (Rabung–Lotts): some 2-coloring of `{1, …, 3703}` has
no monochromatic 7-term AP. Formal proof target (certificate checking). -/
def w27LowerBound : Prop := 3704 ≤ W 2 7

/-- **Open problem**: determine `W(2,7)`. Any proof of `N < W 2 7` for
`N ≥ 3704` (new lower bound) or of `HasVdW 2 7 N` for concrete `N` (upper
bound) is progress. -/
def w27Improvement (N : ℕ) : Prop := 3704 ≤ N ∧ N < W 2 7

end OpenProblems.VanDerWaerden
