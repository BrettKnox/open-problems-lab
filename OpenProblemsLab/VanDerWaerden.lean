import Mathlib.Order.Lattice.Nat
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Finset.Lattice.Fold
import OpenProblemsLab.VdWData

/-!
# Van der Waerden number W(2,7)

`W(r, k)` is the least `N` such that every `r`-coloring of `{1, …, N}`
contains a monochromatic `k`-term arithmetic progression (finite by van der
Waerden's theorem). Exactly six nontrivial 2-color values are known; the last
was `W(2,6) = 1132` (Kouril–Paul 2008, SAT). `W(2,7)` is unknown; best lower
bound `W(2,7) > 3703` (Rabung–Lotts, E-JC 19(2) #P35, verified at source).

Status 2026-08-20: OPEN. Quiet — occasional lower-bound papers. Not in
formal-conjectures.

## What is proved here

* **`not_hasVdW_2_7_3703`** — an explicit 2-coloring of `{1, …, 3703}` has no
  monochromatic 7-term AP (certificate in `VdWData.lean`, checked by
  `native_decide`; independently verified with negative controls in
  `computations/vanderwaerden/`). This is the full content of the published
  record `W(2,7) > 3703`.
* **`not_hasVdW_2_6_1131`** — likewise for `W(2,6)`: the lower half of the
  exact value `W(2,6) = 1132`.
* `hasVdW_mono` and the conditional bounds `w26_lower`/`w27_lower`: mathlib
  has no proof of van der Waerden's theorem yet, so `{N | HasVdW r k N}` is
  not known (in mathlib) to be nonempty, and `W` as an `sInf` could
  degenerate; the certificate theorems above carry the unconditional content.

Attack lanes: lower-bound records via SAT + cyclic-zipper constructions
(cheap, publishable); exact determination is currently infeasible. Also:
formalize van der Waerden's theorem itself (absent from mathlib).
-/

namespace OpenProblems.VanDerWaerden

/-- Every `r`-coloring of `{1, …, N}` has a monochromatic `k`-term AP. -/
def HasVdW (r k N : ℕ) : Prop :=
  ∀ c : ℕ → Fin r, ∃ a d : ℕ, 0 < a ∧ 0 < d ∧ a + (k - 1) * d ≤ N ∧
    ∀ i : ℕ, i < k → c (a + i * d) = c a

/-- The van der Waerden number `W(r, k)`. -/
noncomputable def W (r k : ℕ) : ℕ := sInf {N | HasVdW r k N}

/-- A larger interval only makes monochromatic APs easier to find. -/
theorem hasVdW_mono {r k N M : ℕ} (hNM : N ≤ M) (h : HasVdW r k N) : HasVdW r k M := by
  intro c
  obtain ⟨a, d, ha, hd, hle, hm⟩ := h c
  exact ⟨a, d, ha, hd, le_trans hle hNM, hm⟩

/-- The Rabung–Lotts certificate as a coloring (positions are 1-based). -/
def c27 : ℕ → Fin 2 := fun n => if w27data.getD (n - 1) false then 1 else 0

/-- The Kouril–Paul-length certificate as a coloring. -/
def c26 : ℕ → Fin 2 := fun n => if w26data.getD (n - 1) false then 1 else 0

/-- Bounded, decidable form of "the coloring `f` has a monochromatic `k`-AP
inside `{1, …, N}`". -/
def BadAP (f : ℕ → Fin 2) (k N : ℕ) : Prop :=
  ∃ a ∈ Finset.range (N + 1), ∃ d ∈ Finset.range (N + 1),
    0 < a ∧ 0 < d ∧ a + (k - 1) * d ≤ N ∧
      ∀ i ∈ Finset.range k, f (a + i * d) = f a

theorem c27_no_badAP : ¬ BadAP c27 7 3703 := by
  unfold BadAP c27
  native_decide

theorem c26_no_badAP : ¬ BadAP c26 6 1131 := by
  unfold BadAP c26
  native_decide

/-- **The published record `W(2,7) > 3703`, machine-checked**: the explicit
coloring `c27` of `{1, …, 3703}` has no monochromatic 7-term AP. -/
theorem not_hasVdW_2_7_3703 : ¬ HasVdW 2 7 3703 := by
  intro h
  obtain ⟨a, d, ha, hd, hle, hm⟩ := h c27
  exact c27_no_badAP ⟨a, Finset.mem_range.mpr (by omega), d, Finset.mem_range.mpr (by omega),
    ha, hd, hle, fun i hi => hm i (Finset.mem_range.mp hi)⟩

/-- **The lower half of `W(2,6) = 1132`, machine-checked**: the explicit
coloring `c26` of `{1, …, 1131}` has no monochromatic 6-term AP. -/
theorem not_hasVdW_2_6_1131 : ¬ HasVdW 2 6 1131 := by
  intro h
  obtain ⟨a, d, ha, hd, hle, hm⟩ := h c26
  exact c26_no_badAP ⟨a, Finset.mem_range.mpr (by omega), d, Finset.mem_range.mpr (by omega),
    ha, hd, hle, fun i hi => hm i (Finset.mem_range.mp hi)⟩

/-- Conditional on van der Waerden's theorem for `(2,7)` — which mathlib does
not yet have — the certificate gives `3704 ≤ W 2 7`. -/
theorem w27_lower (hne : ∃ N, HasVdW 2 7 N) : 3704 ≤ W 2 7 := by
  by_contra hlt
  push Not at hlt
  have hmem : HasVdW 2 7 (W 2 7) := Nat.sInf_mem hne
  exact not_hasVdW_2_7_3703 (hasVdW_mono (by omega) hmem)

/-- Conditional on van der Waerden's theorem for `(2,6)`: `1132 ≤ W 2 6`. -/
theorem w26_lower (hne : ∃ N, HasVdW 2 6 N) : 1132 ≤ W 2 6 := by
  by_contra hlt
  push Not at hlt
  have hmem : HasVdW 2 6 (W 2 6) := Nat.sInf_mem hne
  exact not_hasVdW_2_6_1131 (hasVdW_mono (by omega) hmem)

/-- **Open problem**: determine `W(2,7)`. Any proof of `¬ HasVdW 2 7 N` for
`N > 3703` (new lower bound) or of `HasVdW 2 7 N` for concrete `N` (upper
bound) is progress. -/
def w27Improvement (N : ℕ) : Prop := 3704 ≤ N ∧ ¬ HasVdW 2 7 N

end OpenProblems.VanDerWaerden
