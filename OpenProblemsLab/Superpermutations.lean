import Mathlib.GroupTheory.Perm.Basic
import Mathlib.Data.List.OfFn
import Mathlib.Data.List.Infix
import Mathlib.Order.Lattice.Nat

/-!
# Minimal superpermutation length for n = 6

A superpermutation on `n` symbols is a word over `Fin n` containing every
permutation of the symbols as a contiguous substring. `L n` denotes the
minimal length. Known: `L n = n! + (n-1)! + (n-2)! + n - 3` lower bound for
`n ≥ 3` (Houston–Egan–anonymous, 2018-19), giving `867 ≤ L 6`; Egan's
construction gives `L 6 ≤ 872`. Exact value open; `L n` unknown for all n ≥ 6.

Status 2026-08-19: OPEN. Dormant since ~2021 (a minimality claim on the
mailing list died unverified). OEIS A180632. Not in formal-conjectures.

Attack lanes: rule out length 871 by modern SAT with proof logging (untried
with CaDiCaL-era tooling); improve n = 7 bounds.
-/

namespace OpenProblems.Superpermutations

/-- `w` is a superpermutation on `n` symbols: every permutation of `Fin n`,
read as the word `[p 0, …, p (n-1)]`, is an infix of `w`. -/
def IsSuperperm (n : ℕ) (w : List (Fin n)) : Prop :=
  ∀ p : Equiv.Perm (Fin n), (List.ofFn ⇑p) <:+: w

/-- Minimal length of a superpermutation on `n` symbols. (The set is
nonempty: concatenating all `n!` permutations works.) -/
noncomputable def L (n : ℕ) : ℕ :=
  sInf {ℓ | ∃ w : List (Fin n), w.length = ℓ ∧ IsSuperperm n w}

/-- **Open question**: is Egan's 872 optimal for six symbols? Known:
`867 ≤ L 6 ≤ 872`. -/
def sixSymbols872 : Prop := L 6 = 872

/-- Known bounds, formal proof targets: `867 ≤ L 6` (Houston–Egan lower
bound) and `L 6 ≤ 872` (Egan's explicit word). -/
def sixSymbolsBounds : Prop := 867 ≤ L 6 ∧ L 6 ≤ 872

end OpenProblems.Superpermutations
