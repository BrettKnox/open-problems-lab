import Mathlib.GroupTheory.Perm.Basic
import Mathlib.Data.List.OfFn
import Mathlib.Data.List.Infix
import Mathlib.Order.Lattice.Nat
import Mathlib.Data.Fintype.Perm
import OpenProblemsLab.SuperpermData

/-!
# Minimal superpermutation length for n = 6

A superpermutation on `n` symbols is a word over `Fin n` containing every
permutation of the symbols as a contiguous substring. `L n` denotes the
minimal length. Known: `L n ≥ n! + (n-1)! + (n-2)! + n - 3` for `n ≥ 3`
(Houston–Egan–anonymous, 2018-19), giving `867 ≤ L 6`; Houston's 2014 word
gives `L 6 ≤ 872`. Exact value open; `L n` unknown for all n ≥ 6.

Status 2026-08-19: OPEN. Dormant since ~2021 (a minimality claim on the
mailing list died unverified). OEIS A180632. Not in formal-conjectures.

## What is proved here

* `houston872_isSuperperm` / **`L_six_le`** — Houston's explicit 872-symbol
  word is a superpermutation, so `L 6 ≤ 872`. The word is data
  (`SuperpermData.lean`), checked by `native_decide` (trust note: this relies
  on the compiled evaluator, not the kernel; the word is additionally verified
  by an independent Python checker in `computations/superpermutations/`).

Attack lanes: rule out length 871 by modern SAT with proof logging (untried
with CaDiCaL-era tooling); improve n = 7 bounds; formalize the 867 lower
bound.
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

/-- Known bounds; the upper half is proved below (`L_six_le`), the lower half
(`867 ≤ L 6`, Houston–Egan) is a formalization target. -/
def sixSymbolsBounds : Prop := 867 ≤ L 6 ∧ L 6 ≤ 872

/-- Houston's word contains every permutation of six symbols as an infix.
Verified by the compiled evaluator (`native_decide`); independently checked in
`computations/superpermutations/verify_word.py`. -/
theorem houston872_isSuperperm : IsSuperperm 6 houston872 := by
  unfold IsSuperperm
  native_decide

set_option maxRecDepth 4000 in
theorem houston872_length : houston872.length = 872 := by decide

/-- **`L 6 ≤ 872`** — the sharpest known upper bound, via Houston's word.
Because the defining set is now known nonempty, `L 6` is a genuine minimum
attained by some word. -/
theorem L_six_le : L 6 ≤ 872 :=
  Nat.sInf_le ⟨houston872, houston872_length, houston872_isSuperperm⟩

end OpenProblems.Superpermutations
