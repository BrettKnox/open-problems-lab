import Mathlib.Computability.DFA
import Mathlib.Order.Lattice.Nat
import Mathlib.Data.Nat.Log

/-!
# The separating words problem

`sep n` is the least number of DFA states sufficient to distinguish any two
distinct binary words of length `n` (some DFA of that size accepts one and
rejects the other). Known: `sep n = Ω(log n)` (folklore) and
`sep n = O(n^{1/3} log^7 n)` (Chase, STOC 2021). The conjecture is that
`O(log n)` states suffice.

Status 2026-08-19: OPEN. A claimed `O(log² n)` improvement (arXiv:2503.23184)
was withdrawn in April 2025. Quiet since Chase. Not in formal-conjectures.

Attack lanes: exact values of `sep n` for small `n` by exhaustive/SAT search
(no published table exists); improved constructions for special word classes.
-/

namespace OpenProblems.SeparatingWords

/-- `M` separates `u` and `v` iff it accepts exactly one of them. -/
def Separates {σ : Type} (M : DFA (Fin 2) σ) (u v : List (Fin 2)) : Prop :=
  ¬(u ∈ M.accepts ↔ v ∈ M.accepts)

/-- `k` states suffice for length `n`: every pair of distinct binary words of
length `n` is separated by some DFA with state set `Fin k`. -/
def SuffStates (k n : ℕ) : Prop :=
  ∀ u v : List (Fin 2), u.length = n → v.length = n → u ≠ v →
    ∃ M : DFA (Fin 2) (Fin k), Separates M u v

/-- The separation number `sep n`: the least `k` such that `k` states suffice
to separate any two distinct binary words of length `n`. -/
noncomputable def sep (n : ℕ) : ℕ := sInf {k | SuffStates k n}

/-- **Open conjecture**: `O(log n)` states suffice, i.e.
`∃ C, sep n ≤ C · log₂ n` for all `n ≥ 2`. -/
def logConjecture : Prop :=
  ∃ C : ℕ, ∀ n : ℕ, 2 ≤ n → sep n ≤ C * Nat.log 2 n

end OpenProblems.SeparatingWords
