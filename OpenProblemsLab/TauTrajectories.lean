import Mathlib.NumberTheory.Divisors

/-!
# Erdős problem #414: trajectories of n ↦ n + τ(n)

Iterate `h(n) = n + τ(n)` where `τ(n)` is the number of divisors of `n`.
Question (Spiro; discussed by Erdős–Graham 1980, who believed yes): do the
trajectories of any two starting points `m, n ≥ 2` eventually merge?

Status 2026-08-19: OPEN. erdosproblems.com/414 — essentially zero literature
since 1980, nobody registered as working on it. OEIS A064491.

Attack lanes: large-scale trajectory-merging computation (none published);
structural analysis via parity of τ (τ odd iff square).
-/

namespace OpenProblems.TauTrajectories

/-- One step: `n ↦ n + τ(n)` where `τ` counts divisors. -/
def step (n : ℕ) : ℕ := n + n.divisors.card

/-- **Open question** (EP #414): for all `m, n ≥ 2` the `step`-trajectories
meet, i.e. `step^[i] m = step^[j] n` for some `i, j`. (The map is
deterministic and strictly increasing on `n ≥ 2`, so meeting once means
merged forever.) -/
def trajectoriesMerge : Prop :=
  ∀ m n : ℕ, 2 ≤ m → 2 ≤ n → ∃ i j : ℕ, step^[i] m = step^[j] n

end OpenProblems.TauTrajectories
