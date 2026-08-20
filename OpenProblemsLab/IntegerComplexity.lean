import Mathlib.Order.Lattice.Nat
import Mathlib.Analysis.SpecialFunctions.Log.Base

/-!
# Integer complexity: ‖2^n‖ = 2n

`‖n‖` is the least number of 1s needed to write `n` using only `+`, `×`, and
parentheses (e.g. `6 = (1+1)·(1+1+1)` gives `‖6‖ ≤ 5`). Conjecture
(Rawsthorne 1989 / Guy): `‖2^n‖ = 2n` for all `n ≥ 1`. The `≤` direction is
trivial; the lower bound is wide open. Also stated: Selfridge's classical
lower bound `‖n‖ ≥ 3·log₃ n`.

Status 2026-08-19: OPEN. Verified for `2^i ≤ 2^126` (He, arXiv:2308.10301);
`‖2^k·3^ℓ‖ = 2k + 3ℓ` for all `k ≤ 48` and all `ℓ` (Altman, arXiv:1606.03635;
Altman–Arias de Reyna, arXiv:2111.00671). Essentially two active researchers.
No prior Lean formalization of the statement is known (not in
google-deepmind/formal-conjectures as of this date).

Attack lanes: extend Altman's `k ≤ 48` stability computation; extend He's
power search; formalize the defect machinery and Selfridge's bound.
-/

namespace OpenProblems.IntegerComplexity

/-- Expressions built from the constant 1 using addition and multiplication. -/
inductive OnesExpr : Type
  | one : OnesExpr
  | add : OnesExpr → OnesExpr → OnesExpr
  | mul : OnesExpr → OnesExpr → OnesExpr

/-- The value of an expression. -/
def OnesExpr.eval : OnesExpr → ℕ
  | .one => 1
  | .add a b => a.eval + b.eval
  | .mul a b => a.eval * b.eval

/-- The number of 1s used by an expression. -/
def OnesExpr.size : OnesExpr → ℕ
  | .one => 1
  | .add a b => a.size + b.size
  | .mul a b => a.size + b.size

/-- Integer complexity `‖n‖`: the least number of 1s in a `{+, ×}` expression
evaluating to `n`. (For `n = 0` no expression exists and the value is the
junk value `sInf ∅ = 0`; the notion is only used for `n ≥ 1`.) -/
noncomputable def complexity (n : ℕ) : ℕ :=
  sInf {k | ∃ e : OnesExpr, e.eval = n ∧ e.size = k}

/-- **Open conjecture** (Rawsthorne/Guy): `‖2^n‖ = 2n` for all `n ≥ 1`. -/
def powersOfTwoConjecture : Prop :=
  ∀ n : ℕ, 1 ≤ n → complexity (2 ^ n) = 2 * n

/-- Known (Selfridge): `‖n‖ ≥ 3·log₃ n` for `n ≥ 1`. A formal proof of this
is a project target. -/
def selfridgeLowerBound : Prop :=
  ∀ n : ℕ, 1 ≤ n → 3 * Real.logb 3 n ≤ complexity n

/-- Known upper half of the conjecture: `‖2^n‖ ≤ 2n` for `n ≥ 1`
(write `2 = 1+1` and multiply `n` copies). A formal proof is a project target. -/
def powersOfTwoUpper : Prop :=
  ∀ n : ℕ, 1 ≤ n → complexity (2 ^ n) ≤ 2 * n

end OpenProblems.IntegerComplexity
