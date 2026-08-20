import Mathlib.Order.Lattice.Nat
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.IntervalCases

/-!
# Integer complexity: ‖2^n‖ = 2n

`‖n‖` is the least number of 1s needed to write `n` using only `+`, `×`, and
parentheses (e.g. `6 = (1+1)·(1+1+1)` gives `‖6‖ ≤ 5`). Conjecture
(Rawsthorne 1989 / Guy): `‖2^n‖ = 2n` for all `n ≥ 1`.

Status 2026-08-19: OPEN. Verified for `2^i ≤ 2^126` (He, arXiv:2308.10301);
`‖2^k·3^ℓ‖ = 2k + 3ℓ` for all `k ≤ 48` and all `ℓ` (Altman, arXiv:1606.03635;
Altman–Arias de Reyna, arXiv:2111.00671). Essentially two active researchers.
No prior Lean formalization of integer complexity is known (not in
google-deepmind/formal-conjectures as of this date).

## What is proved here

Everything below is proved outright — no `sorry`, and the only axioms used are
`propext`, `Classical.choice`, `Quot.sound`.

* `OnesExpr.cube_eval_le_three_pow_size` / `cube_le_three_pow_complexity` —
  Selfridge's lower bound in its sharp integer form: `n^3 ≤ 3^‖n‖`.
  Equivalently `‖n‖ ≥ 3·log₃ n` (`three_logb_le_complexity`).
* `complexity_three_pow` — `‖3^k‖ = 3k` for `k ≥ 1`, the equality case of the
  Selfridge bound.
* `complexity_add_le`, `complexity_mul_le`, `complexity_pow_le` — the basic
  subadditivity API, and `complexity_one/two/three/six` as exact small values.
* `complexity_two_pow_le` — the easy half of the conjecture, `‖2^n‖ ≤ 2n`.
* `conjecture_iff` — the conjecture is *equivalent* to the lower bound
  `2n ≤ ‖2^n‖`, isolating the one hard direction.
* **`complexity_two_pow_of_le_nine` — the conjecture itself, proved for
  `n ≤ 9`.** Selfridge's bound alone settles it up to `n = 9` and, by
  `selfridge_insufficient_at_ten`, not one step further.
* `defect`, `IsStable` and their basic lemmas — the Altman–Zelinsky vocabulary
  that the known partial results are phrased in.

Selfridge's bound pins `‖2^n‖ ≥ ⌈3n·log₃ 2⌉ ≈ 1.892·n`
(`eight_pow_le_three_pow_complexity_two_pow`), so for `n ≥ 10` the entire open
content of the conjecture is the gap between `1.892n` and `2n`.

## Why `n = 9` and not further

The tempting next step is a verified computation inside Lean: build the sets
of values reachable with `k` ones (capped at `N = 2^n`) and check that `2^n`
is absent below size `2n`. Only the over-approximation direction needs
proving, so the formalization is easy — but the arithmetic does not pay. Each
level is a min-plus convolution costing `O(N²)`: at `N = 2^10` that is already
`~10^8` set operations even compiled, and kernel reduction is far slower
still. The route caps out near `n = 10`–`11`, buying one or two values of `n`
for a large amount of finicky proof work plus a `native_decide` trust
assumption. It was measured and rejected, not overlooked.

Getting past `n = 9` formally means formalizing the actual theory — Altman's
defect and low-defect polynomials — which is what makes the known results
(`k ≤ 48` stability, He's search to `2^126`) possible in the first place.

Attack lanes: extend Altman's `k ≤ 48` stability computation; extend He's
power search; formalize the defect/low-defect-polynomial machinery.
-/

namespace OpenProblems.IntegerComplexity

/-- Expressions built from the constant 1 using addition and multiplication. -/
inductive OnesExpr : Type
  | one : OnesExpr
  | add : OnesExpr → OnesExpr → OnesExpr
  | mul : OnesExpr → OnesExpr → OnesExpr

namespace OnesExpr

/-- The value of an expression. -/
def eval : OnesExpr → ℕ
  | .one => 1
  | .add a b => a.eval + b.eval
  | .mul a b => a.eval * b.eval

/-- The number of 1s used by an expression. -/
def size : OnesExpr → ℕ
  | .one => 1
  | .add a b => a.size + b.size
  | .mul a b => a.size + b.size

theorem one_le_eval (e : OnesExpr) : 1 ≤ e.eval := by
  induction e with
  | one => exact le_refl 1
  | add a b iha ihb => show 1 ≤ a.eval + b.eval; omega
  | mul a b iha ihb => exact Nat.mul_pos iha ihb

theorem one_le_size (e : OnesExpr) : 1 ≤ e.size := by
  induction e with
  | one => exact le_refl 1
  | add a b iha ihb => show 1 ≤ a.size + b.size; omega
  | mul a b iha ihb => show 1 ≤ a.size + b.size; omega

/-- Only the expression `1` has size one, so anything of value `≥ 2` costs at
least two 1s. -/
theorem two_le_size_of_two_le_eval {e : OnesExpr} (h : 2 ≤ e.eval) : 2 ≤ e.size := by
  cases e with
  | one => exact absurd h (by simp [eval])
  | add a b =>
    have := one_le_size a; have := one_le_size b
    show 2 ≤ a.size + b.size; omega
  | mul a b =>
    have := one_le_size a; have := one_le_size b
    show 2 ≤ a.size + b.size; omega

private theorem cube_succ_le {v : ℕ} (h : 3 ≤ v) : (1 + v) ^ 3 ≤ 3 * v ^ 3 := by
  nlinarith [sq_nonneg v, h]

/-- **Selfridge's lower bound**, sharp integer form: an expression of size `s`
cannot evaluate to more than `3^(s/3)`, i.e. `eval^3 ≤ 3^size`.

Equality holds exactly for the powers of 3 built as `(1+1+1)·…·(1+1+1)`, which
is why `‖3^k‖ = 3k` below is exact. -/
theorem cube_eval_le_three_pow_size (e : OnesExpr) : e.eval ^ 3 ≤ 3 ^ e.size := by
  induction e with
  | one => norm_num [eval, size]
  | mul a b iha ihb =>
    show (a.eval * b.eval) ^ 3 ≤ 3 ^ (a.size + b.size)
    rw [pow_add, mul_pow]
    exact Nat.mul_le_mul iha ihb
  | add a b iha ihb =>
    have hsa := one_le_size a
    have hsb := one_le_size b
    have hva := one_le_eval a
    have hvb := one_le_eval b
    have h3a : 3 ≤ 3 ^ a.size := by
      calc (3 : ℕ) = 3 ^ 1 := by norm_num
        _ ≤ 3 ^ a.size := Nat.pow_le_pow_right (by norm_num) hsa
    have h3b : 3 ≤ 3 ^ b.size := by
      calc (3 : ℕ) = 3 ^ 1 := by norm_num
        _ ≤ 3 ^ b.size := Nat.pow_le_pow_right (by norm_num) hsb
    show (a.eval + b.eval) ^ 3 ≤ 3 ^ (a.size + b.size)
    rw [pow_add]
    rcases Nat.lt_or_ge a.eval 2 with hA | hA
    · -- `a` evaluates to 1: the product bound `va + vb ≤ va * vb` fails, so use
      -- the size of `a` (at least one 1) instead.
      have hA1 : a.eval = 1 := by omega
      rcases Nat.lt_or_ge b.eval 3 with hB | hB
      · have hB12 : b.eval = 1 ∨ b.eval = 2 := by omega
        rcases hB12 with hB1 | hB2
        · rw [hA1, hB1]
          exact le_trans (by norm_num) (Nat.mul_le_mul h3a h3b)
        · have h9b : 9 ≤ 3 ^ b.size := by
            calc (9 : ℕ) = 3 ^ 2 := by norm_num
              _ ≤ 3 ^ b.size := Nat.pow_le_pow_right (by norm_num)
                  (two_le_size_of_two_le_eval (by omega))
          rw [hA1, hB2]
          exact le_trans (by norm_num) (Nat.mul_le_mul h3a h9b)
      · calc (a.eval + b.eval) ^ 3 = (1 + b.eval) ^ 3 := by rw [hA1]
          _ ≤ 3 * b.eval ^ 3 := cube_succ_le hB
          _ ≤ 3 ^ a.size * 3 ^ b.size := Nat.mul_le_mul h3a ihb
    · rcases Nat.lt_or_ge b.eval 2 with hB | hB
      · -- mirror image of the previous case
        have hB1 : b.eval = 1 := by omega
        rcases Nat.lt_or_ge a.eval 3 with hA' | hA'
        · have hA2 : a.eval = 2 := by omega
          have h9a : 9 ≤ 3 ^ a.size := by
            calc (9 : ℕ) = 3 ^ 2 := by norm_num
              _ ≤ 3 ^ a.size := Nat.pow_le_pow_right (by norm_num)
                  (two_le_size_of_two_le_eval (by omega))
          rw [hA2, hB1]
          exact le_trans (by norm_num) (Nat.mul_le_mul h9a h3b)
        · calc (a.eval + b.eval) ^ 3 = (1 + a.eval) ^ 3 := by rw [hB1]; ring_nf
            _ ≤ 3 * a.eval ^ 3 := cube_succ_le hA'
            _ = a.eval ^ 3 * 3 := by ring
            _ ≤ 3 ^ a.size * 3 ^ b.size := Nat.mul_le_mul iha h3b
      · -- both parts are at least 2, so `va + vb ≤ va * vb`
        calc (a.eval + b.eval) ^ 3 ≤ (a.eval * b.eval) ^ 3 :=
              Nat.pow_le_pow_left (add_le_mul hA hB) 3
          _ = a.eval ^ 3 * b.eval ^ 3 := by ring
          _ ≤ 3 ^ a.size * 3 ^ b.size := Nat.mul_le_mul iha ihb

/-- Every positive integer is the value of some expression. -/
theorem exists_eval_eq : ∀ n : ℕ, 1 ≤ n → ∃ e : OnesExpr, e.eval = n
  | 1, _ => ⟨.one, rfl⟩
  | (n + 2), _ => by
    obtain ⟨e, he⟩ := exists_eval_eq (n + 1) (by omega)
    exact ⟨.add e .one, by show e.eval + 1 = n + 2; omega⟩

/-- `1 + 1`. -/
def two : OnesExpr := .add .one .one

/-- `1 + 1 + 1`. -/
def three : OnesExpr := .add (.add .one .one) .one

@[simp] theorem eval_two : two.eval = 2 := rfl
@[simp] theorem size_two : two.size = 2 := rfl
@[simp] theorem eval_three : three.eval = 3 := rfl
@[simp] theorem size_three : three.size = 3 := rfl

end OnesExpr

open OnesExpr

/-- The set of sizes of expressions evaluating to `n`. -/
def sizes (n : ℕ) : Set ℕ := {k | ∃ e : OnesExpr, e.eval = n ∧ e.size = k}

/-- Integer complexity `‖n‖`: the least number of 1s in a `{+, ×}` expression
evaluating to `n`. (For `n = 0` no expression exists and the value is the junk
value `sInf ∅ = 0`; the notion is only used for `n ≥ 1`.) -/
noncomputable def complexity (n : ℕ) : ℕ := sInf (sizes n)

theorem sizes_nonempty {n : ℕ} (hn : 1 ≤ n) : (sizes n).Nonempty := by
  obtain ⟨e, he⟩ := exists_eval_eq n hn
  exact ⟨e.size, e, he, rfl⟩

/-- Any expression bounds the complexity of its value. -/
theorem complexity_le_size (e : OnesExpr) : complexity e.eval ≤ e.size :=
  Nat.sInf_le ⟨e, rfl, rfl⟩

/-- The infimum is attained: some expression realises `‖n‖`. -/
theorem exists_optimal {n : ℕ} (hn : 1 ≤ n) :
    ∃ e : OnesExpr, e.eval = n ∧ e.size = complexity n :=
  Nat.sInf_mem (sizes_nonempty hn)

theorem one_le_complexity {n : ℕ} (hn : 1 ≤ n) : 1 ≤ complexity n := by
  obtain ⟨e, _, hs⟩ := exists_optimal hn
  rw [← hs]; exact one_le_size e

/-- **Selfridge's lower bound**: `n^3 ≤ 3^‖n‖`. -/
theorem cube_le_three_pow_complexity {n : ℕ} (hn : 1 ≤ n) : n ^ 3 ≤ 3 ^ complexity n := by
  obtain ⟨e, he, hs⟩ := exists_optimal hn
  subst he
  rw [← hs]
  exact cube_eval_le_three_pow_size e

/-- Selfridge's lower bound in logarithmic form: `3·log₃ n ≤ ‖n‖`. -/
theorem three_logb_le_complexity {n : ℕ} (hn : 1 ≤ n) :
    3 * Real.logb 3 n ≤ (complexity n : ℝ) := by
  have hn' : (0 : ℝ) < (n : ℝ) ^ 3 := by positivity
  have hcast : ((n ^ 3 : ℕ) : ℝ) ≤ ((3 ^ complexity n : ℕ) : ℝ) :=
    Nat.cast_le.mpr (cube_le_three_pow_complexity hn)
  push_cast at hcast
  have : Real.logb 3 ((n : ℝ) ^ 3) ≤ (complexity n : ℝ) := by
    rw [Real.logb_le_iff_le_rpow (show (1:ℝ) < 3 by norm_num) hn']
    rwa [Real.rpow_natCast]
  rwa [Real.logb_pow, Nat.cast_ofNat] at this

/-- Subadditivity: `‖m + n‖ ≤ ‖m‖ + ‖n‖`. -/
theorem complexity_add_le {m n : ℕ} (hm : 1 ≤ m) (hn : 1 ≤ n) :
    complexity (m + n) ≤ complexity m + complexity n := by
  obtain ⟨e, he, hse⟩ := exists_optimal hm
  obtain ⟨f, hf, hsf⟩ := exists_optimal hn
  have := complexity_le_size (.add e f)
  rw [show (OnesExpr.add e f).eval = m + n by show e.eval + f.eval = _; omega] at this
  rw [show (OnesExpr.add e f).size = e.size + f.size from rfl, hse, hsf] at this
  exact this

/-- Submultiplicativity: `‖m · n‖ ≤ ‖m‖ + ‖n‖`. -/
theorem complexity_mul_le {m n : ℕ} (hm : 1 ≤ m) (hn : 1 ≤ n) :
    complexity (m * n) ≤ complexity m + complexity n := by
  obtain ⟨e, he, hse⟩ := exists_optimal hm
  obtain ⟨f, hf, hsf⟩ := exists_optimal hn
  have := complexity_le_size (.mul e f)
  rw [show (OnesExpr.mul e f).eval = m * n by show e.eval * f.eval = _; rw [he, hf]] at this
  rw [show (OnesExpr.mul e f).size = e.size + f.size from rfl, hse, hsf] at this
  exact this

/-- `‖n^k‖ ≤ k·‖n‖`: powers cost at most linearly. Both `‖2^n‖ ≤ 2n` and
`‖3^k‖ ≤ 3k` are instances. -/
theorem complexity_pow_le {n : ℕ} (hn : 1 ≤ n) (k : ℕ) :
    complexity (n ^ (k + 1)) ≤ (k + 1) * complexity n := by
  induction k with
  | zero => simp
  | succ j ih =>
    have h1 : complexity (n ^ (j + 2)) ≤ complexity (n ^ (j + 1)) + complexity n := by
      rw [pow_succ]
      exact complexity_mul_le (Nat.one_le_pow _ _ (by omega)) hn
    calc complexity (n ^ (j + 2)) ≤ complexity (n ^ (j + 1)) + complexity n := h1
      _ ≤ (j + 1) * complexity n + complexity n := by omega
      _ = (j + 2) * complexity n := by ring

/-! ### Exact small values

Selfridge's bound is strong enough to pin down `‖n‖` exactly for small `n`,
which also checks that `complexity` means what it should. -/

/-- If `3^c` is too small to reach `n^3`, then `‖n‖` exceeds `c`. -/
private theorem lt_complexity_of_three_pow_lt {n c : ℕ} (hn : 1 ≤ n) (h : 3 ^ c < n ^ 3) :
    c < complexity n := by
  by_contra hle
  push_neg at hle
  have h1 : (3 : ℕ) ^ complexity n ≤ 3 ^ c := Nat.pow_le_pow_right (by norm_num) hle
  have h2 := cube_le_three_pow_complexity hn
  omega

@[simp] theorem complexity_one : complexity 1 = 1 :=
  le_antisymm (complexity_le_size .one) (one_le_complexity (by norm_num))

@[simp] theorem complexity_two : complexity 2 = 2 :=
  le_antisymm (complexity_le_size two) (lt_complexity_of_three_pow_lt (by norm_num) (by norm_num))

@[simp] theorem complexity_three : complexity 3 = 3 :=
  le_antisymm (complexity_le_size three) (lt_complexity_of_three_pow_lt (by norm_num) (by norm_num))

/-- `‖6‖ = 5`, realised by `(1+1)·(1+1+1)`. -/
theorem complexity_six : complexity 6 = 5 :=
  le_antisymm (complexity_le_size (.mul two three))
    (lt_complexity_of_three_pow_lt (by norm_num) (by norm_num))

/-! ### Powers of three: the equality case -/

/-- `‖3^k‖ ≤ 3k`. -/
theorem complexity_three_pow_le {k : ℕ} (hk : 1 ≤ k) : complexity (3 ^ k) ≤ 3 * k := by
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  calc complexity (3 ^ (j + 1)) ≤ (j + 1) * complexity 3 := complexity_pow_le (by norm_num) j
    _ = 3 * (j + 1) := by rw [complexity_three]; ring

/-- **`‖3^k‖ = 3k`** for `k ≥ 1`: powers of three are exactly where Selfridge's
bound is tight. -/
theorem complexity_three_pow {k : ℕ} (hk : 1 ≤ k) : complexity (3 ^ k) = 3 * k := by
  refine le_antisymm (complexity_three_pow_le hk) ?_
  have h := cube_le_three_pow_complexity (n := 3 ^ k) (Nat.one_le_pow _ _ (by norm_num))
  rw [← pow_mul] at h
  have := (Nat.pow_le_pow_iff_right (show 1 < 3 by norm_num)).mp h
  omega

/-! ### Powers of two: the open conjecture -/

/-- `‖2^n‖ ≤ 2n`, the easy half of the conjecture. -/
theorem complexity_two_pow_le {n : ℕ} (hn : 1 ≤ n) : complexity (2 ^ n) ≤ 2 * n := by
  obtain ⟨j, rfl⟩ : ∃ j, n = j + 1 := ⟨n - 1, by omega⟩
  calc complexity (2 ^ (j + 1)) ≤ (j + 1) * complexity 2 := complexity_pow_le (by norm_num) j
    _ = 2 * (j + 1) := by rw [complexity_two]; ring

/-- What Selfridge's bound gives for powers of two: `8^n ≤ 3^‖2^n‖`, i.e.
`‖2^n‖ ≥ 3n·log₃ 2 ≈ 1.892n`. The conjecture asks for `2n`, so this is the
entire gap. -/
theorem eight_pow_le_three_pow_complexity_two_pow (n : ℕ) :
    8 ^ n ≤ 3 ^ complexity (2 ^ n) := by
  have h := cube_le_three_pow_complexity (n := 2 ^ n) (Nat.one_le_pow _ _ (by norm_num))
  have h8 : (8 : ℕ) ^ n = (2 ^ n) ^ 3 := by
    rw [show (8 : ℕ) = 2 ^ 3 by norm_num, ← pow_mul, ← pow_mul, Nat.mul_comm 3 n]
  rw [h8]
  exact h

/-- **The conjecture holds for `n ≤ 9`**, unconditionally and with no
computation beyond arithmetic: Selfridge's bound forces `3^(2n−1) < 8^n` to
fail, so no expression of size `< 2n` can reach `2^n`.

This is exactly the limit of the Selfridge bound. At `n = 9` it is tight to
within 4%: `3^17 = 129140163 < 134217728 = 8^9`. At `n = 10` it reverses
(`3^19 = 1162261467 > 1073741824 = 8^10`), so `n ≥ 10` needs real input —
see `selfridge_insufficient_at_ten`. -/
theorem complexity_two_pow_of_le_nine {n : ℕ} (hn : 1 ≤ n) (h9 : n ≤ 9) :
    complexity (2 ^ n) = 2 * n := by
  refine le_antisymm (complexity_two_pow_le hn) ?_
  by_contra hlt
  push_neg at hlt
  have h1 : (3 : ℕ) ^ complexity (2 ^ n) ≤ 3 ^ (2 * n - 1) :=
    Nat.pow_le_pow_right (by norm_num) (by omega)
  have h2 := eight_pow_le_three_pow_complexity_two_pow n
  have hcon : (8 : ℕ) ^ n ≤ 3 ^ (2 * n - 1) := le_trans h2 h1
  interval_cases n <;> norm_num at hcon

/-- Why `n = 10` is out of reach of this argument: Selfridge's bound leaves
room for an expression of size 19, one below the conjectured 20. -/
theorem selfridge_insufficient_at_ten : (8 : ℕ) ^ 10 < 3 ^ 19 := by norm_num

/-! ### Defect and stability

The two notions Altman's machinery is built on. The *defect*
`δ(n) = ‖n‖ − 3·log₃ n` measures how far `n` is from the Selfridge bound, and
`n` is *stable* when multiplying by powers of three costs exactly `3` per
factor. Altman proved `2^k` is stable for `k ≤ 48`; stability of every `2^k`
would give the conjecture. -/

/-- The defect `δ(n) = ‖n‖ − 3·log₃ n`, Altman–Zelinsky's central invariant. -/
noncomputable def defect (n : ℕ) : ℝ := (complexity n : ℝ) - 3 * Real.logb 3 n

/-- The defect is nonnegative — a restatement of Selfridge's bound. -/
theorem defect_nonneg {n : ℕ} (hn : 1 ≤ n) : 0 ≤ defect n := by
  have := three_logb_le_complexity hn
  simp only [defect]
  linarith

/-- Powers of three have defect zero: they are exactly the equality case. -/
theorem defect_three_pow {k : ℕ} (hk : 1 ≤ k) : defect (3 ^ k) = 0 := by
  have hlog : Real.logb 3 ((3 ^ k : ℕ) : ℝ) = (k : ℝ) := by
    push_cast
    rw [Real.logb_pow, Real.logb_self_eq_one (by norm_num)]
    ring
  simp only [defect, complexity_three_pow hk, hlog]
  push_cast
  ring

/-- Multiplying by three cannot increase the defect. -/
theorem defect_three_mul_le {n : ℕ} (hn : 1 ≤ n) : defect (3 * n) ≤ defect n := by
  have hmul : complexity (3 * n) ≤ 3 + complexity n := by
    have := complexity_mul_le (m := 3) (n := n) (by norm_num) hn
    rwa [complexity_three] at this
  have hcast : ((complexity (3 * n) : ℝ)) ≤ 3 + (complexity n : ℝ) := by exact_mod_cast hmul
  have hlog : Real.logb 3 ((3 : ℕ) * n) = 1 + Real.logb 3 n := by
    push_cast
    rw [Real.logb_mul (by norm_num) (by positivity), Real.logb_self_eq_one (by norm_num)]
  simp only [defect]
  push_cast at hlog ⊢
  rw [hlog]
  linarith

/-- `n` is **stable** when multiplying by powers of three is exactly as
expensive as it looks: `‖3^k·n‖ = 3k + ‖n‖` for every `k`. -/
def IsStable (n : ℕ) : Prop := ∀ k : ℕ, complexity (3 ^ k * n) = 3 * k + complexity n

/-- One direction of stability is free. -/
theorem complexity_three_pow_mul_le {n : ℕ} (hn : 1 ≤ n) (k : ℕ) :
    complexity (3 ^ k * n) ≤ 3 * k + complexity n := by
  rcases Nat.eq_zero_or_pos k with hk | hk
  · subst hk; simp
  · have h := complexity_mul_le (m := 3 ^ k) (n := n) (Nat.one_le_pow _ _ (by norm_num)) hn
    rw [complexity_three_pow hk] at h
    exact h

/-- Powers of three are stable. -/
theorem isStable_three_pow {j : ℕ} (hj : 1 ≤ j) : IsStable (3 ^ j) := by
  intro k
  rw [← pow_add, complexity_three_pow (by omega), complexity_three_pow hj]
  ring

/-- **Open conjecture** (Rawsthorne/Guy): `‖2^n‖ = 2n` for all `n ≥ 1`. -/
def conjecture : Prop := ∀ n : ℕ, 1 ≤ n → complexity (2 ^ n) = 2 * n

/-- Since `‖2^n‖ ≤ 2n` is proved, the conjecture is exactly the lower bound.
Any attack only has to rule out expressions of size `< 2n` for `2^n`. -/
theorem conjecture_iff : conjecture ↔ ∀ n : ℕ, 1 ≤ n → 2 * n ≤ complexity (2 ^ n) := by
  constructor
  · intro h n hn; exact (h n hn).ge
  · intro h n hn; exact le_antisymm (complexity_two_pow_le hn) (h n hn)

theorem defect_two_pow (k : ℕ) :
    defect (2 ^ k) = (complexity (2 ^ k) : ℝ) - k * (3 * Real.logb 3 2) := by
  simp only [defect]
  push_cast
  rw [Real.logb_pow]
  ring

/-- **The conjecture is exactly linearity of the defect**: `δ(2^k) = k·δ(2)`.

This is the form Altman's machinery works in — the defect, not the complexity,
is the invariant with the good structure theory, and `δ(2) = 2 − 3log₃2 ≈
0.107` is the increment the conjecture claims is never beaten. -/
theorem conjecture_iff_defect :
    conjecture ↔ ∀ k : ℕ, 1 ≤ k → defect (2 ^ k) = k * defect 2 := by
  have hd2 : defect 2 = 2 - 3 * Real.logb 3 2 := by
    simp only [defect, complexity_two]; push_cast; ring
  constructor
  · intro h k hk
    rw [defect_two_pow, h k hk, hd2]
    push_cast
    ring
  · intro h n hn
    have hk := h n hn
    rw [defect_two_pow, hd2] at hk
    have : ((complexity (2 ^ n) : ℝ)) = ((2 * n : ℕ) : ℝ) := by push_cast; linarith
    exact_mod_cast this

end OpenProblems.IntegerComplexity
