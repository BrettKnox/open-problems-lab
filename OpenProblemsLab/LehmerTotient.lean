import Mathlib.Data.Nat.Totient

/-!
# Lehmer's totient problem (1932)

If `φ(n)` divides `n − 1`, must `n` be prime? Equivalently: no composite `n`
satisfies `φ(n) ∣ n − 1`.

Status 2026-08-19: OPEN. Known: any composite solution has `n > 10^20` and at
least 14 distinct prime factors (Cohen–Hagis 1980), `ω(n) ≥ 4·10^7` if
`3 ∣ n` (Burcsi–Czirbusz–Farkas 2011), counting bounds (Luca–Pomerance 2011),
size bound in `ω(n)` (Burek–Żmija 2019). Computational sweeps are 10+ years
old. In formal-conjectures (`Wikipedia/LehmerTotient.lean`); this statement
is written independently.

Attack lanes: modern search raising the `ω(n) ≥ 14` / `10^20`-era bounds;
formalize the Cohen–Hagis constraint framework.
-/

namespace OpenProblems.LehmerTotient

/-- **Open conjecture** (Lehmer): `φ(n) ∣ n − 1` forces `n` prime for
`n ≥ 2`. (`n = 1` satisfies the divisibility trivially.) -/
def conjecture : Prop :=
  ∀ n : ℕ, 2 ≤ n → Nat.totient n ∣ n - 1 → Nat.Prime n

end OpenProblems.LehmerTotient
