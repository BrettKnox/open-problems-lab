import Mathlib.Data.Nat.Totient
import Mathlib.Data.Nat.Squarefree
import Mathlib.Tactic.Ring

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

## What is proved here

The first rungs of the classical constraint ladder on a hypothetical
composite solution, machine-checked (no `sorry`, standard axioms):

* `odd_of_lehmer` — a solution `n ≥ 3` is odd.
* `squarefree_of_lehmer` — every solution is squarefree.
* `not_lehmer_semiprime` — no product of two distinct primes is a solution.
* **`three_le_card_primeFactors_of_lehmer`** — a composite solution has at
  least **3** distinct prime factors (Lehmer's own first bound; the published
  ladder continues 14 ≤ ω(n), which requires serious computation).

Attack lanes: extend the ladder formally (ω ≥ 4 needs case analysis Lehmer
did by hand); modern search raising the `ω(n) ≥ 14` / `10^20`-era bounds;
formalize the Cohen–Hagis constraint framework.
-/

namespace OpenProblems.LehmerTotient

open Nat

/-- **Open conjecture** (Lehmer): `φ(n) ∣ n − 1` forces `n` prime for
`n ≥ 2`. (`n = 1` satisfies the divisibility trivially.) -/
def conjecture : Prop :=
  ∀ n : ℕ, 2 ≤ n → Nat.totient n ∣ n - 1 → Nat.Prime n

/-- A Lehmer solution `n ≥ 3` is odd: `φ(n)` is even for `n > 2`, and an even
number cannot divide the even-minus-one `n − 1` unless `n` is odd. -/
theorem odd_of_lehmer {n : ℕ} (h3 : 3 ≤ n) (hd : n.totient ∣ n - 1) : Odd n := by
  rcases Nat.even_or_odd n with he | ho
  · exfalso
    have hev : Even n.totient := totient_even (by omega)
    have h2t : 2 ∣ n.totient := ⟨n.totient / 2, by
      obtain ⟨k, hk⟩ := hev
      omega⟩
    obtain ⟨c, hc⟩ := h2t.trans hd
    obtain ⟨j, hj⟩ := he
    omega
  · exact ho

/-- Every Lehmer solution is squarefree: if `p² ∣ n` then `p ∣ φ(n) ∣ n − 1`
while also `p ∣ n`, forcing `p ∣ 1`. -/
theorem squarefree_of_lehmer {n : ℕ} (h1 : 1 ≤ n) (hd : n.totient ∣ n - 1) :
    Squarefree n := by
  rw [Nat.squarefree_iff_prime_squarefree]
  rintro p hp ⟨m, hm⟩
  -- `n = p * (p * m)`, and `p ∣ p * m`, so `φ(n) = p * φ(p * m)`
  have hm' : n = p * (p * m) := by rw [hm, mul_assoc]
  have hpdvd : p ∣ p * m := Dvd.intro m rfl
  have htot : n.totient = p * (p * m).totient := by
    rw [hm']
    exact totient_mul_of_prime_of_dvd hp hpdvd
  have hpφ : p ∣ n.totient := htot ▸ Dvd.intro _ rfl
  have hp1 : p ∣ n - 1 := hpφ.trans hd
  have hpn : p ∣ n := hm' ▸ Dvd.intro (p * m) (by ring)
  have : p ∣ 1 := by
    have := Nat.dvd_sub hpn hp1
    rwa [Nat.sub_sub_self h1] at this
  exact hp.one_lt.ne' (Nat.dvd_one.mp this)

/-- No product of two distinct primes satisfies Lehmer's divisibility:
`(p−1)(q−1) ∣ pq − 1` fails because `pq − 1 = (p−1)(q−1) + (p−1) + (q−1)`
and `(p−1)(q−1) > (p−1) + (q−1)` for distinct primes (with the `p = 2`
case failing on parity instead). -/
theorem not_lehmer_semiprime {p q : ℕ} (hp : p.Prime) (hq : q.Prime)
    (hne : p ≠ q) : ¬ (p * q).totient ∣ p * q - 1 := by
  intro hd
  have hco : Nat.Coprime p q := (Nat.coprime_primes hp hq).mpr hne
  have htot : (p * q).totient = (p - 1) * (q - 1) := by
    rw [totient_mul hco, totient_prime hp, totient_prime hq]
  rw [htot] at hd
  have hp2 := hp.two_le
  have hq2 := hq.two_le
  rcases Nat.lt_or_ge p 3 with hplt | hpge
  · -- p = 2: (q − 1) ∣ 2q − 1 = 2(q − 1) + 1 forces q − 1 ∣ 1
    have hp2' : p = 2 := by omega
    subst hp2'
    have hd' : (q - 1) ∣ 2 * q - 1 := by simpa using hd
    have hdd : (q - 1) ∣ 1 := by
      have h2q : (q - 1) ∣ 2 * (q - 1) := dvd_mul_left _ _
      have hEq : 2 * q - 1 = 2 * (q - 1) + 1 := by omega
      rw [hEq] at hd'
      exact (Nat.dvd_add_right h2q).mp hd'
    have := Nat.le_of_dvd (by norm_num) hdd
    omega
  · rcases Nat.lt_or_ge q 3 with hqlt | hqge
    · -- q = 2 symmetric
      have hq2' : q = 2 := by omega
      subst hq2'
      have hd' : (p - 1) ∣ 2 * p - 1 := by
        have : (p - 1) * (2 - 1) = p - 1 := by omega
        rw [this] at hd
        have hpq : p * 2 = 2 * p := by ring
        rwa [hpq] at hd
      have hdd : (p - 1) ∣ 1 := by
        have h2p : (p - 1) ∣ 2 * (p - 1) := dvd_mul_left _ _
        have hEq : 2 * p - 1 = 2 * (p - 1) + 1 := by omega
        rw [hEq] at hd'
        exact (Nat.dvd_add_right h2p).mp hd'
      have := Nat.le_of_dvd (by norm_num) hdd
      omega
    · -- both ≥ 3: the divisor (p−1)(q−1) exceeds the remainder (p−1)+(q−1)
      have hkey : p * q - 1 = (p - 1) * (q - 1) + ((p - 1) + (q - 1)) := by
        obtain ⟨a, ha⟩ := Nat.exists_eq_add_of_le hp2
        obtain ⟨b, hb⟩ := Nat.exists_eq_add_of_le hq2
        subst ha
        subst hb
        have e1 : (2 + a) - 1 = a + 1 := by omega
        have e2 : (2 + b) - 1 = b + 1 := by omega
        rw [e1, e2]
        have e3 : (2 + a) * (2 + b) = (a + 1) * (b + 1) + ((a + 1) + (b + 1)) + 1 := by
          ring
        omega
      have hrem : (p - 1) * (q - 1) ∣ (p - 1) + (q - 1) :=
        (Nat.dvd_add_right (dvd_refl _)).mp (hkey ▸ hd)
      have hle := Nat.le_of_dvd (by omega) hrem
      -- with a = p−1 ≥ 2, b = q−1 ≥ 2: 2a ≤ ab and 2b ≤ ab force a = b, i.e. p = q
      have hab1 : (p - 1) * 2 ≤ (p - 1) * (q - 1) :=
        Nat.mul_le_mul_left _ (by omega)
      have hab2 : 2 * (q - 1) ≤ (p - 1) * (q - 1) :=
        Nat.mul_le_mul_right _ (by omega)
      exact hne (by omega)

/-- **A composite Lehmer solution has at least three distinct prime
factors** (Lehmer 1932's first structural bound, machine-checked): it is
squarefree, it is not prime, and it cannot be a product of two distinct
primes. -/
theorem three_le_card_primeFactors_of_lehmer {n : ℕ} (h2 : 2 ≤ n)
    (hd : n.totient ∣ n - 1) (hcomp : ¬ n.Prime) :
    3 ≤ n.primeFactors.card := by
  have hsf : Squarefree n := squarefree_of_lehmer (by omega) hd
  have hprod : ∏ p ∈ n.primeFactors, p = n := prod_primeFactors_of_squarefree hsf
  by_contra hlt
  push Not at hlt
  have hcases : n.primeFactors.card = 0 ∨ n.primeFactors.card = 1 ∨
      n.primeFactors.card = 2 := by omega
  rcases hcases with hcard | hcard | hcard
  · -- no prime factors: n = empty product = 1 < 2
    rw [Finset.card_eq_zero.mp hcard] at hprod
    simp at hprod
    omega
  · -- one prime factor: n is that prime
    obtain ⟨p, hp⟩ := Finset.card_eq_one.mp hcard
    rw [hp, Finset.prod_singleton] at hprod
    have hpp : p.Prime := Nat.prime_of_mem_primeFactors (hp ▸ Finset.mem_singleton_self p)
    exact hcomp (hprod ▸ hpp)
  · -- two prime factors: n = p * q, distinct primes — refuted above
    obtain ⟨p, q, hne, hpq⟩ := Finset.card_eq_two.mp hcard
    have hpp : p.Prime := Nat.prime_of_mem_primeFactors
      (hpq ▸ Finset.mem_insert_self p {q})
    have hqp : q.Prime := Nat.prime_of_mem_primeFactors
      (hpq ▸ Finset.mem_insert_of_mem (Finset.mem_singleton_self q))
    rw [hpq, Finset.prod_pair hne] at hprod
    exact not_lehmer_semiprime hpp hqp hne (hprod ▸ hd)

end OpenProblems.LehmerTotient
