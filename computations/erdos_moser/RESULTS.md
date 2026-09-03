# Erdős–Moser: computation log (EM-2)

**This is a method reproduction, not a record.** The bound obtained here is far
weaker than both Moser's 1953 elementary bound and Gallot–Moree–Zudilin's, and
the reason is stated precisely below. What this directory establishes is that
the GMZ machinery is implemented correctly end to end, checked against every
row of their published table that this machine can reach.

Run date: 2026-09-02.

## The result being reproduced

The equation is `1^k + 2^k + ... + (m-1)^k = m^k`, and no nontrivial solution
(`k >= 2`) is known. Gallot, Moree and Zudilin
([arXiv:0907.1356](https://arxiv.org/abs/0907.1356)) proved `m > 10^(10^9)` by
an argument that is entirely continued fractions.

**Corollary 1.** If `(m, k)` solves the equation with `k >= 2`, then
`2k/(2m-3)` is a convergent `p_j/q_j` of `log 2` with `j` even.

**Theorem 2** (the quantitative form, and what `gmz.py` implements). Let
`N >= 1` with `N | k`, let `(log 2)/(2N) = [a_0, a_1, ...]` with convergents
`p_i/q_i`, and let `j = j(N)` be the **smallest** index satisfying

| | condition |
|---|---|
| (a) | `j` is even |
| (b) | `a_{j+1} >= 180 N - 2` |
| (c) | `gcd(q_j, 6) = 1` |
| (d) | `nu_p(q_j) = nu_p(3^(p-1) - 1) + nu_p(N) + 1` for every prime `p` in `P(N)` dividing `q_j` |

where `P(N) = {p : p-1 | N} ∪ {p : 3 is a primitive root mod p}`. Then
**`m > q_j / 2`**.

`N` is a free parameter subject to `N | k`, and larger `N` gives a much larger
bound (heuristically `m > 10^(257N)`). The admissible `N` come from
Moree–te Riele–Urbanowicz, who proved `N_1 = lcm(1, ..., 200) | k`, strengthened
with Kellner's result that every prime `200 < p < 1000` divides `k`, giving

    N_2 = 2^8 · 3^5 · 5^4 · 7^3 · 11^2 · 13^2 · 17^2 · 19^2 · ∏_{23<=p<=997} p > 5.7462e427

and `N_2 | k`. Every divisor of `N_2` is therefore a legal choice of `N`.

## Why partial checking of condition (d) is sound

`q_j` has tens of thousands of digits, so factoring it to verify (d) exactly is
out of the question. It is not necessary, and the direction of the error is
what makes this work:

> Conditions (a), (b), (c) and the small-prime part of (d) are all decidable
> exactly, so **every index the program rejects genuinely fails a condition**.
> The true `j(N)` is therefore never smaller than the reported `j`, and since
> `q` increases with the index, `m > q_{j(N)}/2 >= q_j/2`. The printed bound
> holds.

Raising the trial-division bound can only reject more indices, pushing `j` up
and making the bound **stronger**; it can never invalidate one already printed.
This asymmetry is what licenses a partial check, and it is visible in the data:
at `--trial-bound 20000` the row `N = 2304` reports no violating prime, while at
`--trial-bound 60000` it finds `p = 56131` — exactly the prime the paper lists.

## Table 1 reproduced

`python gmz.py --table 1,2,4,8,16,32,64,128,256,768,2304 --trial-bound 60000`

Every column is compared against Table 1 of the paper: the index `j`, the
partial quotient `a_{j+1}`, the value of `q_j`, its residue mod 6, and the
prime witnessing that (d) fails (blank when (d) holds).

| N | j | a_{j+1} | q_j | q_j mod 6 | bad p | vs paper |
|---|---|---|---|---|---|---|
| 1 | 642 | 764 | 2.383153e330 | −1 | 149 | match |
| 2 | 664 | 1 529 | 2.383153e330 | −1 | 149 | match |
| 2² | 1 254 | 21 966 | 1.132014e638 | +1 | 5 | match |
| 2³ | 1 264 | 43 933 | 1.132014e638 | +1 | 5 | match |
| 2⁴ | 1 280 | 87 866 | 1.132014e638 | +1 | 5 | match |
| 2⁵ | 1 294 | 175 733 | 1.132014e638 | +1 | 5 | match |
| 2⁶ | 8 950 | 26 416 | 3.458446e4589 | −1 | — | match |
| 2⁷ | 8 926 | 52 834 | 3.458446e4589 | −1 | — | match |
| 2⁸ | 119 476 | 122 799 | 1.374540e61317 | +1 | — | match |
| 2⁸·3 | 119 008 | 368 398 | 1.374540e61317 | +1 | — | match |
| 2⁸·3² | 139 532 | 782 152 | 9.351282e71882 | +1 | 56 131 | match |

**All 11 reachable rows match exactly**, including the mantissas to 7
significant figures and the two violating primes. Total run time about 90 s.

Two features of the table look wrong at first sight and are in fact correct;
both were settled by computing them rather than by argument:

* **The same `q_j` appears against different `j`** (rows `N = 1, 2` and rows
  `N = 2²..2⁵`). Not a typo: the continued fraction is of `(log 2)/(2N)`, a
  *different real number for each `N`*, so the same rational approximation
  surfaces at different indices.
* **`j` is not monotone in `N`** (`j = 8950` at `N = 2⁶` but `8926` at
  `N = 2⁷`, and `119476` at `2⁸` but `119008` at `2⁸·3`), even though condition
  (b) gets strictly harder as `N` grows. For the same reason: indices in
  different rows index different continued fractions and are not comparable.
  An earlier draft of this note asserted these rows had to be extraction
  errors. They are not — the computation reproduced them.

## The bound obtained, and the gap to the literature

The strongest row here where (d) holds is `N = 2⁸·3 = 768` (a divisor of `N_2`,
so `768 | k`), giving `q_j = 1.374540e61317` and hence

    m > 6.87 · 10^61316.

| source | bound on m | method |
|---|---|---|
| this run | `> 6.87e61316` | GMZ Theorem 2, `N = 768`, `r ≈ 1.2e5` |
| Moser 1953 | `> 10^(10^6)` | elementary, von Staudt–Clausen |
| best pre-GMZ | `> 10^(9.3e6)` | Moser's method, refined |
| **GMZ 2009** | **`> 2.7139e1667658416`** | Theorem 2, `N = 7776000`, `r ≈ 3e9` |

So this run is roughly **`10^4`× short of Moser in the exponent** and `10^13`×
short of GMZ. The gap is entirely in `r`, the number of correct partial
quotients: GMZ used ~3·10⁹ of them (from Yee and Chan's 31-billion-digit
computation of `log 2`), and the bound scales as `10^(0.515 r)` by Lévy's
constant. This implementation reaches `r ≈ 1.4·10^5`.

**That gap is not closable here, and the obstruction is named.** The continued
fraction is extracted by a Euclidean algorithm on integers with `r` digits,
which is quadratic; the paper says as much ("Bit-complexity of this algorithm
is quadratic and reaching the `m > 10^(10^10)` milestone would take
centuries") and reports that they had to switch to a recursive half-GCD
(`O(n log²n log log n)`) to get past `10^(10^8)`. Reproducing GMZ's actual
bound needs a subquadratic HGCD continued-fraction extractor plus a
`log 2` computation of billions of digits — a different program, not a bigger
`--digits`. Measured here: 61 318-digit `q_j` at `N = 2⁸` in 18.8 s, 71 883
digits at `N = 2⁸·3²` in 25.0 s.

## Validation

Eight gates, all passing (`python gmz.py --verify`, ~30 s).

1. **(A)** The leading partial quotients of `log 2` equal the known expansion
   `[0; 1, 2, 3, 1, 6, 3, 1, 1, 2, 1, 1, 1, 1, 3, 10]`.
2. **(B)** Certification nests: the terms certified at 300 digits are a prefix
   of those certified at 600, and there are strictly more of the latter.
3. **(C)** 40 convergent denominators match an independent reconstruction that
   builds the convergent as a `Fraction` from the tail of the expansion,
   sharing no code with the recurrence.
4. **(D)** `P(N)` membership is right on hand-checked cases: 3 is a primitive
   root mod 5, 7, 17 but not mod 11 (order 5) or 13 (order 3); and the
   `p - 1 | N` branch fires for `p = 2, N = 1` and `p = 3, N = 2`.
5. **(E)** The fast `nu_p(3^(p-1) - 1)` (one modular exponentiation mod `p^6`)
   agrees with exact big-integer computation for **every prime below 300**, and
   independently rediscovers that 11 is a Mirimanoff prime (`nu = 2`) — one of
   only two known below `10^14`.
6. **(F)** Negative control: perturbing a single partial quotient changes the
   convergent denominators from that point on, so gate (C) is not vacuous.
7. **(G)** Every reported row is re-verified against (a), (b), (c) after the
   fact, independently of the loop that selected it.
8. **(H)** The `N = 1` row of Table 1 is reproduced exactly — `j = 642`,
   `a_{j+1} = 764`, violating prime 149 — inside the gate suite, so a
   regression in any part of the pipeline fails `--verify`.

Caveats, stated plainly:

* Condition (d) is checked only for `P(N)` primes below `--trial-bound`. As
  argued above this is sound (it can only weaken the bound), but it means the
  reported `j` is a lower bound for `j(N)`, not necessarily `j(N)` itself.
  Where the paper lists a violating prime, this program finds the same one once
  the bound is raised past it.
* The partial quotients are certified by agreement between two precisions
  (`digits` and `digits + 1000`), less an 8-term margin. That is an empirical
  certification, not the rigorous error control of [4] in the paper.
* Single machine, single thread, no independent re-run on other hardware.
* `N | k` for `N | N_2` rests on Moree–te Riele–Urbanowicz and Kellner, cited
  not verified here. The `N = 1` row needs no such input and is unconditional
  (it gives only `m > 10^450`).

## Machine

| | |
|---|---|
| CPU | AMD Ryzen 7 7840HS |
| OS | Windows 11 Pro 10.0.26200 |
| Python | 3.14.3, mpmath (via sympy), sympy for `n_order`/`primerange` |

## Reproducing

```
cd computations/erdos_moser

python gmz.py --verify                       # 8 gates, ~30 s
python gmz.py --table 1,2,4,8,16,32,64,128   # small rows, seconds
python gmz.py --table 256,768,2304 --trial-bound 60000   # ~90 s
python gmz.py --N 768 --digits 140000        # the bound itself
```

The paper's PDF is fetched from `export.arxiv.org` when needed and is not
committed.
