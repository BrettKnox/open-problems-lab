"""Erdos-Moser: reproducing the Gallot-Moree-Zudilin continued-fraction bound.

The equation is 1^k + 2^k + ... + (m-1)^k = m^k, and no nontrivial solution
(k >= 2) is known.  GMZ (arXiv:0907.1356) proved m > 10^(10^9) by an argument
that is pure continued fractions, and this reproduces their method at laptop
scale, with every constant taken from the paper rather than guessed.

Corollary 1 of the paper: if (m, k) solves the equation with k >= 2 then
2k/(2m-3) is a convergent p_j/q_j of log 2 with j EVEN.  (From Theorem 1's
asymptotic k = log 2 * (m - 3/2 - c1/m + O(1/m^2)), which makes 2k/(2m-3) a
good enough rational approximation for Legendre's theorem to apply; log 2
exceeding the ratio forces the index to be even.)

Theorem 2 is the quantitative form, and is what this implements.  Let N >= 1
with N | k, let (log 2)/(2N) = [a_0, a_1, ...] with convergents p_i/q_i, and
let j = j(N) be the SMALLEST index satisfying

    (a)  j is even
    (b)  a_{j+1} >= 180 N - 2
    (c)  gcd(q_j, 6) = 1
    (d)  nu_p(q_j) = nu_p(3^(p-1) - 1) + nu_p(N) + 1
         for every prime p in P(N) dividing q_j

where P(N) = {p : p-1 | N} union {p : 3 is a primitive root mod p} and nu_p is
the p-adic valuation.  Then  m > q_j / 2.

Condition (d) cannot be checked exactly: q_j has thousands of digits and
factoring it is hopeless.  It does not need to be.  Checking (d) only for
primes below a bound B is SAFE, and the direction matters:

    every index this program rejects fails a condition genuinely -- (a), (b),
    (c) and the small-prime part of (d) are all decidable exactly -- so the
    true j(N) is never smaller than the j we report.  Hence
    m > q_{j(N)}/2 >= q_j/2, and the bound we print is valid.

Raising B can therefore only reject more indices, pushing j up and making the
bound STRONGER; it can never invalidate it.  That asymmetry is what makes a
partial check legitimate here.

The scale gap to GMZ is entirely in how far the continued fraction is taken:
they used ~10^9 correct partial quotients (Yee-Chan), which by Levy's constant
gives ~10^(0.515 r).  This runs r in the tens of thousands.

    python gmz.py --verify
    python gmz.py --N 1 --digits 20000
"""

from __future__ import annotations

import argparse
import sys
import time
from fractions import Fraction
from math import gcd

from mpmath import mp
from sympy import n_order, primerange

# q_j runs to tens of thousands of digits; Python 3.11+ caps int -> str at 4300
sys.set_int_max_str_digits(10 ** 7)


# --------------------------------------------------------------------------
# continued fraction of (log 2) / (2N)
# --------------------------------------------------------------------------

def _cf_raw(N: int, digits: int) -> list[int]:
    """Partial quotients from a `digits`-digit decimal truncation."""
    mp.dps = digits + 60
    x = mp.log(2) / (2 * N)
    num = int(mp.floor(x * mp.mpf(10) ** digits))
    den = 10 ** digits
    cf = []
    a, b = num, den
    while b:
        q = a // b
        cf.append(q)
        a, b = b, a - q * b
    return cf


def certified_cf(N: int, digits: int, margin: int = 8) -> list[int]:
    """Partial quotients that two independent precisions agree on.

    A continued fraction computed from a truncated decimal is correct only up
    to some depth, and the depth is not known a priori.  Computing at two
    precisions and keeping the common prefix (less a margin) makes the result
    self-certifying rather than trusting a rule of thumb.
    """
    lo = _cf_raw(N, digits)
    hi = _cf_raw(N, digits + 1000)
    n = 0
    while n < len(lo) and n < len(hi) and lo[n] == hi[n]:
        n += 1
    if n <= margin:
        raise RuntimeError(f"no agreeing prefix at {digits} digits")
    return lo[:n - margin]


def denominators(cf):
    """Yield (i, a_i, q_i) for the convergents of `cf`."""
    qm1, qm2 = 0, 1
    for i, a in enumerate(cf):
        q = a * qm1 + qm2
        yield i, a, q
        qm1, qm2 = q, qm1


# --------------------------------------------------------------------------
# the arithmetic side: P(N) and the valuations in condition (d)
# --------------------------------------------------------------------------

def valuation(n: int, p: int) -> int:
    v = 0
    while n % p == 0:
        n //= p
        v += 1
    return v


def nu_3_pow(p: int) -> int:
    """nu_p(3^(p-1) - 1).

    This is 1 unless p is a Mirimanoff prime (3^(p-1) = 1 mod p^2); the only
    ones below 10^14 are 11 and 1006003.  Computed mod p^6 first so the usual
    case costs one modular exponentiation instead of a huge power.
    """
    r = pow(3, p - 1, p ** 6) - 1
    if r == 0:
        return valuation(3 ** (p - 1) - 1, p)  # exceedingly rare
    return valuation(r, p)


def in_P(p: int, N: int) -> bool:
    """P(N) = {p : p-1 | N} u {p : 3 is a primitive root mod p}."""
    if N % (p - 1) == 0:
        return True
    if p == 3:
        return False
    return n_order(3, p) == p - 1


# --------------------------------------------------------------------------
# the search
# --------------------------------------------------------------------------

def violating_prime(q: int, N: int, ps, nu, nuN):
    """Smallest checked p in P(N) with p | q violating condition (d)."""
    for p in ps:
        if q % p == 0 and valuation(q, p) != nu[p] + nuN[p] + 1:
            return p
    return None


def scan(N: int, digits: int, B: int, verbose: bool = True) -> dict:
    """Indices satisfying (a),(b),(c), up to and including the first that
    also satisfies (d).

    Table 1 of the paper lists the smallest index satisfying (a),(b),(c)
    only, together with a prime witnessing that (d) fails there; the bound
    itself needs (d), so both are reported.
    """
    t0 = time.time()
    cf = certified_cf(N, digits)
    t_cf = time.time() - t0
    if verbose:
        print(f"(log 2)/(2*{N}): {len(cf):,} certified partial quotients "
              f"in {t_cf:.1f}s")

    ps = [p for p in primerange(5, B) if in_P(p, N)]
    nu = {p: nu_3_pow(p) for p in ps}
    nuN = {p: valuation(N, p) for p in ps}
    if verbose:
        print(f"P({N}) primes below {B:,}: {len(ps):,} "
              f"(condition (d) is checked against these)")

    thresh = 180 * N - 2
    rows = []
    for i, a, q in denominators(cf):
        if i + 1 >= len(cf):
            break
        if i % 2 or cf[i + 1] < thresh:      # (a), (b)
            continue
        if gcd(q, 6) != 1:                   # (c)
            continue
        p = violating_prime(q, N, ps, nu, nuN)
        rows.append({"j": i, "a_next": cf[i + 1], "q": q,
                     "q_mod6": q % 6, "bad_p": p})
        if p is None:                        # (d) holds as far as checked
            break
    return {"N": N, "rows": rows, "terms": len(cf), "primes": len(ps),
            "cf_seconds": t_cf, "seconds": time.time() - t0}


def mantissa(q: int, k: int = 7) -> str:
    s = str(q)
    return f"{s[0]}.{s[1:k]} * 10^{len(s) - 1}"


# Table 1 of arXiv:0907.1356: the smallest j satisfying (a),(b),(c), with
# a_{j+1} and (last entry) a prime in P(N) dividing q_j to the first power,
# so that (d) fails there.  None means (d) is not violated at that index.
# Rows past N = 2^8*3^2 need j in the millions, i.e. a continued fraction of
# log 2 far beyond what a quadratic-time Python implementation can reach;
# they are recorded for completeness and skipped by --table.
PUBLISHED = {
    1: (642, 764, 149),
    2: (664, 1529, 149),
    4: (1254, 21966, 5),
    8: (1264, 43933, 5),
    16: (1280, 87866, 5),
    32: (1294, 175733, 5),
    64: (8950, 26416, None),
    128: (8926, 52834, None),
    256: (119476, 122799, None),
    768: (119008, 368398, None),           # 2^8 * 3
    2304: (139532, 782152, 56131),         # 2^8 * 3^2
    6912: (6168634, 1540283, None),        # 2^8 * 3^3
    20736: (22383618, 5167079, 17),        # 2^8 * 3^4
    62208: (155830946, 31664035, None),    # 2^8 * 3^5
    311040: (351661538, 85898211, None),   # 2^8 * 3^5 * 5
    1555200: (1738154976, 1433700727, 5),  # 2^8 * 3^5 * 5^2
    7776000: (2015279170, 4388327617, 19),  # 2^8 * 3^5 * 5^3; Theorem 3
    38880000: (2015385392, 21941638090, 19),  # 2^8 * 3^5 * 5^4
}


# --------------------------------------------------------------------------
# gates
# --------------------------------------------------------------------------

def gates() -> None:
    # (A) the leading partial quotients of log 2 are what they should be.
    # log 2 = [0; 1, 2, 3, 1, 6, 3, 1, 1, 2, 1, 1, 1, 1, 3, 10, ...]
    known = [0, 1, 2, 3, 1, 6, 3, 1, 1, 2, 1, 1, 1, 1, 3, 10]
    got = _cf_raw(1, 200)[:16]
    # _cf_raw(1, .) is log 2 / 2, so redo with the plain constant
    mp.dps = 260
    x = mp.log(2)
    num = int(mp.floor(x * mp.mpf(10) ** 200))
    a, b, cf = num, 10 ** 200, []
    while b:
        qq = a // b
        cf.append(qq)
        a, b = b, a - qq * b
    assert cf[:16] == known, f"cf(log 2) = {cf[:16]}, expected {known}"
    print(f"  ok   (A) cf(log 2) matches the known expansion: {known[:10]}...")

    # (B) certification actually bites: the agreeing prefix is long but finite
    c1 = certified_cf(1, 300)
    c2 = certified_cf(1, 600)
    assert c2[:len(c1)] == c1, "certified prefixes disagree"
    assert len(c2) > len(c1), "more digits must certify more terms"
    print(f"  ok   (B) certified prefixes nest: {len(c1)} terms at 300 digits, "
          f"{len(c2)} at 600")

    # (C) convergent denominators match an independent Fraction reconstruction
    cf = certified_cf(1, 200)[:40]
    for i, a, q in denominators(cf):
        f = Fraction(cf[i], 1)
        for t in reversed(cf[:i]):
            f = t + 1 / f
        assert f.denominator == q, f"q_{i}: {q} vs {f.denominator}"
    print("  ok   (C) 40 convergent denominators match Fraction rebuild")

    # (D) primitive-root membership, checked against hand values.
    # 3 is a primitive root mod 5, 7, 17 but not mod 11 (order 5) or 13 (3)
    for p in (5, 7, 17):
        assert in_P(p, 1), f"3 should be a primitive root mod {p}"
    for p in (11, 13):
        assert not in_P(p, 1), f"3 should NOT be a primitive root mod {p}"
    assert in_P(2, 1) and in_P(3, 2), "p-1 | N branch of P(N)"
    print("  ok   (D) P(N) membership correct on 5,7,17 / 11,13 and p-1|N")

    # (E) nu_p(3^(p-1) - 1) fast path agrees with exact big-int computation
    for p in list(primerange(5, 300)):
        assert nu_3_pow(p) == valuation(3 ** (p - 1) - 1, p), f"nu at {p}"
    assert nu_3_pow(11) == 2, "11 is a Mirimanoff prime, nu must be 2"
    print("  ok   (E) nu_p(3^(p-1)-1) exact for all p < 300; Mirimanoff 11 -> 2")

    # (F) negative control: a corrupted partial quotient changes the
    # denominators, so the Fraction rebuild in (C) is not vacuous
    bad = list(certified_cf(1, 200)[:40])
    bad[7] += 1
    qs_good = [q for _, _, q in denominators(certified_cf(1, 200)[:40])]
    qs_bad = [q for _, _, q in denominators(bad)]
    assert qs_good[:7] == qs_bad[:7] and qs_good[8:] != qs_bad[8:]
    print("  ok   (F) negative control: perturbed quotient shifts q_j")

    # (G) every reported row genuinely satisfies (a), (b), (c)
    r = scan(1, 1200, 2000, verbose=False)
    cf = certified_cf(1, 1200)
    assert r["rows"], "expected at least one row for N=1"
    for row in r["rows"]:
        assert row["j"] % 2 == 0, "condition (a)"
        assert cf[row["j"] + 1] >= 178, "condition (b)"
        assert gcd(row["q"], 6) == 1, "condition (c)"
    print(f"  ok   (G) {len(r['rows'])} reported rows re-verified "
          f"against (a),(b),(c)")

    # (H) reproduce the first published row of Table 1 exactly
    j, a, p = PUBLISHED[1]
    row = r["rows"][0]
    assert row["j"] == j, f"j: got {row['j']}, paper says {j}"
    assert row["a_next"] == a, f"a_j+1: got {row['a_next']}, paper says {a}"
    assert row["bad_p"] == p, f"bad prime: got {row['bad_p']}, paper says {p}"
    print(f"  ok   (H) Table 1 row N=1 reproduced: j={j}, a={a}, p={p}")
    print("all gates: PASS")


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__.split("\n")[0])
    ap.add_argument("--verify", action="store_true")
    ap.add_argument("--N", type=int, default=1,
                    help="a known divisor of k (N=1 is unconditional; "
                         "N=2 uses Moser's theorem that k is even)")
    ap.add_argument("--digits", type=int, default=0)
    ap.add_argument("--trial-bound", type=int, default=20000,
                    help="check condition (d) for P(N) primes below this")
    ap.add_argument("--table", type=str, default="",
                    help="comma-separated N values; reproduces Table 1")
    args = ap.parse_args()

    if args.verify:
        gates()

    if args.table:
        Ns = [int(x) for x in args.table.split(",")]
        print(f"{'N':>10} {'j':>10} {'a_j+1':>12} {'q_j mod 6':>10} "
              f"{'bad p':>7}  paper")
        for N in Ns:
            # ~1.03 decimal digits per partial quotient (Lochs), plus slack
            need = args.digits or max(2000, int(1.15 * PUBLISHED.get(
                N, (2000,))[0]) + 2000)
            r = scan(N, need, args.trial_bound, verbose=False)
            if not r["rows"]:
                print(f"{N:>10} {'-':>10}  no row within {r['terms']:,} terms")
                continue
            row = r["rows"][0]
            pub = PUBLISHED.get(N)
            if pub is None:
                verdict = "(not in table)"
            elif (row["j"], row["a_next"], row["bad_p"]) == pub:
                verdict = "MATCH"
            else:
                verdict = f"DIFFERS: paper says j={pub[0]}, a={pub[1]}, p={pub[2]}"
            print(f"{N:>10} {row['j']:>10} {row['a_next']:>12,} "
                  f"{row['q_mod6']:>10} {str(row['bad_p']):>7}  {verdict}")
            print(f"{'':>10} q_j = {mantissa(row['q'])} "
                  f"({len(str(row['q'])):,} digits), {r['seconds']:.1f}s")

    if args.digits and not args.table:
        r = scan(args.N, args.digits, args.trial_bound)
        good = [x for x in r["rows"] if x["bad_p"] is None]
        print(f"rows satisfying (a),(b),(c): {len(r['rows'])}")
        for row in r["rows"]:
            print(f"  j={row['j']:,}  a_j+1={row['a_next']:,}  "
                  f"q_j = {mantissa(row['q'])}  q mod 6 = {row['q_mod6']}  "
                  + (f"(d) fails at p={row['bad_p']}" if row["bad_p"]
                     else "(d) holds"))
        if not good:
            print(f"no index satisfied all four conditions in "
                  f"{r['terms']:,} terms -- increase --digits")
        else:
            q = good[0]["q"]
            d = len(str(q))
            print(f"j({r['N']}) = {good[0]['j']:,}, q_j has {d:,} digits")
            # the bound is q_j/2, which has one fewer leading digit than q_j;
            # printing 10^(d-1) here would overstate it
            print(f"=> any solution of the Erdos-Moser equation with k >= 2"
                  + (f" and {r['N']} | k" if r["N"] > 1 else "")
                  + f" has m > q_j/2 = {mantissa(q // 2)}")
        print(f"total {r['seconds']:.1f}s")

    if not (args.verify or args.digits or args.table):
        ap.print_help()
    return 0


if __name__ == "__main__":
    sys.exit(main())
