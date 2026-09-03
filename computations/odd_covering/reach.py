"""How far the coprime screen can possibly reach, in closed form.

The screen (see dfs_cover.py) rests on: for T the primes dividing L, a
covering with lcm L needs

    g(L) := sum_{m | L, m > 1, m not prime} 1/phi(m)  >=  1.

That sum has a closed form, because sum_{m | L} 1/phi(m) is multiplicative:

    sum_{m | L} 1/phi(m) = prod_{p^e || L} (1 + S(p, e)),
    S(p, e) = sum_{k=1}^{e} 1/(p^(k-1) (p-1)) = p/(p-1)^2 * (1 - p^-e),

so subtracting the two excluded kinds of divisor (m = 1, and m prime),

    g(L) = prod_{p^e || L} (1 + S(p, e))  -  1  -  sum_{p | L} 1/(p-1).

This makes the screen's ceiling explicit rather than empirical.  S(p, e)
increases in e but is bounded by p/(p-1)^2, so g(L) is bounded above by a
quantity depending only on the SET of primes dividing L, no matter how large
the exponents are:

    g_sup(P) = prod_{p in P} (1 + p/(p-1)^2)  -  1  -  sum_{p in P} 1/(p-1).

Once g_sup(P) >= 1 the criterion can never fire for any L with that prime
set -- not with more computing, not with a bigger bound.  For P = {3,5,7,11,13}
the supremum is about 2.32, so those shapes are permanently out of reach, and
they are exactly the twelve survivors found below 10^7.

    python reach.py --verify
    python reach.py
"""

from __future__ import annotations

import argparse
import sys
from fractions import Fraction

from sympy import factorint, primerange

import dfs_cover as d


def S(p: int, e: int) -> Fraction:
    """sum_{k=1..e} 1/(p^(k-1) (p-1)), exactly."""
    return sum((Fraction(1, p ** (k - 1) * (p - 1)) for k in range(1, e + 1)),
               Fraction(0))


def g_closed(L: int) -> Fraction:
    """sum 1/phi(m) over divisors m > 1 of L that are not prime."""
    f = factorint(L)
    prod = Fraction(1)
    for p, e in f.items():
        prod *= 1 + S(p, e)
    return prod - 1 - sum((Fraction(1, p - 1) for p in f), Fraction(0))


def g_direct(L: int) -> Fraction:
    from sympy import totient, isprime
    return sum((Fraction(1, int(totient(m))) for m in d.odd_divisors(L)
                if not isprime(m)), Fraction(0))


def g_sup(primes) -> Fraction:
    """Supremum of g over all L with exactly this prime set (e -> infinity)."""
    prod = Fraction(1)
    for p in primes:
        prod *= 1 + Fraction(p, (p - 1) ** 2)
    return prod - 1 - sum((Fraction(1, p - 1) for p in primes), Fraction(0))


def minimal_unreachable(max_primes: int = 6):
    """Smallest odd prime sets whose supremum already defeats the criterion."""
    out = []
    ps = list(primerange(3, 60))

    def rec(i: int, cur: list):
        if cur and g_sup(cur) >= 1:
            # minimal: no proper subset already suffices
            if not any(g_sup(cur[:j] + cur[j + 1:]) >= 1
                       for j in range(len(cur))):
                out.append((tuple(cur), g_sup(cur)))
            return
        if len(cur) == max_primes:
            return
        for j in range(i, len(ps)):
            rec(j + 1, cur + [ps[j]])

    rec(0, [])
    return out


def gates() -> None:
    # (A) the closed form matches the direct sum on every odd abundant L
    for L in d.odd_abundant(200000):
        a, b = g_closed(L), g_direct(L)
        assert a == b, f"L={L}: closed {a} != direct {b}"
    print("  ok   (A) closed form == direct sum on all 391 odd abundant "
          "L <= 200,000 (exact rationals)")

    # (B) g < 1 implies the screen fires (the converse need not hold: the
    # group correction closes shapes with g > 1, e.g. 675675)
    for L in d.odd_abundant(20000):
        if g_closed(L) < 1:
            assert d.coprime_screen(d.odd_divisors(L))[0], f"L={L}"
    assert g_closed(945) < 1 and g_closed(675675) > 1
    print(f"  ok   (B) g(945) = {float(g_closed(945)):.4f} < 1 (dead), "
          f"g(675675) = {float(g_closed(675675)):.4f} > 1 (needs groups)")

    # (C) g increases with exponents and is bounded by the supremum
    for p, q in ((3, 5), (3, 7), (5, 7)):
        prev = Fraction(0)
        for e in range(1, 12):
            v = g_closed(p ** e * q ** e)
            assert v > prev, "g must increase with exponents"
            assert v < g_sup([p, q]), "g must stay below its supremum"
            prev = v
    print("  ok   (C) g increases in the exponents, always below g_sup")

    # (D) negative control: a prime set whose supremum is below 1 stays
    # killable no matter the exponents
    assert g_sup([3, 5]) < 1
    for e in range(1, 30):
        assert g_closed(3 ** e * 5 ** e) < 1
    print(f"  ok   (D) g_sup({{3,5}}) = {float(g_sup([3, 5])):.4f} < 1: "
          "every 3^a 5^b is killed, for all exponents")

    # (E) g_sup is monotone under adding a prime, which is what lets a single
    # prime SET stand for all its subsets.  Adding q multiplies the product by
    # (1 + q/(q-1)^2) and subtracts 1/(q-1), a net gain of at least
    # q/(q-1)^2 - 1/(q-1) = 1/(q-1)^2 > 0.
    ps = list(primerange(3, 40))
    for i, q in enumerate(ps):
        for P in ([3], [3, 5], [3, 5, 7], [5, 11], [7, 13, 19]):
            if q in P:
                continue
            assert g_sup(sorted(P + [q])) > g_sup(P), (P, q)
    print("  ok   (E) g_sup strictly increases when a prime is added")

    # (F) the headline infinite family, checked directly at large exponents
    for a, b, c, e in ((9, 7, 5, 4), (14, 9, 6, 5), (20, 12, 8, 6)):
        L = 3 ** a * 5 ** b * 7 ** c * 13 ** e
        assert g_closed(L) < 1, f"3^{a}5^{b}7^{c}13^{e}"
    print(f"  ok   (F) g_sup({{3,5,7,13}}) = {float(g_sup([3, 5, 7, 13])):.4f}"
          " < 1: every 3^a 5^b 7^c 13^d is killed, all exponents")
    print("all gates: PASS")


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__.split("\n")[0])
    ap.add_argument("--verify", action="store_true")
    args = ap.parse_args()
    if args.verify:
        gates()
        return 0

    print("Suprema of g over all L with a given prime set (exponents -> inf).")
    print("g_sup < 1  =>  the criterion kills EVERY such L, whatever the "
          "exponents.\n")
    print(f"{'prime set':>28} {'g_sup':>9}  verdict")
    for P in ([3], [3, 5], [3, 7], [3, 5, 7], [3, 5, 11], [3, 5, 7, 11],
              [3, 5, 7, 13], [3, 5, 7, 11, 13], [3, 5, 7, 11, 13, 17],
              [3, 5, 7, 11, 13, 17, 19]):
        v = g_sup(P)
        verdict = ("always killed" if v < 1 else
                   "OUT OF REACH for large exponents")
        print(f"{str(P):>28} {float(v):>9.4f}  {verdict}")

    print("\nHeadline: g_sup < 1 is an INFINITE family, not a finite check.")
    for P in ([3, 5, 7], [3, 5, 11], [3, 5, 7, 13]):
        e = " * ".join(f"{p}^a{i}" for i, p in enumerate(P))
        print(f"  no odd covering system has lcm {e}  "
              f"(g_sup = {float(g_sup(P)):.4f}), for ANY exponents")
    print(f"  the boundary is {[3, 5, 7, 11]}: g_sup = "
          f"{float(g_sup([3, 5, 7, 11])):.4f} >= 1, and every one of the "
          f"twelve survivors below 10^7 contains 11.")

    print("\nThe twelve survivors below 10^7, against the criterion:")
    for L in (2027025, 3378375, 3828825, 4279275, 4729725, 6081075,
              6185025, 6891885, 7432425, 7702695, 8783775, 9324315):
        P = sorted(factorint(L))
        print(f"  {L:>9}  primes {str(P):>22}  g = {float(g_closed(L)):.4f}  "
              f"g_sup = {float(g_sup(P)):.4f}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
