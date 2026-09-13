"""Check the length-48 identity of T_5 from Bulatov, Karpova, Shur, Startsev.

Theorem 8 of "Lower Bounds on Words Separation: Are There Short Identities in
Transformation Semigroups?" (Electron. J. Combin. 24(3) (2017) #P3.35,
arXiv:1609.03199) says T_k satisfies

    (xy)^(k-2+L) (yx)^k (xy)^(k-1)  =  (xy)^(k-2) (yx)^k (xy)^(k-1+L),
    L = lcm(1..k-1),

of length 2L + 6(k-1).  For k = 5 that is two distinct binary words of length
48 that no 5-state DFA separates, so sep(48) >= 6 and N(5) <= 47.  This
contradicts the conjecture N(k) = 2k-3+lcm(1..k), which predicts N(5) = 67.

Checks (well under a second, single thread):
  (1) no canonical transition function on <= 5 states separates the pair
  (2) no random raw 5-state function, from any start state, separates it
      (independent of the canonical enumeration, which gate (A) in
      separate.py only checks for k <= 4)
  (3) control: the same shape with L = 11 IS separated by some <= 5-state one
  (4) control: some random 6-state function separates the length-48 pair
  (5) control: the DESW n = 18 pair has no <= 4-state separator, has a 5-state one

    python bkss_identity.py
"""

import math
import sys

import numpy as np

import separate as S


def identity5(k: int, L: int) -> tuple[str, str]:
    xy, yx = "01", "10"
    return (xy * (k - 2 + L) + yx * k + xy * (k - 1),
            xy * (k - 2) + yx * k + xy * (k - 1 + L))


def n_separating(T: np.ndarray, u: str, v: str) -> int:
    st = S.batch_states(T, np.stack([S.parse_word(u), S.parse_word(v)]))
    return int((st[:, 0] != st[:, 1]).sum())


def random_separating(k: int, u: str, v: str, m: int, all_starts: bool,
                      rng) -> tuple[int, int]:
    R = rng.integers(0, k, size=(m, k, 2), dtype=np.uint8)
    ar = np.arange(m)[:, None]
    starts = np.arange(k, dtype=np.uint8) if all_starts else np.zeros(1, np.uint8)
    cu = np.tile(starts, (m, 1))
    cv = cu.copy()
    for a in S.parse_word(u):
        cu = R[ar, cu, a]
    for a in S.parse_word(v):
        cv = R[ar, cv, a]
    return int((cu != cv).sum()), cu.size


def main() -> int:
    L = math.lcm(1, 2, 3, 4)
    u, v = identity5(5, L)
    assert len(u) == len(v) == 48 and u != v
    print(f"k=5, L=lcm(1..4)={L}, |u|=|v|={len(u)}")
    print(f"u = {u}\nv = {v}")

    T5 = S.icdfa_upto(5)
    got = n_separating(T5, u, v)
    print(f"(1) canonical <=5-state functions ({T5.shape[0]:,}) separating: {got}")
    assert got == 0

    rng = np.random.default_rng(20260912)
    got, tot = random_separating(5, u, v, 200_000, True, rng)
    print(f"(2) random raw 5-state (function, start) pairs separating: {got} of {tot:,}")
    assert got == 0

    u2, v2 = identity5(5, 11)
    got = n_separating(T5, u2, v2)
    print(f"(3) control L=11 (length {len(u2)}): <=5-state functions separating: {got}")
    assert got > 0

    got, tot = random_separating(6, u, v, 200_000, False, rng)
    print(f"(4) control: random 6-state functions separating the length-48 pair: {got} of {tot:,}")
    assert got > 0

    a, b = "111000000000000000", "111111111111111000"
    g4, g5 = n_separating(S.icdfa_upto(4), a, b), n_separating(T5, a, b)
    print(f"(5) control: DESW n=18 pair, <=4-state separators {g4}, <=5-state separators {g5}")
    assert g4 == 0 and g5 > 0

    print("=> sep(48) >= 6, so N(5) <= 47; the prediction N(5) = 67 is false")
    return 0


if __name__ == "__main__":
    sys.exit(main())
