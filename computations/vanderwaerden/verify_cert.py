"""Verify a van der Waerden lower-bound certificate: a coloring of [1, N]
with no monochromatic k-term arithmetic progression, hence W(r, k) > N.

Checker is exhaustive over all (start, difference) pairs — the literal
definition, no cyclic-structure shortcuts, independent of both the source
repository's C checker and the Lean check.
"""

from __future__ import annotations

import sys


def load(path: str) -> list[int]:
    txt = open(path).read()
    return [ord(c) - ord("a") for c in txt if c.isalpha()]


def largest_mono_ap(cols: list[int], kmax: int = 20) -> int:
    n = len(cols)
    best = 1
    for d in range(1, n):
        if 1 + best * d >= n and best >= kmax:
            break
        for a in range(n):
            if a + d >= n:
                break
            c = cols[a]
            k = 1
            while a + k * d < n and cols[a + k * d] == c:
                k += 1
            if k > best:
                best = k
    return best


def main() -> int:
    path, k = sys.argv[1], int(sys.argv[2])
    cols = load(path)
    r = len(set(cols))
    m = largest_mono_ap(cols)
    n = len(cols)
    ok = m < k
    print(f"{path}: length {n}, colors {r}, largest mono AP = {m} "
          f"-> {'certifies W(' + str(r) + ',' + str(k) + ') >= ' + str(n + 1) if ok else 'NOT a certificate'}")
    # negative control: flipping one color must create a mono k-AP or at least
    # be detected as changing the AP structure; we check the checker catches a
    # planted mono AP.
    planted = list(cols)
    d = 1
    for i in range(k):
        planted[100 + i * 7] = 0
    m2 = largest_mono_ap(planted)
    print(f"negative control (plant a mono {k}-AP): largest = {m2} -> "
          f"{'caught' if m2 >= k else 'NOT caught (!!)'}")
    return 0 if ok and m2 >= k else 1


if __name__ == "__main__":
    sys.exit(main())
