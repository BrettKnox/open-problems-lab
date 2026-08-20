"""Verify a claimed superpermutation: every permutation of 1..n occurs as a
contiguous substring. Independent of the Lean check (different algorithm:
sliding-window set collection vs per-permutation find)."""

from __future__ import annotations

import sys
from itertools import permutations


def check(word: str, n: int) -> tuple[bool, int]:
    """(is superpermutation, number of distinct permutations found)."""
    need = {"".join(p) for p in permutations("123456789"[:n])}
    seen = set()
    for i in range(len(word) - n + 1):
        w = word[i : i + n]
        if w in need:
            seen.add(w)
    return seen == need, len(seen)


def main() -> int:
    path, n = sys.argv[1], int(sys.argv[2])
    word = open(path).read().strip()
    ok, found = check(word, n)
    total = 1
    for k in range(2, n + 1):
        total *= k
    print(f"length {len(word)}, permutations found {found}/{total}: "
          f"{'SUPERPERMUTATION' if ok else 'NOT a superpermutation'}")
    # negative control: damaging one character must break it
    bad = word[:100] + ("1" if word[100] != "1" else "2") + word[101:]
    ok2, found2 = check(bad, n)
    print(f"negative control (flip char 100): {found2}/{total} -> "
          f"{'NOT caught (!!)' if ok2 else 'caught'}")
    return 0 if ok and not ok2 else 1


if __name__ == "__main__":
    sys.exit(main())
