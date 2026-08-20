"""Check ||2^k|| = 2k and ||3^k|| = 3k against a computed A005245 table.

  * ||2^k|| = 2k is the open conjecture (Rawsthorne / Guy).  Only "<=" is a
    theorem; every k here is one more verified instance of the hard direction
    2k <= ||2^k||.
  * ||3^k|| = 3k is a theorem (the equality case of Selfridge's bound,
    `complexity_three_pow` in OpenProblemsLab/IntegerComplexity.lean), so it is
    a cross-check on the table rather than new information: a failure means the
    harness is broken.

    python verify_powers.py --limit 1000000
    python verify_powers.py --table table.npy
"""

from __future__ import annotations

import argparse

import numpy as np


def _powers(f: np.ndarray, base: int, factor: int):
    """(largest k verified, list of (k, computed, expected) failures)."""
    limit = len(f) - 1
    ok, bad, k, v = 0, [], 1, base
    while v <= limit:
        got = int(f[v])
        if got == factor * k:
            ok = k
        else:
            bad.append((k, got, factor * k))
        k += 1
        v *= base
    return ok, bad


def check(f: np.ndarray, verbose: bool = True) -> dict:
    limit = len(f) - 1
    ok2, bad2 = _powers(f, 2, 2)
    ok3, bad3 = _powers(f, 3, 3)
    if verbose:
        print(f"table covers n <= {limit:,}")
        print(f"  ||2^k|| = 2k  verified for 1 <= k <= {ok2} "
              f"(2^{ok2} = {2**ok2:,}); failures: {bad2 or 'none'}")
        print(f"  ||3^k|| = 3k  verified for 1 <= k <= {ok3} "
              f"(3^{ok3} = {3**ok3:,}); failures: {bad3 or 'none'}")
    if bad2:
        raise AssertionError(
            f"||2^k|| != 2k at {bad2} -- if the table is validated against "
            "OEIS this would be a counterexample to the conjecture; check the "
            "harness first")
    if bad3:
        raise AssertionError(f"||3^k|| != 3k at {bad3} -- the harness is broken "
                             "(this equality is a theorem)")
    return {"limit": limit, "max_k_two": ok2, "max_k_three": ok3}


def main() -> None:
    p = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    g = p.add_mutually_exclusive_group(required=True)
    g.add_argument("--limit", type=int, help="compute the table up to N first")
    g.add_argument("--table", type=str, help="load a table saved by complexity.py")
    args = p.parse_args()

    if args.table:
        f = np.load(args.table, mmap_mode="r")
    else:
        from complexity import integer_complexity_table
        f = integer_complexity_table(args.limit)
    check(f, verbose=True)


if __name__ == "__main__":
    main()
