"""Validate a computed ||n|| table against the OEIS A005245 b-file.

The b-file (https://oeis.org/A005245/b005245.txt) is the reference table of
||n|| maintained by OEIS.  Agreement over the whole overlap is the gate: a
harness that disagrees with A005245 is worthless, so this asserts exact
equality on every term and reports the first divergence if there is one.

    python validate_oeis.py --limit 1000000
    python validate_oeis.py --table table.npy
    python validate_oeis.py --limit 100000 --bfile b005245.txt   # offline
"""

from __future__ import annotations

import argparse
import os
import urllib.request

import numpy as np

BFILE_URL = "https://oeis.org/A005245/b005245.txt"
CACHE = os.path.join(os.path.dirname(os.path.abspath(__file__)), "b005245.txt")


def load_bfile(path: str | None = None, url: str = BFILE_URL) -> np.ndarray:
    """Return the b-file as an array indexed by n (index 0 unused).

    Downloads to a local cache on first use; later runs are offline.
    """
    path = path or CACHE
    if not os.path.exists(path):
        req = urllib.request.Request(url, headers={"User-Agent": "OpenProblemsLab/1.0"})
        with urllib.request.urlopen(req, timeout=120) as r:
            data = r.read()
        with open(path, "wb") as fh:
            fh.write(data)
        print(f"downloaded {url} -> {path} ({len(data)} bytes)")
    ns, vs = [], []
    with open(path, "r", encoding="ascii") as fh:
        for line in fh:
            line = line.strip()
            if not line or line.startswith("#"):
                continue
            n, v = line.split()
            ns.append(int(n))
            vs.append(int(v))
    ns_arr = np.array(ns, dtype=np.int64)
    if not np.array_equal(ns_arr, np.arange(ns[0], ns[0] + len(ns))):
        raise ValueError("b-file indices are not contiguous")
    if ns[0] != 1:
        raise ValueError(f"b-file starts at n={ns[0]}, expected 1")
    out = np.zeros(len(vs) + 1, dtype=np.int16)
    out[1:] = vs
    return out


def check(f: np.ndarray, bpath: str | None = None, verbose: bool = True) -> int:
    """Assert f agrees with A005245 on the overlap. Returns the overlap length."""
    b = load_bfile(bpath)
    hi = min(len(b) - 1, len(f) - 1)
    if hi < 1:
        raise ValueError("no overlap with the b-file")
    mine = f[1:hi + 1].astype(np.int16)
    theirs = b[1:hi + 1]
    bad = np.flatnonzero(mine != theirs)
    if bad.size:
        first = int(bad[0]) + 1
        raise AssertionError(
            f"DISAGREES with A005245 at {bad.size} of {hi} terms; "
            f"first at n={first}: computed {int(mine[bad[0]])}, "
            f"OEIS {int(theirs[bad[0]])}"
        )
    if verbose:
        print(f"OEIS A005245: exact agreement on n = 1..{hi:,} "
              f"({hi:,} terms, b-file has {len(b)-1:,})")
    return hi


def main() -> None:
    p = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    g = p.add_mutually_exclusive_group(required=True)
    g.add_argument("--limit", type=int, help="compute the table up to N first")
    g.add_argument("--table", type=str, help="load a table saved by complexity.py")
    p.add_argument("--bfile", type=str, default=None, help="local b-file path")
    args = p.parse_args()

    if args.table:
        f = np.load(args.table, mmap_mode="r")
    else:
        from complexity import integer_complexity_table
        f = integer_complexity_table(args.limit)
    check(f, args.bfile, verbose=True)


if __name__ == "__main__":
    main()
