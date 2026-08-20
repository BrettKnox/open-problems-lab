# Integer complexity: computation log

**This is validation infrastructure, not a record.** Everything below is far
inside the published frontier (see [Comparison to the literature](#comparison-to-the-literature)).
The point of this directory is to have a from-scratch, OEIS-validated table of
`||n||` that this repo controls end to end, so that later work on
`||2^n|| = 2n` has a trusted oracle to build on.

Run date: 2026-08-20.

## What was run

```
python complexity.py --limit 4294967296 --verify --selfcheck 20000 --audit 24
```

Verbatim output:

```
blocks=77 sweeps=88 max_cap=153 max_complexity=72
computed ||n|| for n <= 4,294,967,296 in 426.06 s (10.08 M n/s), max ||n|| = 72
self-check: matches the quadratic reference recurrence on n = 0..20,000 [0.1s]
OEIS A005245: exact agreement on n = 1..10,000 (10,000 terms, b-file has 10,000)
table covers n <= 4,294,967,296
  ||2^k|| = 2k  verified for 1 <= k <= 32 (2^32 = 4,294,967,296); failures: none
  ||3^k|| = 3k  verified for 1 <= k <= 20 (3^20 = 3,486,784,401); failures: none
recurrence audit: 27 random n in [2,147,483,648, 4,294,967,296] re-derived from
the full definition (all additive splits, no pruning) -- all match [71.9s]
```

Total wall clock 8m20s: 426 s table + 72 s audit + ~1 s for the other checks.

**Independently reproduced** on the same machine from a clean process, same
command: 448.42 s (9.58 M n/s), identical results — `||2^k|| = 2k` for
`k <= 32`, `||3^k|| = 3k` for `k <= 20`, OEIS exact on all 10,000 terms, all 27
audit points matching. Separately re-checked at `N = 2*10^8`: agreement with
`brute_force` on `n <= 25,000`, table invariance across block sizes
`1, 2, 7, 64, 4096, 2^20`, and a negative control (one entry decremented at
`n = 199,999,999`) correctly caught by the audit.

## Machine

| | |
|---|---|
| CPU | AMD Ryzen 7 7840HS (8 cores / 16 threads, 16 MiB L3) |
| RAM | 27.8 GiB (14.8 GiB free at launch) |
| OS | Windows 11 Pro 10.0.26200 |
| Python | 3.14.3 (CPython, 64-bit) |
| numpy | 2.5.0 |
| Threads used | 1 (numpy elementwise/reduction ops only; nothing here is parallel) |

Memory is one `int8` per integer: **4.00 GiB** of table at `N = 2^32`, plus
704 MiB of block workspace at the default block size `2^26` and up to ~320 MiB
of per-sweep temporaries — about **5 GiB peak**.

## Results

**N reached: 4,294,967,296 = 2^32.**

* `||2^k|| = 2k` verified for **1 <= k <= 32**, no failures. Only `<=` is a
  theorem (`complexity_two_pow_le` in `OpenProblemsLab/IntegerComplexity.lean`),
  so each k is one more instance of the hard direction `2k <= ||2^k||`, which is
  exactly what `conjecture_iff` isolates as the open content.
* `||3^k|| = 3k` verified for **1 <= k <= 20**, no failures. This one *is* a
  theorem (`complexity_three_pow`, the equality case of Selfridge's bound), so
  it is a cross-check on the harness, not new information — a failure here would
  mean the code is broken.
* `max ||n|| = 72` over `n <= 2^32`.
* The largest additive window the pruning ever needed was `cap = 153` (see
  below), against a naive additive range of up to `n/2 ~ 2.1e9`.

### Timing ladder

Single runs, table computation only (no checks), same machine:

| N | time | throughput | max ‖n‖ |
|---|---|---|---|
| 10^5 | 0.020 s | 5.0 M n/s | 39 |
| 10^6 | 0.055 s | 18.2 M n/s | 46 |
| 10^7 | 0.467 s | 21.4 M n/s | 53 |
| 10^8 | 6.88 s | 14.5 M n/s | 60 |
| 10^9 | 83.6 s | 12.0 M n/s | 67 |
| 2^32 | 426.1 s | 10.1 M n/s | 72 |

Scaling is close to linear with a slow decay from the divisor pass
(`sum_{d<=sqrt N} N/d`, i.e. an extra `~0.5 ln N`) and from falling out of
cache. Profiling one 2^26-wide block at `n ~ 2*10^8`: multiplicative pass 3.35 s,
additive relaxation 2.47 s, `a=1` closed form 0.18 s, selection masks 0.21 s.
The multiplicative pass is DRAM-bandwidth bound on strided writes, so it is the
natural next target if this ever needs to go further.

## Method, and why it is exact

Full detail is in the `complexity.py` module docstring. The two load-bearing
points:

1. **Additive pruning is a theorem, not a heuristic.** Selfridge's bound
   `n^3 <= 3^||n||` — proved in this repo as `cube_le_three_pow_complexity` —
   forces the smaller summand of any optimal additive split `n = a + b` to obey
   `a <= floor(icbrt(3^U) / ceil(n/2))` for any known upper bound `U >= ||n||`.
   The bound is evaluated in exact integer arithmetic (`icbrt` is an exact
   integer cube root; no floating point anywhere in the decision). Overestimating
   `U` only enlarges the window, so the pruning can never discard a split.
   Measured: the window is at most 153 over the whole range, versus `n/2`.
2. **Blocking makes the multiplicative pass trivial.** Blocks satisfy
   `R <= 2L`, so every cofactor `e = n/d <= n/2` of a block element is already
   final; the whole multiplicative minimum becomes one strided numpy write per
   divisor. What is left inside a block is the additive recurrence, solved by
   relaxation to a fixed point — the dependency graph is acyclic in `n`, so that
   fixed point is unique and equal to `||n||`. Chains of `+1` are collapsed in
   closed form by a running minimum of `f[n] - n`.

## Validation

Four gates, all passing. The first three ran in the `N = 2^32` job.

1. **OEIS A005245 b-file, exact agreement over the whole overlap.**
   `validate_oeis.py` fetches `https://oeis.org/A005245/b005245.txt` (cached
   locally, gitignored) and asserts equality term by term.
   **Overlap checked: n = 1 .. 10,000 — all 10,000 terms, which is the entire
   b-file.** Zero mismatches. The b-file is the binding constraint here: A005245
   publishes 10,000 terms, so OEIS cannot validate anything past `n = 10^4`.
2. **Independent brute force.** `brute_force()` implements the definition
   directly (`Theta(N^2)`, all additive splits, trial-division divisors) and
   shares no code path with the fast routine. Agreement on `n = 0..20,000` in
   the main run; separately cross-checked on `n = 0..30,000` across block sizes
   `1, 2, 3, 5, 64, 1000, 4096, 2^20` and across every limit in `1..39` plus the
   block-boundary limits `4095..4098, 8193..8195` — identical tables in all cases.
3. **Recurrence audit at large n.** This is the gate that matters, because OEIS
   stops at `10^4` where the pruning window is tiny. `complexity.audit()` picks
   random `n` in `[N/2, N]` (plus `N`, `N-1`, `N/2`) and recomputes `||n||` from
   the full definition — scanning **every** additive split `1 <= a <= n/2` with
   no pruning at all, plus all divisors — using the table for smaller values.
   27 values in `[2^31, 2^32]` re-derived; all matched. This directly tests the
   Selfridge window at the scale where it is actually doing work.
4. **Negative controls**, so the gates are not vacuous. Decrementing a single
   table entry was confirmed to be caught: at `n = 7777` by the OEIS check, at
   `n = 2^20` by the power check, and at `n = 1,999,999` by the audit
   ("table says 44, full recurrence says 45").

Caveats, stated plainly:

* Gates 1 and 2 only reach `n ~ 2*10^4`. Confidence above that rests on gate 3
  (random sampling, 27 points) plus the proof sketched above, not on exhaustive
  external comparison. A sampled audit is not a proof that all 4.3e9 entries are
  right; it is strong evidence.
* The table is `int8`. Correctness depends on `max ||n|| < 128`, which the code
  asserts per block (observed max 72 at `N = 2^32`, and `||n|| <= 3 log_2 n`
  keeps this safe well past `10^12`).
* Single-threaded, single machine, no independent re-run on other hardware.
* The 4.00 GiB table is not committed; regenerate with the command above.

## Comparison to the literature

**Nothing here is a record, and nothing here is new mathematics.**

* **`||2^k|| = 2k`.** He, [arXiv:2308.10301](https://arxiv.org/abs/2308.10301)
  (2023), verified `||2^i|| = 2i` for all `2^i <= 2^126`. This run reaches
  `k = 32`. That is **94 powers short**, and the gap is not a compute gap —
  He does not build a table of `||n||` up to `2^126` (that is physically
  impossible: it would be `8.5e37` bytes). Reaching `k = 126` requires the
  defect/stability machinery of Altman and Arias de Reyna
  ([arXiv:2111.00671](https://arxiv.org/abs/2111.00671),
  [arXiv:1606.03635](https://arxiv.org/abs/1606.03635)), which reasons about
  low-defect polynomials instead of enumerating integers. A dense table cannot
  be pushed there by any amount of hardware.
* **Tables of `||n||`.** Iraids, Balodis, Cernenoks, Opmanis, Opmanis and
  Podnieks computed `||n||` to roughly `10^12` ("Integer complexity:
  experimental and analytical results"). This run reaches `4.3e9`, about
  **230x short**, and theirs was a distributed computation with an out-of-core
  table. A single laptop process holding one byte per integer cannot reach
  `10^12` (that is 1 TB of RAM); getting there needs segmented/on-disk storage
  and many machines.

So: the correct description of this directory is a **fast, exact, OEIS-validated
reimplementation** that gives the repo its own trusted `||n||` oracle and a
reproducible harness, at a scale (`2^32`) chosen to fit in one laptop-minute
budget rather than to compete with anyone. It is a foundation for the attack
lane in the README ("extend Altman's k <= 48 stability computation; extend He's
power search"), not a step along it.

## Reproducing

```
cd computations/integer_complexity

# the full run logged above (~8.5 min, ~5 GiB RAM)
python complexity.py --limit 4294967296 --verify --selfcheck 20000 --audit 24

# a fast sanity pass (~1 s)
python complexity.py --limit 1000000 --verify --selfcheck 5000 --audit 8

# the pieces standalone
python complexity.py --limit 10000000 --out table.npy
python validate_oeis.py  --table table.npy
python verify_powers.py  --table table.npy
```

`validate_oeis.py` needs network access on first use to fetch the b-file; pass
`--bfile PATH` to run fully offline.
