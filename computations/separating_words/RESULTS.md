# Separating words: computation log

Exact values of the separating-words function `sep(n)`: the least number of DFA
states that always suffices to distinguish two distinct binary words of length
`n`.

**Status of the numbers.** `n <= 18` **reproduces** the only published table
found (Tran, AFL 2023; see
[Comparison to the literature](#comparison-to-the-literature)). `n = 19..30`
appears to be **new**: no table beyond `n = 18` exists in the literature we
could find, and the sequence is not in OEIS. That is an extension of a small
exhaustive computation, not progress on the open problem. The gap between the
`Omega(log n)` lower bound and Chase's `O~(n^{1/3})` upper bound is untouched,
and nothing here is a step toward closing it.

Run date: 2026-08-20.

## What was run

```
python separate.py --nmax 30 --kmax 5 --save-cert cert_k5_n30.npy
python separate.py --check-cert cert_k5_n30.npy --nmax 30
python separate.py --verify --deep --negative-control --nmax 18 --kmax 5
```

Abridged output of the first (the full log is `run30.log`):

```
canonical initially-connected transition functions over {0,1}:
  k=1:          1   (of k^(2k) = 1)
  k=2:         12   (of k^(2k) = 16)
  k=3:        216   (of k^(2k) = 729)
  k=4:      5,248   (of k^(2k) = 65,536)
  k=5:    160,675   (of k^(2k) = 9,765,625)

    k=1: first unseparable pair at n=1: 0 / 1
N(1) = 0   [0.0s, 0 functions in the certificate]
    k=2: first unseparable pair at n=4: 0110 / 1010
N(2) = 3   [0.0s, 5 functions in the certificate]
    k=3: first unseparable pair at n=10: 1100000000 / 1111111100
N(3) = 9   [0.0s, 20 functions in the certificate]
    k=4: first unseparable pair at n=18: 111000000000000000 / 111111111111111000
N(4) = 17   [0.3s, 42 functions in the certificate]
    k=5: n=25 separated by 62 functions (+2)  [6.9s]
    k=5: n=26 separated by 65 functions (+3)  [14.2s]
    k=5: n=27 separated by 67 functions (+2)  [32.0s]
    k=5: n=28 separated by 70 functions (+3)  [69.6s]
    k=5: n=29 separated by 72 functions (+2)  [153.6s]
    k=5: n=30 separated by 74 functions (+2)  [356.4s]
N(5) >= 30 (search capped at n=30)   [639.3s, 74 functions in the certificate]
certificate for sep(n) <= 5 up to n=30 saved to cert_k5_n30.npy (74 transition functions)

sequence: 2, 2, 2, 3, 3, 3, 3, 3, 3, 4, 4, 4, 4, 4, 4, 4, 4, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5
total 640.4s
```

Total wall clock for the table: **10m 40s**. The certificate re-check is a
separate 4m 36s:

```
certificate cert_k5_n30.npy: 74 transition functions on 5 states; signatures of
all 1,073,741,824 words of length 30 are distinct -> sep(30) <= 5 VERIFIED  [276.2s]
```

**Independently reproduced** on the same machine: an earlier run with a
different random seed (`--seed 20260820` versus `--seed 7`) built a *different*
certificate, 75 functions instead of 74, sharing no construction path after
`n = 17`, and produced the **identical** `sep(n)` table and the identical
witness pairs, in 649.4 s. Both certificates were then re-verified at `n = 30`
from file (276.2 s and 279.3 s). The `N(k)` lower bounds for `k <= 4` are
exhaustive and carry no randomness at all.

## Machine

| | |
|---|---|
| CPU | AMD Ryzen 7 7840HS (8 cores / 16 threads, 16 MiB L3) |
| RAM | 27.8 GiB |
| OS | Windows 11 Pro 10.0.26200 |
| Python | 3.14.3 (CPython, 64-bit) |
| numpy | 2.5.0 |
| Threads used | 1 (numpy gathers and elementwise ops only; nothing here is parallel) |

Peak memory is one `uint64` signature hash per word of length `n`, plus a
sorted copy of one sixteenth of it: **~9 GiB at `n = 30`**, doubling with each
further `n`. That is the wall this method hits, not CPU time.

## Results

### `sep(n)` for `n = 1..30`

| n | 1 | 2 | 3 | 4 | 5 | 6 | 7 | 8 | 9 | 10 | 11 | 12 | 13 | 14 | 15 |
|---|---|---|---|---|---|---|---|---|---|----|----|----|----|----|----|
| **sep(n)** | 2 | 2 | 2 | 3 | 3 | 3 | 3 | 3 | 3 | 4 | 4 | 4 | 4 | 4 | 4 |

| n | 16 | 17 | 18 | 19 | 20 | 21 | 22 | 23 | 24 | 25 | 26 | 27 | 28 | 29 | 30 |
|---|----|----|----|----|----|----|----|----|----|----|----|----|----|----|----|
| **sep(n)** | 4 | 4 | 5 | 5 | 5 | 5 | 5 | 5 | 5 | 5 | 5 | 5 | 5 | 5 | 5 |

```
2, 2, 2, 3, 3, 3, 3, 3, 3, 4, 4, 4, 4, 4, 4, 4, 4, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5
```

Equivalently, in the compact form `N(k) = max { n : sep(n) <= k }`:

| k | 1 | 2 | 3 | 4 | 5 |
|---|---|---|---|---|---|
| **N(k)** | 0 | 3 | 9 | 17 | **>= 30** |
| gap `N(k)-N(k-1)` |  | 3 | 6 | 8 | >= 13 |

`N(1) = 0` is the statement that a one-state DFA accepts everything or nothing.
`N(2) = 3`, `N(3) = 9` and `N(4) = 17` are **exact**: at lengths 4, 10 and 18
respectively, *every* canonical transition function on at most 2, 3, 4 states
was run against the surviving words and none separates them. `N(5) >= 30` is a
search bound: the `k = 5` run was stopped by memory at `n = 30`, not by
finding a hard pair.

### The `round(sqrt(n))` near-miss, and why `n = 28` was worth computing

The first 27 terms coincide exactly with `round(sqrt(n+3))` (OEIS A000194
shifted by 3): runs of length 6 and 8 at the values 3 and 4 are exactly what
"`v` appears `2v` times" predicts, and that is also why the numeric OEIS search
for our prefix returns A000194. The prediction is `sep(28) = 6`.

**`sep(28) = 5`.** The run of fives is at least 13 long, not 10, so the
square-root law breaks at the first term past the published table. That is a
small thing, but it is the concrete payoff of extending it: on `n <= 27` alone
the data is perfectly consistent with a formula that is wrong.

### Hardest pairs

One witness per length, each verified independently by `verify_pair` (some
`sep(n)`-state function separates it, no smaller one does):

| n | sep(n) | witness |
|---|---|---|
| 1 | 2 | `0` / `1` |
| 4 | 3 | `0110` / `1010` |
| 10 | 4 | `1100000000` / `1111111100` = `1^2 0^8` / `1^8 0^2` |
| 18 | 5 | `111000000000000000` / `111111111111111000` = `1^3 0^15` / `1^15 0^3` |

For `n` between two jumps, appending a common suffix to the witness at the jump
works, since `minK(uw,vw) >= minK(u,v)` and `sep(n)` caps it from above.

### Every extremal pair, at each length where `sep` increases

`--census` refines the surviving words by **all** canonical transition
functions, so these lists are complete.

**`n = 4`, not separable by 2 states, 8 pairs:**

```
0001/0111  0001/1101  0010/1000  0010/1110
0101/1001  0110/1010  0111/1101  1000/1110
```

**`n = 10`, not separable by 3 states, 4 pairs:**

```
0000000011 / 0011111111        (0^8 1^2 / 0^2 1^8)
0000000100 / 0100000000        (single 1 at position 8 vs position 2)
1011111111 / 1111111011        (complement of the second)
1100000000 / 1111111100        (1^2 0^8 / 1^8 0^2)
```

**`n = 18`, not separable by 4 states, 4 pairs:**

```
000000000000000111 / 000111111111111111    (0^15 1^3 / 0^3 1^15)
000000000000001000 / 001000000000000000    (single 1 at position 15 vs position 3)
110111111111111111 / 111111111111110111    (complement of the second)
111000000000000000 / 111111111111111000    (1^3 0^15 / 1^15 0^3)
```

So at both `n = 10` and `n = 18` the extremal set is exactly two
complementation orbits (complementing both words is an alphabet relabelling,
so it preserves `minK`), one of shape `1^a 0^b` vs `1^b 0^a` and one of shape
"a single 1 in two different positions".

**Reversal is not a symmetry, at the extremal pairs.** This is the phenomenon
Demaine–Eisenstat–Shallit–Wilson study, and it shows up in the census:

```
minK(000000000000001000, 001000000000000000) = 5
minK(000100000000000000, 000000000000000100) = 4     <- the same pair reversed
```

The two-block pairs, by contrast, are self-reversing up to swapping `u` and
`v`, and keep `minK = 5`.

### The extremal pairs live in two tiny families

`--families` scans only `1^a 0^b` vs `1^b 0^a` and "single 1 at position `i`
vs position `j`": `O(n^2)` pairs instead of `4^n`. For **every** `n` from 2 to
30 the hardest pair inside those two families attains `sep(n)` exactly. So the
whole table could have been *guessed* in 16 seconds from `O(n^2)` pairs; what
the exhaustive search adds is turning the guess into a value, since a family
scan can only ever give lower bounds. Pushed further, the families still cap
at `minK = 5` through `n = 34`, which is suggestive of `N(5) > 34` and no
more.

### Timing

`k = 1..4` together take 0.3 s (through `n = 17`, plus the exhaustive
verification at `n = 18`). The whole cost is the `k = 5` upper bound. Per
level, on the machine below:

| n | time | functions in the certificate | words `2^n` |
|---|---|---|---|
| 20 | 0.2 s | 49 | 1.0 M |
| 22 | 0.8 s | 55 | 4.2 M |
| 24 | 3.3 s | 60 | 16.8 M |
| 26 | 14.2 s | 65 | 67 M |
| 28 | 69.6 s | 70 | 268 M |
| 29 | 153.6 s | 72 | 537 M |
| 30 | 356.4 s | 74 | 1,074 M |

Clean doubling per level, as it must be: the work is a constant number of
passes over `2^n` words. `n = 31` would need ~17 GiB and ~13 min, `n = 32`
~34 GiB, past this machine. Reaching `sep`'s next increase would need
`N(5)+1` to be within a few of 30, and the gaps (3, 6, 8, >= 13) give no reason
to expect that.

## Method

### 1. Accept sets are irrelevant

For a transition function `delta` on `k` states with start `q0`, write
`delta*(q0,w)` for the state reached on `w`. Then

> some `k`-state DFA separates `u` from `v`
> **iff** some `k`-state transition function and start state send `u` and `v`
> to *different* states.

Forward: acceptance depends only on the final state, so equal final states
means both accepted or both rejected. Backward: take the accept set to be the
singleton `{delta*(q0,u)}`. So the search never enumerates accept sets (a
factor `2^k`) and, more importantly, the question becomes one about **end
states**, which is what makes everything below work.

This reduction is *not assumed*. Gate (B) recomputes separability from the
literal definition (every transition function, every start state, every
accept set, acceptance tested directly) and compares.

### 2. Canonical transition functions

States unreachable from `q0` can be deleted, and relabelling states does not
change whether two runs end apart, so it suffices to enumerate *initially
connected* transition structures with `q0 = 0` and the other states numbered
in BFS order (letter 0 before letter 1), the canonical string of an ICDFA
(Almeida–Moreira–Reis). Generated directly, never by filtering:

| k | canonical | all `k^(2k)` | ratio |
|---|---|---|---|
| 1 | 1 | 1 | 1.0 |
| 2 | 12 | 16 | 1.3 |
| 3 | 216 | 729 | 3.4 |
| 4 | 5,248 | 65,536 | 12.5 |
| 5 | 160,675 | 9,765,625 | 60.8 |
| 6 | 5,931,540 | 2,176,782,336 | 367 |

Gate (A) checks this list against brute-force canonicalisation of all `k^(2k)`
functions for `k <= 4`.

### 3. The signature automaton

For a set `S` of transition functions define `sig_S(w) = (delta*(0,w))_{delta in S}`.
Each coordinate advances on its own, so `sig_S(wb)` depends only on `sig_S(w)`
and the letter `b`. The array of signatures of all `2^(t+1)` words of length
`t+1` is therefore one gather away from the array for length `t`:

```
row_{t+1}[2x + b] = delta(row_t[x], b)
```

Packing `(delta(q,0), delta(q,1))` into a `uint16` makes each doubling a single
gather whose two output bytes already land in the right order, so one
transition function's whole length-`n` array costs `2^n` gathers, not
`n * 2^n`, and with no strided writes. Two directions follow.

**Upper bound (cheap).** If `sig_S` is injective on `{0,1}^n` for some set `S`
of `k`-state functions, then `sep(n) <= k`. Information-theoretically `S` needs
at least `n / log2(k)` members; in practice the greedy search finds one about
5.7x that size (74 functions at `n = 30`, against a floor of 13). `S` is a
**certificate**: `--check-cert` re-verifies it in one pass without redoing the
search.

**Lower bound (the expensive half).** `sep(n) > k` iff `sig` over the *whole*
canonical list is non-injective. Running all 160,675 five-state functions over
`2^30` words is out of the question, so instead: refine with a growing `S`
until the surviving collision groups are tiny, then run **every** canonical
function on just those few words. A group that nothing splits is genuinely
unseparable, and its pairs are exactly the hardest pairs. When a sampled
function fixes a group it is used; the exhaustive sweep runs whenever the
sample fails, and *always* before concluding "unseparable".

### 4. `sep` is non-decreasing (a theorem, used to interpolate)

If `delta*(0,u) = delta*(0,v)` then `delta*(0,ub) = delta*(0,vb)`. Contrapositive:
anything separating `ub` from `vb` already separates `u` from `v`, so
`minK(ub,vb) >= minK(u,v)` and hence **`sep(n+1) >= sep(n)`**. Consequently
`{n : sep(n) <= k}` is an initial segment, the whole table is determined by

```
N(k) = max { n : sep(n) <= k },      sep(n) = min { k : N(k) >= n },
```

and one hard pair at length `N(k)+1`, padded with a common suffix, witnesses
every larger length up to `N(k+1)`. Gate (F) checks the monotonicity and the
suffix inequality empirically anyway.

## Validation

Six gates plus negative controls, run by
`python separate.py --verify --deep --negative-control --nmax 18 --kmax 5`.
Verbatim output:

```
--- validation gates ---
(A) canonical enumeration vs brute-force canonicalisation
  ok   icdfa k=1: 1 canonical transition functions
  ok   icdfa k=2: 12 canonical transition functions
  ok   icdfa k=3: 216 canonical transition functions
  ok   icdfa k=4: 5248 canonical transition functions
(B) accept-set reduction, exhaustive over all pairs and all DFAs
  ok   reduction n=1 k=3: 1 pairs, 17,496 literal DFAs  [0.0s]
  ok   reduction n=2 k=3: 6 pairs, 17,496 literal DFAs  [0.0s]
  ok   reduction n=3 k=3: 28 pairs, 17,496 literal DFAs  [0.0s]
  ok   reduction n=4 k=3: 120 pairs, 17,496 literal DFAs  [0.0s]
  ok   reduction n=5 k=3: 496 pairs, 17,496 literal DFAs  [0.0s]
  ok   reduction n=6 k=3: 2016 pairs, 17,496 literal DFAs  [0.0s]
  ok   reduction n=7 k=3: 8128 pairs, 17,496 literal DFAs  [0.1s]
  ok   reduction n=1 k=4: 1 pairs, 4,194,304 literal DFAs  [0.1s]
  ok   reduction n=2 k=4: 6 pairs, 4,194,304 literal DFAs  [0.3s]
  ok   reduction n=3 k=4: 28 pairs, 4,194,304 literal DFAs  [0.4s]
  ok   reduction n=4 k=4: 120 pairs, 4,194,304 literal DFAs  [0.9s]
  ok   reduction n=5 k=4: 496 pairs, 4,194,304 literal DFAs  [2.2s]
  ok   reduction n=8 k=3: 32640 pairs, 17,496 literal DFAs  [0.3s]
  ok   reduction n=6 k=4: 2016 pairs, 4,194,304 literal DFAs  [6.5s]
  ok   reduction n=7 k=4: 8128 pairs, 4,194,304 literal DFAs  [20.8s]
  ok   reduction n=8 k=4: 32640 pairs, 4,194,304 literal DFAs  [74.9s]
(C) fast minK vs literal minK on random pairs
  ok   40 random pairs: fast minK == literal minK (k <= 4)
(D) sep(n) from the literal definition, tiny n
  ok   literal sep(n) for n <= 7: [2, 2, 2, 3, 3, 3, 3] vs computed [2, 2, 2, 3, 3, 3, 3]
(E) literal reference on the hardest pairs
  ok   n=1  0/1: literal minK = 2 (claimed 2); 130 DFAs enumerated [0.0s]
  ok   n=4  0110/1010: literal minK = 3 (claimed 3); 17,626 DFAs enumerated [0.0s]
  ok   n=10 1100000000/1111111100: literal minK = 4 (claimed 4); 4,211,930 DFAs enumerated [0.0s]
  ok   n=18 111000000000000000/111111111111111000: literal minK = 5 (claimed 5); 1,566,711,930 DFAs enumerated [0.5s]
(F) structural sanity
  ok   sep(n) non-decreasing over the computed range
  ok   200 pairs: minK <= i+2 for first difference at position i
  ok   50 pairs: minK(uw,vw) >= minK(u,v)
  ok   minK >= 2 always (a 1-state DFA accepts everything or nothing)

all gates: PASS

--- negative controls (each gate must catch a corrupted result) ---
  control 1: one transition flipped in the k=3 canonical list
  FAIL icdfa k=3: 215 generated vs 216 canonical
    -> CAUGHT
  control 2: delete the 73 k=3 functions that separate 0110/1010
    -> fast says None, literal reference says 3: CAUGHT
  control 3 (n=1): claim minK(0,1)=1
    -> true claim 2: accepted (2-state witness, runs end in states 0 != 1)
    -> false claim 1: CAUGHT (no transition function on <= 1 states separates them)
  control 4: claim sep(4) <= 2
    -> exhaustive search over all <= 2-state functions gives N(2)=3 < 4: CAUGHT

negative controls: PASS (every corruption caught)
```

Reading the gates:

1. **(A) Canonical enumeration.** The generated ICDFA list equals the set of
   BFS-canonical forms of all `k^(2k)` transition functions, for `k <= 4`.
   A wrong symmetry reduction would silently inflate `minK`; this catches it.
2. **(B) The reduction, exhaustively.** For every pair of words of length
   `n <= 8` and every DFA on `k <= 4` states (**all** `4,194,304` of them at
   `k = 4`, counting each transition function, each start state and each of
   the 16 accept sets separately, with acceptance tested directly), literal
   separability agrees with end-state separability over canonical functions on
   every one of the 32,640 pairs. This is the gate that independently tests
   the key reduction; if the reduction were wrong, it fails.
3. **(C, D)** The fast `minK` agrees with the literal all-DFA reference on
   random pairs, and `sep(n)` computed from the literal definition alone
   agrees for `n <= 7`.
4. **(E) The hardest pairs, from the definition.** Each witness is re-derived
   by the literal reference. The headline lower bound `sep(18) > 4` is
   confirmed by enumerating **1,566,711,930** DFAs (all transition functions,
   start states and accept sets on up to 5 states) and finding that none of
   the `<= 4`-state ones separates `1^3 0^15` from `1^15 0^3`.
5. **(F) Structure.** `sep` non-decreasing; `minK <= i+2` when the first
   difference is at position `i`; `minK(uw,vw) >= minK(u,v)`; `minK >= 2`
   always.

**Negative controls.** Each gate is shown to be non-vacuous by corrupting the
result it guards: a single flipped transition in the canonical list, deletion
of exactly the functions that separate a witness pair, a claim that a witness
needs one state fewer than it does, and a claim that `sep(n) <= sep(n)-1`. All
four are caught. A fifth, in the same spirit: the certificate for `n = 20`
correctly **refuses** to verify `n = 22`
(`--check-cert cert.npy --nmax 22` reports "NOT distinct -> claim REFUTED").

Consistency with the known asymptotics: `sep(n) = Omega(log n)` and
`O~(n^{1/3})` are both far too loose to constrain anything at `n <= 30`
(Chase's bound is in the thousands there), so they are satisfied vacuously and
provide no independent check. The binding external check is the published
table.

## Comparison to the literature

**`n <= 18`: MATCHES published values. `n >= 19`: no published values found.**

* **Tran, "Separating Words from Every Start State with Horner Automata",
  AFL 2023, EPTCS 386, 243–252**
  ([doi:10.4204/EPTCS.386.19](https://doi.org/10.4204/EPTCS.386.19),
  [arXiv:2309.02766](https://arxiv.org/abs/2309.02766), open access). Table 1,
  "Values of D∃(n) and D∀(n) for 1 <= n <= 18", obtained "via exhaustive
  search" with a C++ program on an i7-4790S. `D∃` is our `sep`: Tran defines
  separation as ending in different states from a common start state, the
  same reduction used here, over "two distinct strings of length n", the
  **exactly-`n`** convention. His `D∃` row is

  ```
  n     1 2 3 4 5 6 7 8 9 10 11 12 13 14 15 16 17 18
  D∃(n) 2 2 2 3 3 3 3 3 3  4  4  4  4  4  4  4  4  5
  ```

  **All 18 terms agree with this computation, exactly.** This is the strongest
  external check in the whole file: an independent implementation, in a
  different language, by a different author, published in 2023. `D∀(n)` in the same table is a *different* quantity (different end
  states from *every* start state) and is not what is computed here.
* **Shallit's lecture slides** carry the identical table under "Some data:":
  [sep2.pdf](https://cs.uwaterloo.ca/~shallit/Talks/sep2.pdf) (slide 29),
  [open10r.pdf](https://cs.uwaterloo.ca/~shallit/Talks/open10r.pdf) (slide 13),
  [hawaii2.pdf](https://cs.uwaterloo.ca/~shallit/Talks/hawaii2.pdf) (slide 35),
  with `S(n)` defined over `|w| = |x| = n`. No method or attribution is given
  and slides are not a publication, but they predate Tran and are presumably
  the same data.
* **Demaine, Eisenstat, Shallit, Wilson, "Remarks on separating words"**
  (DCFS 2011, [arXiv:1103.4513](https://arxiv.org/abs/1103.4513))
  **contains no table**, checked against the full extracted text of v1. It
  does state isolated values, and they agree with ours:
  `sep(1000, 0010) = 3` and `sep(0001, 0111) = 3` (both reproduced by
  `--pair`; `0010/1000` is in fact one of our eight extremal pairs at `n = 4`).
  The paper also redefines `S(n)` from "length at most n" to "length exactly
  n", which is the convention used here and by Tran.
* **OEIS: absent.** Searched independently of the literature agent. The
  numeric query
  [`2,2,2,3,3,3,3,3,3,4,4,4,4,4,4,4,4,5,5,5,5,5,5,5`](https://oeis.org/search?q=2,2,2,3,3,3,3,3,3,4,4,4,4,4,4,4,4,5,5,5,5,5,5,5)
  returns six hits, all coincidental supersequences of round-square-root type
  (A000194 and relatives); the full-text queries `separating words`,
  `separating words automaton` and `smallest DFA distinguish` return nothing
  about DFA separation. **No A-number matches**, so there is no term-by-term
  OEIS comparison to make. The sequence looks submittable.
* **Bounds, for context, none of which this touches:** Goralčík–Koubek 1986
  (`o(n)`), Robson 1989 (`O(n^{2/5} log^{3/5} n)`), Chase, STOC 2021
  (`O~(n^{1/3})`, [arXiv:2007.12097](https://arxiv.org/abs/2007.12097)),
  lower bound `Omega(log n)` (DESW 2011). A claimed `O(log^2 n)` improvement,
  [arXiv:2503.23184](https://arxiv.org/abs/2503.23184), was **withdrawn** by
  its author in April 2025.
* **No SAT-based computation of `sep(n)` was found**; Tran's is an exhaustive
  C++ search and this one is exhaustive numpy. The README's attack lane says
  "exact small-n values via SAT (no published table exists)": the second half
  of that is **wrong** and should be corrected: a table for `n <= 18` was
  published in 2023.

### So what is actually new here

Modest, and worth stating plainly:

1. **`sep(n)` for `n = 19..30`** (12 terms), with the `n <= 18` values
   independently reproduced rather than assumed.
2. **`N(4) = 17` and `N(5) >= 30`** as the compact form of the table.
3. **A census of the extremal pairs** at the lengths where `sep` increases
   (above). No published table of these exists.
4. **Machine-checkable certificates**: the upper bounds are re-verifiable in
   one pass from a saved file, and the lower bounds are single pairs whose
   hardness any independent implementation can confirm in milliseconds.

None of this bears on the `log n` versus `n^{1/3}` question. `n = 30` is not
remotely large enough to distinguish those, and the method cannot be pushed
much further: each additional `n` doubles both time and memory.

## Caveats

* **Search bound, not a value.** `N(5)` is only pinned from below. `sep(n)`
  for `n > 30` is not computed. The family probe reaching `n = 34` without
  passing 5 is suggestive, nothing more: it searches `O(n^2)` pairs out of
  `4^n`, so it can only ever produce lower bounds on `sep`.
* **Signature hashes can collide.** Collision groups proposed by the 64-bit
  hash are re-checked against actual signature vectors before being believed.
  Equal signatures always hash equal, so no collision is missed; a hash
  collision only wastes work.
* **The greedy certificate is not minimal.** 74 functions where 13 would
  suffice information-theoretically. That costs time and nothing else: an
  over-large certificate can only fail to prove an upper bound, never assert a
  false one.
* **Single machine, single-threaded, one implementation.** The external check
  on `n <= 18` (Tran) is real; `n = 19..30` rests on this code plus its gates,
  reproduced only here.
* `icdfa_cache/` (~72 MiB at `k = 6`) and the `.npy` certificates are
  regenerated by the commands below and need not be committed.

## Reproducing

```
cd computations/separating_words

# the full table (~11 min, ~9 GiB at n = 30)
python separate.py --nmax 30 --kmax 5 --save-cert cert_k5_n30.npy

# re-verify the upper bound from the certificate alone, no search
python separate.py --check-cert cert_k5_n30.npy --nmax 30

# all validation gates and negative controls (~2 min)
python separate.py --verify --deep --negative-control --nmax 18 --kmax 5

# one pair, with the witness automaton and the literal all-DFA reference
python separate.py --pair 111000000000000000 111111111111111000 --brute

# every pair that no <= k-state DFA separates, at a given length
python separate.py --kmax 4 --census 18

# structured hard-pair families (O(n^2) pairs, seconds)
python separate.py --families 34 --kmax 5
```

A fast sanity pass, a few seconds:

```
python separate.py --nmax 20 --kmax 5 --verify
```

## SW-5: N(k), and a sharp conjecture for where 5 states run out

`N(k)` is the largest `n` such that some `k`-state DFA separates every pair of
distinct binary words of length `n` -- the inverse view of `sep`. Exhaustive
search gives `N(1) = 0`, `N(2) = 3`, `N(3) = 9`, `N(4) = 17`, and stalls at
`N(5) >= 30`: deciding `n = 31` needs a collision check over all `2^n`
signatures, about 17 GiB.

**Verifying and witnessing are not equally hard.** A witness is one unseparable
pair, and the known ones are extremely structured -- `1^2 0^8` vs `1^8 0^2` at
`n = 10`, `1^3 0^15` vs `1^15 0^3` at `n = 18`. Both are two-block words
`1^a 0^(n-a)`, a family with only `n + 1` members per length, so it can be
pushed far past exhaustive range. `blocks.py` evaluates it in
`O(#functions * n)` by iterating the `0`-map once and indexing into it, rather
than running each word.

### The construction is known; the tightness is the news

Searching the two-block family and asking *why* it works recovers a theorem
already in the literature -- **Theorem 1 of Demaine, Eisenstat, Shallit and
Wilson** ([arXiv:1103.4513](https://arxiv.org/abs/1103.4513), 2011): no DFA of
at most `k` states separates `0^(k-1) 1^(k-1+L)` from `0^(k-1+L) 1^(k-1)`,
where `L = lcm(1, ..., k)`. The orbit of any state under one letter has tail
`<= k-1` and cycle length dividing `L`, so shifting a block by `L` is
invisible. That gives

    N(k)  <=  2k - 3 + lcm(1, ..., k).

This was re-derived here before the source was found; it is theirs, and the
asymptotic content (the classical `Omega(log n)` lower bound on `sep`) is
theirs too.

What does not appear in the literature is that **the bound is exact wherever
anything is known**:

| k | 2k-3+lcm(1..k) | N(k), exhaustive |
|---|---|---|
| 1 | 0 | 0 |
| 2 | 3 | 3 |
| 3 | 9 | 9 |
| 4 | 17 | 17 |
| 5 | **67** | `>= 30`, `<= 67` |

Four for four, witnesses included: the construction's pair at `k = 3` is
exactly `1^2 0^8 / 1^8 0^2`, and at `k = 4` exactly `1^3 0^15 / 1^15 0^3` --
the same pairs exhaustive search finds. That suggests

> **Conjecture.** `N(k) = 2k - 3 + lcm(1, ..., k)`, equivalently `sep(n) = 5`
> for exactly `18 <= n <= 67`, with `sep(68) = 6`.

### Evidence for N(5) = 67

* The upper bound `N(5) <= 67` is **proved** (the DESW pair at `n = 68` is
  `1^4 0^64 / 1^64 0^4`; `min_states` independently confirms it needs 6
  states).
* The two-block family's first collision is at **exactly** `n = 68` -- nothing
  earlier, scanned from `n = 20`.
* The three-block family `1^a 0^b 1^c` also first collides at **exactly**
  `n = 68`, at `1^3 0^1 1^64` vs `1^63 0^1 1^4` -- again two indices differing
  by `L = 60`. Scanned over every `(a, b, c)` for `n <= 71`.
* Exhaustive search over **all** words confirms no collision at all for
  `n <= 30`, so the prediction `sep(n) = 5` is verified for the 13 lengths
  `18 <= n <= 30` -- beyond the `n <= 18` the formula was fitted on.

The gap `31 <= n <= 67` is what would have to be closed to prove `N(5) = 67`,
and the memory wall makes that unreachable by the exhaustive route. Closing it
needs an argument that the extremal pairs are always of this periodic type,
which is the open content of the conjecture rather than a computation.

Gates (`python blocks.py --verify`): the family reproduces both known
witnesses; those witnesses need strictly more than `k` states via an
independent `min_states` path; the fast two-block and three-block sweeps agree
with `batch_states` on the same words; no collision at `n = 9` for `k = 3, 4`
(negative control, since `N(3) = 9`); and the formula reproduces `N(1..4)`.
