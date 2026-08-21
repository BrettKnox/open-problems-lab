# Open Problems Lab

A working list of open problems in mathematics and computational theory that this project
is actively attacking, each with a machine-checked formal statement in Lean 4 (mathlib).
The goal is real contributions: proofs, disproofs, record extensions, and formalizations
of known partial results — on problems chosen because they are precisely statable,
genuinely open, and quietly attended, not because they are famous.

**Every problem here has its statement formalized in [`OpenProblemsLab/`](OpenProblemsLab/)
and CI enforces that everything compiles.** A compiling statement is the entry ticket: it
pins down exactly what would count as a resolution before any work starts.

## Selection criteria

1. **Precisely statable** — a single `Prop` in Lean, no hand-waving.
2. **Open** — status verified against current literature, erdosproblems.com, and arXiv
   as of **2026-08-19** (dates matter: several candidates were dropped after this check).
3. **Quiet** — few active researchers, no heavyweight group currently cranking on it.
   Dropped for heat: lonely runner (solved through 13 runners in 2025–26), Gilbreath
   (Chase–Hunter–Tao, July 2026), no-three-in-line records (Heule, Aug 2026), R(5,5),
   Erdős–Straus (crowded).
4. **Incrementally attackable** — a concrete lane exists: computational verification,
   record construction, SAT search, or formalization of known partial results.

## The list

Tier A = own-the-niche (novel results plausible), B = structured search with real odds,
C = stretch / compute records. EP = [erdosproblems.com](https://www.erdosproblems.com),
FC = [formal-conjectures](https://github.com/google-deepmind/formal-conjectures).

| # | Problem | Tier | Lean file | Last substantial progress | Attack lane |
|---|---------|------|-----------|---------------------------|-------------|
| 1 | **Integer complexity** ‖2ⁿ‖ = 2n | A | [IntegerComplexity.lean](OpenProblemsLab/IntegerComplexity.lean) | Altman–Arias de Reyna 2026 ([2111.00671](https://arxiv.org/abs/2111.00671)); search to 2¹²⁶ (He, [2308.10301](https://arxiv.org/abs/2308.10301)) | **In progress — see [Results](#results).** Extend Altman k≤48 stability + He's search. ~2 researchers worldwide |
| 2 | **Separating words** | A | [SeparatingWords.lean](OpenProblemsLab/SeparatingWords.lean) | Chase, STOC 2021: O(n^⅓ log⁷ n); 2025 improvement claim withdrawn; exact values n ≤ 18 (Tran, [AFL 2023](https://arxiv.org/abs/2309.02766)) | **In progress — see [Results](#results).** Extend the exact table; log n vs n^⅓ gap wide open |
| 3 | **Erdős–Gyárfás** (min deg 3 ⟹ 2ᵏ-cycle) | A | [ErdosGyarfas.lean](OpenProblemsLab/ErdosGyarfas.lean) | General: ≥ 32 (Balaji 2026, unrefereed SAT); cubic: ≥ 30 (Markström 2004); cubic bipartite: ≥ 60 (Tranquilli, [2608.02675](https://arxiv.org/abs/2608.02675)) | **In progress — see [Results](#results).** Extend the cubic record; independently verify the unrefereed general record |
| 4 | **EP [#414](https://www.erdosproblems.com/414)**: n ↦ n+τ(n) trajectories merge? | A | [TauTrajectories.lean](OpenProblemsLab/TauTrajectories.lean) | Erdős–Graham 1980; nothing since | **In progress — see [Results](#results).** Zero competition. Census + parity structure |
| 5 | **Superpermutations**, L(6) = 872? | A | [Superpermutations.lean](OpenProblemsLab/Superpermutations.lean) | Houston 872 (2014); Houston–Egan–anon lower bound 867 (2019); dormant since 2021 | **In progress — see [Results](#results).** Rule out 871 via modern SAT + proof logging (untried) |
| 6 | **Antimagic labeling** (Hartsfield–Ringel) | A | [Antimagic.lean](OpenProblemsLab/Antimagic.lean) | Regular graphs 2015–16; subdivisions ([2608.11723](https://arxiv.org/abs/2608.11723)) | **In progress — see [Results](#results).** Small-graph sweep; degree-2-heavy trees |
| 7 | **Graceful tree conjecture** | A | [GracefulTrees.lean](OpenProblemsLab/GracefulTrees.lean) | Verified ≤35 vertices (Fang 2010, [1003.3045](https://arxiv.org/abs/1003.3045)) — record untouched 16 years | **In progress — see [Results](#results).** Push exhaustive verification (embarrassingly parallel) |
| 8 | **W(2,7)** van der Waerden | A | [VanDerWaerden.lean](OpenProblemsLab/VanDerWaerden.lean) | W(2,6)=1132 (Kouril–Paul 2008); W(2,7) > 3703 (Rabung–Lotts, [E-JC 19(2) #P35](https://www.combinatorics.org/ojs/index.php/eljc/article/view/v19i2p35)) | **In progress — see [Results](#results).** Lower-bound records via SAT + cyclic zipper |
| 9 | **Odd covering systems** (EP [#7](https://www.erdosproblems.com/7); $25/$2000) | B | [OddCovering.lean](OpenProblemsLab/OddCovering.lean) | BBMST 2022: no odd squarefree covering; lcm divisible by 9 or 15 | Search admissible lcm shapes; LP density bounds |
| 10 | **Distinct subset sums** (EP [#1](https://www.erdosproblems.com/1), $500) | B | [DistinctSubsetSums.lean](OpenProblemsLab/DistinctSubsetSums.lean) | Dubroff–Fox–Xu 2021 lower bound; Bohman 0.22002·2ⁿ construction | Beat Bohman's constant by search; formalize DFX |
| 11 | **Erdős–Moser** 1ᵏ+⋯+(m−1)ᵏ = mᵏ | C | [ErdosMoser.lean](OpenProblemsLab/ErdosMoser.lean) | GMZ 2011: m > 10^(10⁹) via CF of log 2 | Extend the CF computation past 10^(10¹⁰); formalize Moser's odd-k proof |
| 12 | **Lehmer's totient problem** | C | [LehmerTotient.lean](OpenProblemsLab/LehmerTotient.lean) | Cohen–Hagis 1980 (n>10²⁰, ω≥14); Burek–Żmija 2019 | **In progress — see [Results](#results).** Modern sweep; formalize Cohen–Hagis framework |

## Results

### 1. Integer complexity, ‖2ⁿ‖ = 2n

A formalization of integer complexity in
[IntegerComplexity.lean](OpenProblemsLab/IntegerComplexity.lean), with no prior one known:
the notion is absent from mathlib and from DeepMind's formal-conjectures, and we could find
no published formalization. No `sorry`; the only axioms used are `propext`,
`Classical.choice`, `Quot.sound`.

- **Selfridge's lower bound**, in the sharp integer form `n³ ≤ 3^‖n‖` (and the logarithmic
  form `‖n‖ ≥ 3·log₃ n`). Proved by structural induction on expressions.
- **‖3ᵏ‖ = 3k** for k ≥ 1 — the exact equality case of that bound.
- **The conjecture itself, proved for n ≤ 9.** Selfridge's bound alone rules out any
  expression of size below 2n for 2ⁿ up to n = 9, where it is tight to within 4%
  (3¹⁷ = 129140163 < 134217728 = 8⁹). At n = 10 it reverses, so 10 and beyond need
  genuinely new input. This is far short of He's computational verification to 2¹²⁶, but
  it is a proof rather than a computation, and it is the first formal one.
- **`conjecture_iff`**: since ‖2ⁿ‖ ≤ 2n is proved, the conjecture reduces exactly to the
  lower bound 2n ≤ ‖2ⁿ‖. Everything open lives in the gap between 1.892n and 2n.
- The **defect** δ(n) = ‖n‖ − 3·log₃ n and **stability** — the Altman–Zelinsky vocabulary
  the known partial results are stated in — with their basic lemmas, as the foundation for
  pushing past n = 9. In particular `conjecture_iff_defect`: **the conjecture is exactly
  the statement that δ(2ᵏ) = k·δ(2)**, i.e. that the increment δ(2) ≈ 0.107 is never
  beaten. That is the form Altman's machinery operates on, since the defect (not the
  complexity) is the invariant with a structure theory.

The file also documents a route that was **measured and rejected**: verifying more values
of n by computation inside Lean. Each level is an O(N²) min-plus convolution, so it caps
out near n = 10–11 for a large amount of proof work plus a `native_decide` trust
assumption. Getting further formally means formalizing the theory, not out-computing it.

**Computationally** ([computations/integer_complexity/](computations/integer_complexity/),
log in [RESULTS.md](computations/integer_complexity/RESULTS.md)): an exact table of ‖n‖ to
**n = 2³² = 4,294,967,296** in 426 s single-threaded, confirming **‖2ᵏ‖ = 2k for k ≤ 32**.
The additive search is pruned by the Selfridge bound proved above — it forces the smaller
summand of an optimal split to satisfy a ≤ ∛(3^U)/⌈n/2⌉, a window measured at **≤ 153**
against a naive n/2 ≈ 2.1×10⁹ — in exact integer arithmetic, so the table stays exact.

Four validation gates, all passing: exact agreement with **all 10,000 terms** of the OEIS
A005245 b-file; agreement with an independent brute-force implementation of the definition
(sharing no code path) on n ≤ 30,000 and across block sizes; a **large-n audit** that
re-derives ‖n‖ for random n ∈ [2³¹, 2³²] from the full definition scanning *every* additive
split with no pruning; and **negative controls** confirming a single corrupted entry is
caught, so the gates are not vacuous.

This is a trusted oracle, **not a record**. He ([2308.10301](https://arxiv.org/abs/2308.10301))
verified ‖2ⁱ‖ = 2i to 2¹²⁶ — 94 powers further, and unreachable by any dense table, since
that needs the defect machinery rather than enumeration. Iraids et al. tabulated ‖n‖ to
~10¹², about 230× further, on a distributed out-of-core computation.

### 2. Separating words

In [SeparatingWords.lean](OpenProblemsLab/SeparatingWords.lean). No `sorry`; standard axioms
only.

- **The accept set is irrelevant** (`exists_separates_iff_exists_eval_ne`): a k-state DFA
  separating u from v exists exactly when some k-state *transition function* sends them to
  different states — given that, accept precisely the state u lands in. This is the lemma
  that makes exhaustive search practical, since it removes the 2ᵏ accept-set factor
  entirely; the computation below enumerates transition functions only.
- **`sep n ≤ n + 2`**, via a counter that latches on the symbol at the first position where
  the words differ. Weak as a bound, but it is what makes `sep` *well defined*: without a
  construction the infimum ranges over an empty set and `sep n` would silently be 0.
- **`2 ≤ sep n`** for n ≥ 1 — one state distinguishes nothing.

**Computationally** ([computations/separating_words/](computations/separating_words/), log in
[RESULTS.md](computations/separating_words/RESULTS.md)): exact values of sep(n) for
**n ≤ 30**, using the reduction above to enumerate transition functions only.

```
n      1 2 3 4 5 6 7 8 9 10 11 12 13 14 15 16 17 18 19 ... 30
sep(n) 2 2 2 3 3 3 3 3 3  4  4  4  4  4  4  4  4  5  5 ...  5
```

For **n ≤ 18 this reproduces the one published table**, Tran, [AFL 2023](https://arxiv.org/abs/2309.02766)
(EPTCS 386, Table 1, D∃(n)), term for term and under the same convention — an earlier version
of this README wrongly said no such table existed. **n = 19..30 extends it** by 12 terms, and
the sequence is not in OEIS.

The extension immediately earns its keep. The first 27 terms agree exactly with
**round(√(n+3))**, which would predict sep(28) = 6; the exhaustive value is **sep(28) = 5**.
So the tempting square-root law dies at the first term past the published table — a reminder
of how little of this function's shape is pinned down.

Validation: the accept-set reduction is checked *exhaustively* against the literal definition
(every transition function, start state, and accept set — 4,194,304 DFAs at k = 4) rather
than assumed, giving the Lean theorem an independent computational cross-check; each witness
pair is re-derived from the literal definition (sep(18) > 4 required enumerating 1,566,711,930
DFAs); and four deliberate corruptions were each caught by the gates. Values for n ≤ 6 were
also reproduced by a separate from-scratch brute force.

`sep(n) ≥ 5` is exact through n = 30; the search stopped at a 9 GiB memory wall, not at a hard
pair, so where the next jump lies is unknown.

**Exact values in Lean, kernel only** (`sep_one`, `sep_four` — no `native_decide`): sep(1) = 2
and sep(4) = 3, the function's first jump. The lower half is the machine-checked fact that
`0110` vs `1010` defeats every two-state automaton; the upper half kernel-searches all 3-state
transition functions for all 256 pairs of length-4 words, through a second reduction lemma
(`exists_eval_ne_iff_exists_step`) that eliminates the non-decidable `Set`-valued accept
field. As far as we could determine, the first formally verified separating-words values. An
OEIS submission package for the sequence is drafted in
[computations/separating_words/](computations/separating_words/) (submission is a user
action).

### 3. Erdős–Gyárfás

**Records, verified at source** (every secondary claim below was checked against the actual
paper or archived page — details in the docstring of
[ErdosGyarfas.lean](OpenProblemsLab/ErdosGyarfas.lean)):

| Class | Counterexample needs | Source |
|---|---|---|
| min deg ≥ 3 | ≥ 16 vertices | Royle, "The 2ⁿ conjecture" webpage (≤ 2000, archived; checked ≤ 15) |
| min deg ≥ 3 | ≥ 32 vertices | Balaji 2026, SAT (Zenodo [10.5281/zenodo.21190438](https://doi.org/10.5281/zenodo.21190438)) — **unrefereed** |
| cubic | ≥ 30 vertices | Markström, Congr. Numer. 171 (2004) — all cubic ≤ 28 checked |
| cubic bipartite | ≥ 60 vertices | Tranquilli, [arXiv:2608.02675](https://arxiv.org/abs/2608.02675) (2026) |

The widely copied "**a counterexample has at least 17 vertices**" (Wikipedia, and papers citing
it) has **no primary source**: Royle's own page says 15, and Markström reports Royle's search
as "less than 16 vertices". The 17 appears to be a decades-old citation drift.

**In Lean** ([ErdosGyarfas.lean](OpenProblemsLab/ErdosGyarfas.lean), no `sorry`, standard
axioms): `sweep_reduction` — the search-space reduction every published computation relies on
(checking C4-free graphs suffices, since a C4 is itself a power-of-two cycle), formalized; this
is the warrant for `geng -f` in our sweeps. And `exists_cycle_of_two_le_degree` — minimum
degree 2 forces a cycle at all (via mathlib's component/tree machinery), the ground fact
beneath the conjecture.

**Computationally** ([computations/erdos_gyarfas/](computations/erdos_gyarfas/), log in
[RESULTS.md](computations/erdos_gyarfas/RESULTS.md)): **Markström's hardest published data
point is independently reproduced** — among the 9,467,449 C4-free connected cubic graphs on
24 vertices, exactly **4** have neither a C4 nor a C8 (his count), each containing a C16;
zero counterexamples. Different generator, checker, language, and hardware than the 2004
computation. General min-deg-3 lane verified through **n = 17** (34,758,006 C4-free graphs
at 17 alone, zero counterexamples) — with the Lean `sweep_reduction` this means any
counterexample has ≥ 18 vertices by our independent method, second-verifying the low range
of Balaji's unrefereed SAT record. Measured scaling puts cubic n = 26–28 in overnight/forge territory and the
n = 30 record step behind a compiled-filter barrier (documented in RESULTS.md). A bonus for
the methodology section: the validation gate caught a real off-by-one in the cycle-search
pruning on its first run (Petersen has a C8 the pruned search missed) — which is why the
gates exist.

### 4. EP #414 (n ↦ n + τ(n))

**In Lean** ([TauTrajectories.lean](OpenProblemsLab/TauTrajectories.lean), no `sorry`,
standard axioms, no `native_decide`): the map strictly increases (`n + 2 ≤ step n` for
n ≥ 2), meeting once means merged forever (`merged_of_eq`), and — the headline —
**`merge_pairs_upTo30`: every pair of starting points 2 ≤ m, n ≤ 30 has merging
trajectories**, each instance kernel-verified with explicit iterate indices (e.g. the
trajectories of 11 and 2 meet at 38 after 8 steps each). As far as we could determine,
these are the first machine-checked instances of EP #414.

**Computationally** ([computations/tau_trajectories/](computations/tau_trajectories/), log in
[RESULTS.md](computations/tau_trajectories/RESULTS.md)): **every starting point up to 10⁸
merges into the single stream containing 2**, with the single stream achieved just 0.18%
above the range — there is no second persistent stream. The mechanism is parity: τ(n) is odd
exactly at squares, so trajectories change parity only when stepping from a square, and the
census shows the long-deferred merges waiting for exactly that. Five gates and four negative
controls, including exact agreement between the census and the kernel-checked Lean witnesses
on the overlap. **The parity mechanism is now formal too**
(`odd_card_divisors_iff_isSquare`, axiom-clean): τ(n) is odd exactly when n is a square —
absent from mathlib (an upstreaming candidate) — with the corollaries that `step` preserves
trajectory parity off squares and flips it exactly at squares, which is the machinery the
census observed empirically.

### 5. Superpermutations

**`L 6 ≤ 872` is now a Lean theorem** ([Superpermutations.lean](OpenProblemsLab/Superpermutations.lean)):
Houston's 2014 word ships as data ([SuperpermData.lean](OpenProblemsLab/SuperpermData.lean)),
its 720-permutation coverage is checked by `native_decide` (the one theorem in this repo
leaning on the compiled evaluator — stated plainly here; the word length is kernel-checked,
and the word is independently verified by
[verify_word.py](computations/superpermutations/verify_word.py), which also confirms a
corrupted word is rejected). Next on the ladder: SAT calibration on L(5) = 153, then the
length-871 feasibility verdict for n = 6.

### 7. Graceful trees

**Stars are the first tree family proved graceful in Lean**
(`starGraph_isTree_and_graceful` in [GracefulTrees.lean](OpenProblemsLab/GracefulTrees.lean),
no `sorry`, standard axioms): label the center 0 and leaf i with i; edge labels come out
exactly 1,…,m. Combined with mathlib's `isTree_starGraph`, a machine-checked instance family
of the Ringel–Kotzig conjecture. The star edge-enumeration machinery is shared with the
antimagic proof ([StarFacts.lean](OpenProblemsLab/StarFacts.lean)).

**Computationally** ([computations/graceful/](computations/graceful/), log in
[RESULTS.md](computations/graceful/RESULTS.md)): **every tree on ≤ 18 vertices verified
graceful** — 123,867 trees at n = 18 alone, counts gated against OEIS A000055, every
labeling independently re-verified, with an exact-search fallback that was never needed.
This is a reproduction baseline, plainly stated: Fang's 2010 record stands at 35 vertices;
the measured cost curve puts the mid-20s in forge territory with a compiled climber.

### 8. W(2,7)

**The published lower-bound records are now machine-checked**
([VanDerWaerden.lean](OpenProblemsLab/VanDerWaerden.lean)): explicit colorings with no
monochromatic 7-term AP on {1,…,3703} (`W(2,7) > 3703`, the Rabung–Lotts record — their
E-JC table entry verified at source) and no 6-term AP on {1,…,1131} (the lower half of
Kouril–Paul's exact `W(2,6) = 1132`). Each rests on one `native_decide` evaluation of the
certificate data; the colorings are independently verified with negative controls in
[computations/vanderwaerden/](computations/vanderwaerden/).

Two honest notes. First, mathlib has no proof of van der Waerden's theorem, so the number
`W(r,k)` defined as an infimum is only known nonempty conditionally; the certificate theorems
(`¬ HasVdW 2 7 3703`) carry the unconditional content, and formalizing vdW's theorem itself is
now on the ladder. Second, a small find: Heule's public certificate files are one cell short
of the published records (3702 and 1130 cells — they certify one less). The full-length
certificates here were reconstructed by unrolling the cyclic patterns one further cell and
flipping one boundary symbol, which removes the unique wraparound progression whose
difference equals the period — then re-verified from the literal definition.

### 6. Antimagic labeling

**The first graph family is proved antimagic in Lean** (`isAntimagic_starGraph` in
[Antimagic.lean](OpenProblemsLab/Antimagic.lean), no `sorry`, standard axioms): stars
`K_{1,m}` with m ≥ 2, by the labeling that gives the edge to leaf i the label i — the leaves
then carry the distinct sums 1,…,m and the center carries their total, which exceeds every
leaf sum exactly when m ≥ 2. The pleasing part: **the m = 1 failure of this argument is
precisely the K₂ exception** in the Hartsfield–Ringel conjecture — the exception is visible
in the arithmetic.

**Computationally** ([computations/antimagic/](computations/antimagic/), log in
[RESULTS.md](computations/antimagic/RESULTS.md)): **the conjecture is verified for every
connected graph on ≤ 10 vertices** — all 11,989,763 of them received an explicit antimagic
labeling, each independently re-verified, with `K₂` *proved* not antimagic by exhaustive
search (the lone exception, exactly as conjectured). The hill-climber never once needed the
exact fallback above K₂: at small scale, antimagic labelings are everywhere. We could find no
published exhaustive sweep of this kind (family results abound; claim stated as "not found",
not as certain novelty).

### 12. Lehmer's totient problem

**Lehmer's own first structural bound is machine-checked**
([LehmerTotient.lean](OpenProblemsLab/LehmerTotient.lean), no `sorry`, standard axioms): a
composite n with φ(n) | n−1 must be odd (`odd_of_lehmer`), squarefree
(`squarefree_of_lehmer`), cannot be a product of two distinct primes
(`not_lehmer_semiprime` — the identity pq−1 = (p−1)(q−1) + (p−1)+(q−1) makes the divisor
exceed the remainder), and therefore has **at least 3 distinct prime factors**
(`three_le_card_primeFactors_of_lehmer`). The published ladder continues to ω(n) ≥ 14
(Cohen–Hagis 1980), which is computation-heavy; formalizing further rungs is queued.

### 9. Odd covering systems

In [OddCovering.lean](OpenProblemsLab/OddCovering.lean) (no `sorry`, standard axioms):
**the finite-check reduction** `isCovering_of_covers_period` — a system whose moduli divide a
period L covers ℤ iff it covers {0,…,L−1} — which is the formal warrant behind every
computational verification or search over covering systems (including the planned OC-2
shape search). Applied to the textbook five-congruence system {0(2), 0(3), 1(4), 5(6),
7(12)}: covers ℤ by a kernel `decide` over its period 12 (`classic_isCovering`), and, as
Erdős's conjecture demands of every covering system, it is not odd (`classic_not_odd`).

### 10. Distinct subset sums

**The Conway–Guy construction is verified exactly** ([computations/subset_sums/](computations/subset_sums/),
log in [RESULTS.md](computations/subset_sums/RESULTS.md)): the n-element sets built from
OEIS A005318 have all 2ⁿ subset sums pairwise distinct, checked by a blocked saturating
polynomial-coefficient DP for every **n ≤ 31** (ratios max/2ⁿ descending 0.255 → 0.2427,
marching toward the 0.23513 limit; n = 31 needs a 10.4 GB coefficient array, n = 32 is past
this machine), cross-gated against brute-force enumeration for n ≤ 20 with negative
controls. **In Lean**
([DistinctSubsetSums.lean](OpenProblemsLab/DistinctSubsetSums.lean)): the 16-element
Conway–Guy set has distinct subset sums with max 17305 < 2¹⁵ — a machine-checked witness
that the trivial powers-of-two construction is beaten by a factor ~1.9 (one `native_decide`
counting 65536 sums; independently verified in Python).

### 11. Erdős–Moser

**The k = 1 case is completely proved in Lean** (`k_eq_one_case` in
[ErdosMoser.lean](OpenProblemsLab/ErdosMoser.lean), axiom-clean): 1 + 2 + ⋯ + (m−1) = m
only at m = 3, by Gauss's identity. The entire open content lives in k ≥ 2.

**Moser's odd-k machinery is now formal through the mod-m² step** (all axiom-clean, no
`sorry`): the pairing i ↔ m−i gives m ∣ 2·∑ i^k for odd k; the binomial expansion sharpens
this to the congruence **2·∑ i^k + m^k ≡ k·m·∑ i^(k−1) (mod m²)**; and `dvd_of_solution`
extracts Moser's actual lever — any solution with odd k ≥ 2 forces **m ∣ k·∑_{i<m} i^(k−1)**,
turning the equation into a constraint on the *lower* power sum. Done in ℤ, since truncated
ℕ subtraction makes the binomial step unstateable. What remains is evaluating that power sum
mod m, which is where Moser's bound m > 10^(10⁶) comes from.

### Bench (documented, not active)

Sorting-network size S(13) (known through n=12, Harder 2020; n=13 likely CPU-decades) ·
Hadamard order 668 (search-frontier mapped, odds low) · Brocard n!+1=m² beyond 10¹⁵ ·
EP [#412](https://www.erdosproblems.com/412) (iterated σ) ·
EP [#324](https://www.erdosproblems.com/324) (polynomial Sidon) ·
chromatic number of the plane · BB(6) holdout deciders (great community, Coq-first).

## Ground rules

- **Re-verify before attacking.** AI systems and SAT groups are actively resolving
  problems on these lists (2025–26 saw several fall). Check EP / arXiv the same week any
  serious effort starts.
- **The Lean gate.** A claim counts only as: a Lean proof that compiles here, or a
  reproducible computation (code + logs +, where possible, certificates) committed to
  this repo. Nothing else is "progress".
- **Faithfulness over compilation.** A wrong formal statement that compiles is worse
  than none. Statements carry the informal version + citations in their docstrings;
  where FC formalized the same problem, semantics were cross-checked but written
  independently. [`Sanity.lean`](OpenProblemsLab/Sanity.lean) pins definitions down with
  concrete witnesses (‖6‖ ≤ 5, τ(6)=4 so 6 ↦ 10, `[0,1,0]` is a superpermutation on two
  symbols, `{1,2,3}` fails distinct subset sums, Lehmer verified to n = 100) so a
  definition that drifts fails the build instead of compiling vacuously.
- **Honest tiers.** Full resolutions are stretch goals. Records, verified partial
  results, and first formalizations are the bread and butter.

## Build

```
elan self update   # or install elan: https://github.com/leanprover/elan
lake exe cache get # fetch mathlib binaries (multi-GB, once)
lake build         # elaborates every problem statement
```

CI runs `lake build` on every push via [lean-action](https://github.com/leanprover/lean-action).

## Roadmap

- **Phase 1 (done):** curated list, formal statements, CI. ✔
- **Phase 2:** per-problem: formalize the *known* results marked as targets in the
  docstrings (Selfridge bound, superperm bounds, W(2,7) certificate, Moser odd-k);
  stand up the compute lanes (search harnesses for #4, #6, #7, #10).
- **Phase 3:** sustained iterative attack, problem by problem; anything resolved or
  improved gets written up and, where it fits, upstreamed (EP, FC, OEIS, arXiv).

## License

Apache-2.0. Statement files cite their sources; independent write-ups, no code copied
from formal-conjectures (also Apache-2.0).
