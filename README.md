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
| 5 | **Superpermutations**, L(6) = 872? | A | [Superpermutations.lean](OpenProblemsLab/Superpermutations.lean) | Houston 872 (2014); Houston–Egan–anon lower bound 867 (2019); dormant since 2021 | **See [Results](#results).** Direct SAT ruled out (barrier documented); needs a Chaffin/TSP-style encoding |
| 6 | **Antimagic labeling** (Hartsfield–Ringel) | A | [Antimagic.lean](OpenProblemsLab/Antimagic.lean) | Regular graphs 2015–16; subdivisions ([2608.11723](https://arxiv.org/abs/2608.11723)) | **In progress — see [Results](#results).** Small-graph sweep; degree-2-heavy trees |
| 7 | **Graceful tree conjecture** | A | [GracefulTrees.lean](OpenProblemsLab/GracefulTrees.lean) | Verified ≤35 vertices (Fang 2010, [1003.3045](https://arxiv.org/abs/1003.3045)) — record untouched 16 years | **In progress — see [Results](#results).** Push exhaustive verification (embarrassingly parallel) |
| 8 | **W(2,7)** van der Waerden | A | [VanDerWaerden.lean](OpenProblemsLab/VanDerWaerden.lean) | W(2,6)=1132 (Kouril–Paul 2008); W(2,7) > 3703 (Rabung–Lotts, [E-JC 19(2) #P35](https://www.combinatorics.org/ojs/index.php/eljc/article/view/v19i2p35)) | **In progress — see [Results](#results).** Lower-bound records via SAT + cyclic zipper |
| 9 | **Odd covering systems** (EP [#7](https://www.erdosproblems.com/7); $25/$2000) | B | [OddCovering.lean](OpenProblemsLab/OddCovering.lean) | BBMST 2022: no odd squarefree covering; lcm divisible by 9 or 15 | **Result — see [Results](#results): no odd covering has lcm ≤ 10⁶.** |
| 10 | **Distinct subset sums** (EP [#1](https://www.erdosproblems.com/1), $500) | B | [DistinctSubsetSums.lean](OpenProblemsLab/DistinctSubsetSums.lean) | Dubroff–Fox–Xu 2021 lower bound; Bohman 0.22002·2ⁿ construction | Beat Bohman's constant by search; formalize DFX |
| 11 | **Erdős–Moser** 1ᵏ+⋯+(m−1)ᵏ = mᵏ | C | [ErdosMoser.lean](OpenProblemsLab/ErdosMoser.lean) | GMZ 2009 ([0907.1356](https://arxiv.org/abs/0907.1356)): m > 2.7139·10^1667658416 via CF of log 2 | **In progress — see [Results](#results).** Formalize Moser's odd-k proof; GMZ machinery reproduced |
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
**Altman's stability theorem is instantiated in that range too**: all **350** pairs (k, ℓ)
with 2ᵏ·3ᶫ ≤ 2³² satisfy ‖2ᵏ3ᶫ‖ = 2k + 3ℓ (k to 32, ℓ to 20). That confirms his theorem on a
bounded rectangle with our own validated table — it is not a reproduction of his proof, which
is uniform in ℓ and reaches k = 48 by reasoning about low-defect polynomials rather than
enumerating integers. No amount of table-extension closes that gap, since the ℓ-direction is
unbounded.

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

**That verdict is now in, and it is negative** (log in
[RESULTS.md](computations/superpermutations/RESULTS.md)). The CNF encoder is gated and
**reproduces L(4) = 33** exactly (UNSAT at 32 in 54 s). But n = 5's *easiest* ladder rung,
L = 149, ran 22.6 CPU-hours at 99.5% utilisation without returning — a > 1500× jump from
n = 4, on an instance strictly easier than the L = 152 one that would prove L(5) = 153. So
direct symbol-assignment SAT does not reach n = 5, and n = 6 at L = 871 is not a
compute-budget problem a forge window fixes. SP-3 is dropped rather than left perpetually
"queued"; reopening it needs the permutation-graph/TSP formulation the real searches use.

### 7. Graceful trees

**Stars are the first tree family proved graceful in Lean**
(`starGraph_isTree_and_graceful` in [GracefulTrees.lean](OpenProblemsLab/GracefulTrees.lean),
no `sorry`, standard axioms): label the center 0 and leaf i with i; edge labels come out
exactly 1,…,m. Combined with mathlib's `isTree_starGraph`, a machine-checked instance family
of the Ringel–Kotzig conjecture. The star edge-enumeration machinery is shared with the
antimagic proof ([StarFacts.lean](OpenProblemsLab/StarFacts.lean)).

**Paths are graceful too** (`isGraceful_pathGraph`), by the classical zigzag labeling
0, m, 1, m−1, 2, …: vertex i takes i/2 when even and m−(i−1)/2 when odd, so edge {i,i+1}
carries exactly m−i and the edge labels sweep m, m−1, …, 1. Two infinite families of the
conjecture are now machine-checked. (A `DecidableRel` instance for mathlib's `pathGraph`
falls out of this and may be worth upstreaming.)

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

**Paths are antimagic too** (`isAntimagic_pathGraph`, m ≥ 2 edges) — a second family, and
the proof records a genuine subtlety. The obvious left-to-right labeling (edge i ↦ i+1) is
antimagic **iff m is even**: the interior sums are 1, 3, …, 2m−1 and the far endpoint carries
m, which collides exactly when m is odd, at v = (m−1)/2. For m = 5 the sums are 1, 3, 5, 7,
9, 5. Swapping the last two labels repairs the odd case, and that two-case construction —
checked computationally for all m ≤ 400 before any proof was attempted — is what is
formalized. The first draft of this proof was *reverted rather than left with a* `sorry`,
because the falsity surfaced precisely at the vertex-sum obligation a `sorry` would have
hidden.

**Computationally** ([computations/antimagic/](computations/antimagic/), log in
[RESULTS.md](computations/antimagic/RESULTS.md)): **the conjecture is verified for every
connected graph on ≤ 11 vertices** — all **1,018,690,328** of them received an explicit
antimagic labeling, each independently re-verified, with `K₂` *proved* not antimagic by
exhaustive search (the lone exception, exactly as conjectured). The n = 11 level alone is
1,006,700,565 graphs (7.9 h); n = 12 is ~164 billion and needs a compiled checker. The hill-climber never once needed the
exact fallback above K₂: at small scale, antimagic labelings are everywhere. We could find no
published exhaustive sweep of this kind (family results abound; claim stated as "not found",
not as certain novelty).

**The theoretically hard subcase shows no difficulty** ([RESULTS_spiders.md](computations/antimagic/RESULTS_spiders.md)):
sparse trees with many degree-2 vertices are where doubt about the conjecture is
concentrated, but all 426 spider families on ≤ 16 vertices were labeled on the *first*
restart, and subdivided stars pushed to 321 vertices need at most 3. Evidence for the
conjecture, not proof — a heuristic-first search can only show labelings are easy to find,
never that none exists. The read: these trees are hard to *prove*, not hard to *label*, so
the next pass is Lean proofs for these families rather than more search.

### 12. Lehmer's totient problem

**Computationally** ([computations/lehmer/](computations/lehmer/)): **no composite n below
10⁹ satisfies φ(n) ∣ n − 1** (7 h, segmented φ sieve gated against trial division with a
negative control). A clean self-check falls out: the sweep found 50,847,535 solutions, and
π(10⁹) + 1 = 50,847,535 exactly — so the solution set is precisely {1} ∪ primes, confirmed
without reference to the primality test used inside the sweep.

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

**Computationally** ([computations/odd_covering/](computations/odd_covering/), log in
[RESULTS.md](computations/odd_covering/RESULTS.md)): a rigorous density screen —
a covering needs Σ1/mᵢ ≥ 1, so a shape whose odd divisors fall short is dead with no search
— **kills 97.5% of admissible shapes up to L = 200,000** (15,165 of 15,556), leaving 391
that need real structure. The survivors are strikingly marginal: the tightest, L = 32,445,
clears the threshold with density **1.0002**. Two gates here caught wrong assertions of
mine, and both corrections are the interesting content: odd moduli 3..15 already reach
density 1.0218, so density is *satisfiable* and not the obstruction; the real obstruction is
CRT overlap (for {3,5,15} the naive 5+3+1 = 9 residues is unreachable — the true maximum is
8, because the mod-3 and mod-5 classes must meet).

The survivors were then handed to a SAT solver, where UNSAT at a shape *proves* no odd
covering has that lcm. Over all admissible L ≤ 20,000 (3 h 34 m): 1,513 shapes killed by
density, **2 proved impossible by SAT** (L = 945 and 2205), 41 undecided at a 2×10⁶ conflict
budget, and **no covering system found**. So any odd covering with lcm ≤ 20,000 must have its
lcm among 41 named values — a narrowing from 1,556, not a resolution, and the log says which
41. Two fixes made even that possible: a linear (not pairwise-quadratic) at-most-one
encoding, and exploiting translation symmetry to fix one modulus's class, which took the
smallest survivor from unsolved-after-400 s to UNSAT in 47 s.

### 9. Odd covering systems (Erdős #7)

**No odd covering system has lcm at most 10⁶.** 1,996 candidate lcms, 49 seconds,
**zero search** — no SAT solver, no literature input, exact rational arithmetic. The
previous pass here left 41 shapes below 20,000 undecided after 3.5 hours of CDCL; all 41
are now closed, and so is everything else up to a bound 50× larger.

The result is not a faster solver. It is a necessary condition with no free choices left
in it. A covering with lcm L uses only divisors of L, so the *maximal* system (every odd
divisor m > 1, one class each) is the best possible attempt, and the question is finite.
Then:

1. **The lcm must be an odd abundant number.** The maximal system's density is
   σ(L)/L − 1, so density ≥ 1 is exactly σ(L) ≥ 2L. That alone cuts the search space to
   43 candidates below 20,000. (Standard — "covering number" is established terminology —
   but it makes this computation self-contained, with no appeal to BBMST's 9-or-15
   theorem. The counting step is formalized as `card_le_sum_of_covers_period`.)
2. **The coprime screen.** If T is a set of *pairwise coprime* moduli, CRT makes their
   classes independent, so they cover exactly L(1 − ∏(1 − 1/m)) **whatever classes are
   chosen** — the choice drops out. Bounding everything else by L/m gives
   D ≥ Σ_{m∈T} 1/m + ∏_{m∈T}(1 − 1/m). Taking T to be the primes of L, the share of the
   uncovered region a modulus can reach is exactly 1/φ(m), so the criterion becomes:
   **a covering with lcm L needs Σ 1/φ(m) ≥ 1 over the non-prime divisors of L.** For
   L = 945 that sum is 0.5946 — dead in one line, where CDCL needed 47 seconds.
3. **Coprime groups.** The uncovered region is a product set, so a coprime *group* is
   independent inside it and covers 1 − ∏(1 − 1/φ(m)), strictly less than Σ 1/φ(m).
   Partitioning into groups is stronger than both the additive bound and a
   forced-overlap matching, and is **sound for any partition** — the greedy one used here
   needs no optimality argument. This is what kills 675675, where Σ 1/φ = 1.0127 but the
   partition bound is 0.9922.

A complete search is kept alongside, branching on *which modulus covers the smallest
uncovered residue* (so it assigns a class outright, making the depth the modulus count)
with a capacity bound and two symmetry reductions. It beats CDCL by ~8× on L = 945 — and
still times out from L = 1575 up. **The screen, not the search, is what resolved this.**

The gates are built to catch an unsound screen rather than to confirm it: the search
agrees with brute force on all 31 subsets of {2,3,4,6,12}, and the screen **never fired on
any of 71 modulus sets that demonstrably admit a covering**, across 8 lattices, with the
group correction active. Even moduli are used there deliberately — the odd case has no
known positive instance to test against.

Pushed to 10⁷, the screen kills 20,649 of 20,661 candidates (99.94%), so **any odd
covering system with lcm ≤ 10⁷ has lcm among twelve explicit values** — all of them
3·5·7·11·13 with extra prime powers or one extra prime. Those twelve will not fall to
more of the same: the complete search is far out of reach at that size, and a better
partition cannot help much, since every modulus divisible by 3 must sit in a different
coprime group, forcing ~70 groups and making the correction second-order however it is
chosen. The remaining looseness is on *mixed* moduli (15, 45, 105, …) — prime-power
towers are already handled exactly — so closing them wants a different argument, not a
tuned one.

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
only at m = 3, by Gauss's identity. **The k = 3 case is complete too**
(`k_eq_three_case`): squaring Gauss gives 4·∑_{i≤t} i³ = (t(t+1))² — proved here, since
mathlib has the linear Gauss sum but not the cubic one — and the equation collapses to
t² = 4t + 4, which has no integer root.

**Moser's odd-k machinery is now formal through the mod-m² step** (all axiom-clean, no
`sorry`): the pairing i ↔ m−i gives m ∣ 2·∑ i^k for odd k; the binomial expansion sharpens
this to the congruence **2·∑ i^k + m^k ≡ k·m·∑ i^(k−1) (mod m²)**; and `dvd_of_solution`
extracts Moser's actual lever — any solution with odd k ≥ 2 forces **m ∣ k·∑_{i<m} i^(k−1)**,
turning the equation into a constraint on the *lower* power sum. Done in ℤ, since truncated
ℕ subtraction makes the binomial step unstateable.

The next rung is in too: **`sum_pow_range_mod`** evaluates the power sum modulo a prime —
∑_{i<p} i^j ≡ −1 when (p−1) ∣ j, and ≡ 0 otherwise. mathlib has this for finite fields; what
was missing was the bridge from a `Finset.range p` sum of naturals (which is what the
equation hands us) onto `ZMod p`, where the casts enumerate the field exactly once. That is
the tool Moser's bound m > 10^(10⁶) is built from.

**Computationally** ([computations/erdos_moser/](computations/erdos_moser/), log in
[RESULTS.md](computations/erdos_moser/RESULTS.md)): the Gallot–Moree–Zudilin continued-fraction
machinery reimplemented from the paper, with **all 11 rows of their Table 1 that this machine
can reach reproduced exactly** — index, partial quotient, q_j to seven significant figures,
residue mod 6, and the prime witnessing that condition (d) fails. Their result is that
2k/(2m−3) must be a convergent of log 2, quantified by a four-condition search over the
convergents of (log 2)/(2N) for any N dividing k.

The load-bearing observation for making this checkable at all: **condition (d) cannot be
verified exactly** — it asks about the prime factorization of a q_j with tens of thousands of
digits — **but checking it only for small primes is sound**, because every rejection the
program makes is a genuine failure, so the reported j never exceeds the true j(N) and the
bound m > q_j/2 survives. Raising the trial bound can only strengthen the result, never
invalidate it. That is visible in the data: at bound 20,000 the row N = 2⁸·3² shows no
violating prime; at 60,000 it finds p = 56131, exactly the prime the paper lists.

Two features of the published table look like typos and are not: the same q_j appears against
different j, and j is not monotone in N even though condition (b) strictly tightens. Both are
correct — each row is a continued fraction of a *different real number* (log 2)/(2N), so
indices are not comparable across rows. This repo asserted they were extraction errors before
computing them; the computation settled it.

The bound reached is **m > 6.87·10^61316** (at N = 2⁸·3, using N₂ ∣ k from Moree–te
Riele–Urbanowicz and Kellner), or **m > 2.64·10^450** with no divisibility input at all. Both
are far below Moser's 10^(10⁶) and GMZ's 2.7139·10^1667658416, and the gap is entirely in the
number of correct partial quotients: the bound scales as 10^(0.515·r), GMZ used r ≈ 3·10⁹, and
this reaches r ≈ 1.4·10⁵. **The barrier is named rather than hand-waved**: extraction here is
a quadratic Euclidean algorithm, and the paper itself reports having to switch to a recursive
half-GCD to pass 10^(10⁸). Closing the gap needs a different program, not a larger budget.

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
