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
| 1 | **Integer complexity** ‖2ⁿ‖ = 2n | A | [IntegerComplexity.lean](OpenProblemsLab/IntegerComplexity.lean) | Altman–Arias de Reyna 2026 ([2111.00671](https://arxiv.org/abs/2111.00671)); search to 2¹²⁶ (He, [2308.10301](https://arxiv.org/abs/2308.10301)) | Extend Altman k≤48 stability + He's search. ~2 researchers worldwide. **First Lean formalization of the statement anywhere** |
| 2 | **Separating words** | A | [SeparatingWords.lean](OpenProblemsLab/SeparatingWords.lean) | Chase, STOC 2021: O(n^⅓ log⁷ n); 2025 improvement claim withdrawn | Exact small-n values via SAT (no published table); log n vs n^⅓ gap wide open |
| 3 | **Erdős–Gyárfás** (min deg 3 ⟹ 2ᵏ-cycle) | A | [ErdosGyarfas.lean](OpenProblemsLab/ErdosGyarfas.lean) | P₁₃-free ([2410.22842](https://arxiv.org/abs/2410.22842)); minimal counterexample "predominantly cubic" (2026) | Raise minimal-counterexample bounds (>17 vertices, cubic >30 — old, low) via geng/nauty + SAT |
| 4 | **EP [#414](https://www.erdosproblems.com/414)**: n ↦ n+τ(n) trajectories merge? | A | [TauTrajectories.lean](OpenProblemsLab/TauTrajectories.lean) | Erdős–Graham 1980; nothing since | Zero competition. Large-scale trajectory computation + parity-of-τ structure |
| 5 | **Superpermutations**, L(6) = 872? | A | [Superpermutations.lean](OpenProblemsLab/Superpermutations.lean) | Egan 872 (2014); Houston–Egan–anon lower bound 867 (2019); dormant since 2021 | Rule out 871 via modern SAT + proof logging (untried) |
| 6 | **Antimagic labeling** (Hartsfield–Ringel) | A | [Antimagic.lean](OpenProblemsLab/Antimagic.lean) | Regular graphs 2015–16; subdivisions ([2608.11723](https://arxiv.org/abs/2608.11723)) | Systematic small-graph verification (none published); degree-2-heavy trees |
| 7 | **Graceful tree conjecture** | A | [GracefulTrees.lean](OpenProblemsLab/GracefulTrees.lean) | Verified ≤35 vertices (Fang 2010, [1003.3045](https://arxiv.org/abs/1003.3045)) — record untouched 16 years | Push exhaustive verification to 36–37 (embarrassingly parallel) |
| 8 | **W(2,7)** van der Waerden | A | [VanDerWaerden.lean](OpenProblemsLab/VanDerWaerden.lean) | W(2,6)=1132 (Kouril–Paul 2008); lb 3703 (Rabung–Lotts) | Lower-bound records via SAT + cyclic zipper |
| 9 | **Odd covering systems** (EP [#7](https://www.erdosproblems.com/7); $25/$2000) | B | [OddCovering.lean](OpenProblemsLab/OddCovering.lean) | BBMST 2022: no odd squarefree covering; lcm divisible by 9 or 15 | Search admissible lcm shapes; LP density bounds |
| 10 | **Distinct subset sums** (EP [#1](https://www.erdosproblems.com/1), $500) | B | [DistinctSubsetSums.lean](OpenProblemsLab/DistinctSubsetSums.lean) | Dubroff–Fox–Xu 2021 lower bound; Bohman 0.22002·2ⁿ construction | Beat Bohman's constant by search; formalize DFX |
| 11 | **Erdős–Moser** 1ᵏ+⋯+(m−1)ᵏ = mᵏ | C | [ErdosMoser.lean](OpenProblemsLab/ErdosMoser.lean) | GMZ 2011: m > 10^(10⁹) via CF of log 2 | Extend the CF computation past 10^(10¹⁰); formalize Moser's odd-k proof |
| 12 | **Lehmer's totient problem** | C | [LehmerTotient.lean](OpenProblemsLab/LehmerTotient.lean) | Cohen–Hagis 1980 (n>10²⁰, ω≥14); Burek–Żmija 2019 | Modern sweep raising 10-year-old bounds; formalize Cohen–Hagis framework |

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
