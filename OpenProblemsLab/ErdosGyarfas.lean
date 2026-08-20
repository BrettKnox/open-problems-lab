import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Combinatorics.SimpleGraph.Paths

/-!
# Erdős–Gyárfás conjecture (cycles of length 2^k)

Every finite simple graph with minimum degree at least 3 contains a cycle
whose length is a power of two.

Status 2026-08-19: OPEN. Known: holds for cubic planar graphs, claw-free
graphs, P₁₃-free graphs (arXiv:2410.22842), diameter-2 graphs
(arXiv:2508.19302); a minimal counterexample is "predominantly cubic"
(arXiv:2605.22844); any counterexample has > 17 vertices (> 30 if cubic;
Royle–Markström computations). Not in formal-conjectures.

Attack lanes: raise the minimal-counterexample vertex bounds by exhaustive
generation (geng/nauty) + SAT per graph — the current records are old and low.
-/

namespace OpenProblems.ErdosGyarfas

/-- **Open conjecture** (Erdős–Gyárfás 1995): every finite graph with all
degrees ≥ 3 has a cycle of length `2^k` for some `k`. (Cycles have length
≥ 3, so such `k` is necessarily ≥ 2.) -/
def conjecture : Prop :=
  ∀ (V : Type) [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj],
    (∀ v : V, 3 ≤ G.degree v) →
    ∃ (v : V) (w : G.Walk v v), w.IsCycle ∧ ∃ k : ℕ, w.length = 2 ^ k

end OpenProblems.ErdosGyarfas
