import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Data.Sym.Sym2
import Mathlib.Data.Nat.Dist
import Mathlib.Data.Set.Function
import Mathlib.Order.Interval.Set.Defs

/-!
# Graceful tree conjecture (Ringel–Kotzig)

A tree on `n + 1` vertices (so `n` edges) is graceful if its vertices can be
injectively labeled with `{0, …, n}` so that the induced edge labels
`|f(u) − f(v)|` are exactly `{1, …, n}`. Conjecture: every tree is graceful.

Status 2026-08-19: OPEN. Exhaustive verification stands at ≤ 35 vertices
(Fang 2010, arXiv:1003.3045; previously 27, Aldred–McKay 1998) — untouched
for 16 years. A claimed proof (arXiv:2202.03178) is not accepted. Class
results continue (spiders 2026, binary trees 2026). In formal-conjectures
(`Wikipedia/GracefulLabeling.lean`); this statement is written independently.

Attack lanes: push exhaustive verification to 36-37 vertices (embarrassingly
parallel backtracking, GPU-friendly); new infinite classes.
-/

namespace OpenProblems.GracefulTrees

/-- The label a vertex labeling `f` induces on an edge: `|f a − f b|`
(as `Nat.dist`, the symmetric distance on `ℕ`). -/
def edgeLabel {V : Type} (f : V → ℕ) : Sym2 V → ℕ :=
  Sym2.lift ⟨fun a b => Nat.dist (f a) (f b), fun a b => Nat.dist_comm (f a) (f b)⟩

/-- `G` (with `m` edges) is graceful: some injective vertex labeling into
`{0, …, m}` makes the induced edge labels biject onto `{1, …, m}`. -/
def IsGraceful {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] : Prop :=
  ∃ f : V → ℕ,
    Function.Injective f ∧ (∀ v : V, f v ≤ G.edgeFinset.card) ∧
    Set.BijOn (edgeLabel f) G.edgeSet (Set.Icc 1 G.edgeFinset.card)

/-- **Open conjecture** (Ringel–Kotzig): every finite tree is graceful. -/
def conjecture : Prop :=
  ∀ (V : Type) [Fintype V] [DecidableEq V] (T : SimpleGraph V) [DecidableRel T.Adj],
    T.IsTree → IsGraceful T

end OpenProblems.GracefulTrees
