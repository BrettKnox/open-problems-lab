import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Set.Function
import Mathlib.Order.Interval.Set.Defs

/-!
# Antimagic labeling conjecture (Hartsfield–Ringel 1990)

A graph with `m` edges is antimagic if its edges can be labeled bijectively
with `1, …, m` so that all vertex sums (sum of labels on incident edges) are
pairwise distinct. Conjecture: every connected graph other than `K₂` is
antimagic.

Status 2026-08-19: OPEN. Known: dense graphs (Alon–Kaplan–Lev–Roditty–Yuster
2004), regular graphs (2015-16), many families since; recent activity on
subdivisions (arXiv:2608.11723). Hard subcase: trees with many degree-2
vertices. Not in formal-conjectures.

Attack lanes: systematic exhaustive verification over all small connected
graphs (no published record of such a sweep); tree subcase search.
-/

namespace OpenProblems.Antimagic

/-- `G` is antimagic: some bijective edge labeling by `{1, …, m}` makes all
vertex sums distinct. -/
def IsAntimagic {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] : Prop :=
  ∃ f : Sym2 V → ℕ,
    Set.BijOn f G.edgeSet (Set.Icc 1 G.edgeFinset.card) ∧
    Function.Injective fun v : V => ∑ e ∈ G.incidenceFinset v, f e

/-- **Open conjecture** (Hartsfield–Ringel): every connected graph on ≠ 2
vertices is antimagic. (The only connected graph on 2 vertices is `K₂`, the
sole exception.) -/
def conjecture : Prop :=
  ∀ (V : Type) [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj],
    G.Connected → Fintype.card V ≠ 2 → IsAntimagic G

end OpenProblems.Antimagic
