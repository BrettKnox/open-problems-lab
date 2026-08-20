import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Combinatorics.SimpleGraph.Star
import Mathlib.Data.Sym.Sym2
import Mathlib.Data.Nat.Dist
import Mathlib.Data.Set.Function
import Mathlib.Order.Interval.Set.Defs
import OpenProblemsLab.StarFacts

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

/-! ### Stars are graceful

The first tree family: label the center `0` and leaf `i` with `i`. Edge labels
are exactly `1, …, m`. Together with mathlib's `isTree_starGraph`, this is a
machine-checked instance family of the conjecture. -/

open SimpleGraph OpenProblems.StarFacts

variable {m : ℕ}

theorem isGraceful_starGraph : IsGraceful (starGraph (0 : Fin (m + 1))) := by
  classical
  refine ⟨Fin.val, Fin.val_injective, ?_, ?_⟩
  · intro v
    rw [starGraph_edgeFinset_card]
    omega
  · rw [starGraph_edgeFinset_card, ← SimpleGraph.coe_edgeFinset, starGraph_edgeFinset]
    have hlab : ∀ i : Fin m, edgeLabel Fin.val (starEdge m i) = i.val + 1 := by
      intro i
      simp [edgeLabel, starEdge, Nat.dist, Fin.val_succ]
    refine ⟨?_, ?_, ?_⟩
    · rintro e he
      simp only [Finset.coe_image, Finset.coe_univ, Set.image_univ, Set.mem_range] at he
      obtain ⟨i, rfl⟩ := he
      rw [hlab]
      simp only [Set.mem_Icc]
      omega
    · rintro e₁ he₁ e₂ he₂ h
      simp only [Finset.coe_image, Finset.coe_univ, Set.image_univ, Set.mem_range] at he₁ he₂
      obtain ⟨i, rfl⟩ := he₁
      obtain ⟨j, rfl⟩ := he₂
      rw [hlab, hlab] at h
      exact congrArg (starEdge m) (Fin.val_injective (by omega))
    · rintro k hk
      simp only [Set.mem_Icc] at hk
      refine ⟨starEdge m ⟨k - 1, by omega⟩, ?_, ?_⟩
      · simp only [Finset.coe_image, Finset.coe_univ, Set.image_univ, Set.mem_range]
        exact ⟨_, rfl⟩
      · rw [hlab]
        show k - 1 + 1 = k
        omega

/-- Stars witness the conjecture: a genuine tree family, graceful. -/
theorem starGraph_isTree_and_graceful :
    (starGraph (0 : Fin (m + 1))).IsTree ∧ IsGraceful (starGraph (0 : Fin (m + 1))) :=
  ⟨isTree_starGraph 0, isGraceful_starGraph⟩

end OpenProblems.GracefulTrees
