import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Mathlib.Combinatorics.SimpleGraph.Star
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

/-! ### Stars are antimagic

The first infinite family, and the cleanest: label the edge to leaf `i` with
`i`. The leaves then carry the pairwise-distinct sums `1, …, m` and the center
carries `1 + ⋯ + m`, which exceeds every leaf sum precisely when `m ≥ 2` —
the failure at `m = 1` **is** the `K₂` exception of the conjecture. -/

open SimpleGraph

variable {m : ℕ}

/-- Edge enumeration of the star `K_{1,m}` on `Fin (m+1)` with center `0`:
the `i`-th edge joins the center to leaf `i + 1`. -/
private def starEdge (m : ℕ) (i : Fin m) : Sym2 (Fin (m + 1)) :=
  s(0, i.succ)

private lemma starEdge_injective : Function.Injective (starEdge m) := by
  intro i j h
  rcases Sym2.eq_iff.mp h with ⟨-, h2⟩ | ⟨h1, -⟩
  · exact Fin.succ_injective _ h2
  · exact absurd h1.symm (Fin.succ_ne_zero j)

private lemma starGraph_edgeFinset :
    (starGraph (0 : Fin (m + 1))).edgeFinset = Finset.image (starEdge m) Finset.univ := by
  ext e
  refine e.ind fun a b => ?_
  simp only [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet, starGraph_adj,
    Finset.mem_image, Finset.mem_univ, true_and, starEdge]
  constructor
  · rintro ⟨hne, h0 | h0⟩
    · subst h0
      obtain ⟨j, rfl⟩ : ∃ j : Fin m, b = j.succ :=
        ⟨b.pred (fun hb => hne hb.symm), by simp⟩
      exact ⟨j, rfl⟩
    · subst h0
      obtain ⟨j, rfl⟩ : ∃ j : Fin m, a = j.succ := ⟨a.pred hne, by simp⟩
      exact ⟨j, Sym2.eq_swap⟩
  · rintro ⟨j, hj⟩
    rcases Sym2.eq_iff.mp hj with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · subst h1
      subst h2
      exact ⟨(Fin.succ_ne_zero j).symm, Or.inl rfl⟩
    · subst h1
      subst h2
      exact ⟨Fin.succ_ne_zero j, Or.inr rfl⟩

/-- The label of an edge of the star: the larger endpoint (as a number). For
`starEdge i` this is `i + 1`. -/
private def starLabel : Sym2 (Fin (m + 1)) → ℕ :=
  Sym2.lift ⟨fun a b => max a.val b.val, fun a b => Nat.max_comm a.val b.val⟩

@[simp] private lemma starLabel_starEdge (i : Fin m) :
    starLabel (starEdge m i) = i.val + 1 := by
  simp [starLabel, starEdge, Fin.val_succ]

private lemma star_incidence_leaf (j : Fin m) :
    (starGraph (0 : Fin (m + 1))).incidenceFinset j.succ = {starEdge m j} := by
  classical
  ext e
  simp only [SimpleGraph.mem_incidenceFinset, SimpleGraph.incidenceSet, Set.mem_ofPred_eq,
    Finset.mem_singleton]
  constructor
  · rintro ⟨hmem, hin⟩
    rw [← SimpleGraph.mem_edgeFinset, starGraph_edgeFinset] at hmem
    simp only [Finset.mem_image, Finset.mem_univ, true_and] at hmem
    obtain ⟨i, rfl⟩ := hmem
    simp only [starEdge, Sym2.mem_iff] at hin
    rcases hin with h | h
    · exact (Fin.succ_ne_zero j h).elim
    · exact congrArg (starEdge m) (Fin.succ_injective _ h.symm)
  · rintro rfl
    refine ⟨?_, by simp [starEdge]⟩
    show s(0, j.succ) ∈ (starGraph (0 : Fin (m + 1))).edgeSet
    rw [SimpleGraph.mem_edgeSet]
    exact SimpleGraph.starGraph_center_adj (Ne.symm (Fin.succ_ne_zero j))

private lemma star_incidence_center :
    (starGraph (0 : Fin (m + 1))).incidenceFinset 0
      = (starGraph (0 : Fin (m + 1))).edgeFinset := by
  classical
  ext e
  simp only [SimpleGraph.mem_incidenceFinset, SimpleGraph.incidenceSet, Set.mem_ofPred_eq,
    SimpleGraph.mem_edgeFinset]
  refine ⟨fun h => h.1, fun h => ⟨h, ?_⟩⟩
  have h' := h
  rw [← SimpleGraph.mem_edgeFinset, starGraph_edgeFinset] at h'
  simp only [Finset.mem_image, Finset.mem_univ, true_and] at h'
  obtain ⟨i, rfl⟩ := h'
  simp [starEdge]

/-- **Stars are antimagic** for `m ≥ 2` leaves. The `m = 1` case is `K₂`,
the unique exception in the Hartsfield–Ringel conjecture. -/
theorem isAntimagic_starGraph (hm : 2 ≤ m) :
    IsAntimagic (starGraph (0 : Fin (m + 1))) := by
  classical
  have hcard : (starGraph (0 : Fin (m + 1))).edgeFinset.card = m := by
    rw [starGraph_edgeFinset, Finset.card_image_of_injective _ starEdge_injective,
      Finset.card_univ, Fintype.card_fin]
  have hbig : (m - 1) + m ≤ ∑ i : Fin m, (i.val + 1) := by
    have hne : (⟨m - 2, by omega⟩ : Fin m) ≠ ⟨m - 1, by omega⟩ := by
      simp only [ne_eq, Fin.mk.injEq]
      omega
    calc (m - 1) + m
        = ∑ i ∈ ({⟨m - 2, by omega⟩, ⟨m - 1, by omega⟩} : Finset (Fin m)),
            (i.val + 1) := by
          rw [Finset.sum_insert (by simpa using hne), Finset.sum_singleton]
          simp only []
          omega
      _ ≤ _ := Finset.sum_le_sum_of_subset (Finset.subset_univ _)
  have hsum : ∀ v : Fin (m + 1),
      (∑ e ∈ (starGraph (0 : Fin (m + 1))).incidenceFinset v, starLabel e)
        = if v = 0 then ∑ i : Fin m, (i.val + 1) else v.val := by
    intro v
    by_cases hv : v = 0
    · subst hv
      rw [ite_eq_left rfl, star_incidence_center, starGraph_edgeFinset,
        Finset.sum_image (fun a _ b _ h => starEdge_injective h)]
      simp
    · rw [ite_eq_right hv]
      obtain ⟨j, rfl⟩ : ∃ j : Fin m, v = j.succ := ⟨v.pred hv, by simp⟩
      rw [star_incidence_leaf, Finset.sum_singleton, starLabel_starEdge, Fin.val_succ]
  refine ⟨starLabel, ?_, ?_⟩
  · -- bijection onto {1, …, m}
    rw [hcard, ← SimpleGraph.coe_edgeFinset, starGraph_edgeFinset]
    refine ⟨?_, ?_, ?_⟩
    · rintro e he
      simp only [Finset.coe_image, Finset.coe_univ, Set.image_univ, Set.mem_range] at he
      obtain ⟨i, rfl⟩ := he
      simp only [starLabel_starEdge, Set.mem_Icc]
      omega
    · rintro e₁ he₁ e₂ he₂ h
      simp only [Finset.coe_image, Finset.coe_univ, Set.image_univ, Set.mem_range] at he₁ he₂
      obtain ⟨i, rfl⟩ := he₁
      obtain ⟨j, rfl⟩ := he₂
      simp only [starLabel_starEdge] at h
      exact congrArg (starEdge m) (Fin.val_injective (by omega))
    · rintro k hk
      simp only [Set.mem_Icc] at hk
      refine ⟨starEdge m ⟨k - 1, by omega⟩, ?_, ?_⟩
      · simp only [Finset.coe_image, Finset.coe_univ, Set.image_univ, Set.mem_range]
        exact ⟨_, rfl⟩
      · simp only [starLabel_starEdge]
        omega
  · -- vertex sums are pairwise distinct
    intro u v huv
    simp only [hsum] at huv
    by_cases hu : u = 0 <;> by_cases hv : v = 0
    · rw [hu, hv]
    · exfalso
      rw [ite_eq_left hu, ite_eq_right hv] at huv
      have : v.val ≤ m := by omega
      omega
    · exfalso
      rw [ite_eq_right hu, ite_eq_left hv] at huv
      have : u.val ≤ m := by omega
      omega
    · rw [ite_eq_right hu, ite_eq_right hv] at huv
      exact Fin.val_injective huv

end OpenProblems.Antimagic
