import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Mathlib.Combinatorics.SimpleGraph.Star
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Set.Function
import Mathlib.Order.Interval.Set.Defs
import Mathlib.Combinatorics.SimpleGraph.Hasse
import OpenProblemsLab.StarFacts
import OpenProblemsLab.PathFacts

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

open SimpleGraph OpenProblems.StarFacts OpenProblems.PathFacts

/-! ### Paths are antimagic

Label the edges left to right, `edge i ↦ i + 1`, **except** that for odd `m`
the last two labels are swapped (`…, m-2, m, m-1`). The swap is not cosmetic:
with the plain left-to-right labeling the interior sums are `1, 3, …, 2m-1`
and the far endpoint carries `m`, which collides exactly when `m` is odd, at
the vertex `v = (m-1)/2`. (For `m = 5` the sums are `1, 3, 5, 7, 9, 5`.) The
two-case labeling was checked computationally for all `m ≤ 400` before being
proved here; see `computations/antimagic/RESULTS_spiders.md`. -/

/-- Position-indexed edge label: `i + 1`, with the last two swapped when `m`
is odd. -/
def pathLab (m i : ℕ) : ℕ :=
  if m % 2 = 1 ∧ i = m - 2 then m
  else if m % 2 = 1 ∧ i = m - 1 then m - 1
  else i + 1

/-- The labeling as a function on edges (via the smaller endpoint). -/
private def pathLabel (m : ℕ) : Sym2 (Fin (m + 1)) → ℕ :=
  Sym2.lift ⟨fun a b => pathLab m (min a.val b.val),
    fun a b => by
      show pathLab m (min a.val b.val) = pathLab m (min b.val a.val)
      rw [Nat.min_comm]⟩

@[simp] private lemma pathLabel_pathEdge {m : ℕ} (i : Fin m) :
    pathLabel m (pathEdge m i) = pathLab m i.val := by
  simp [pathLabel, pathEdge]

/-- `pathLab m` restricted to `{0, …, m-1}` is a bijection onto `{1, …, m}`:
it is the identity shift except for a transposition of the top two values. -/
private lemma pathLab_mem {m i : ℕ} (hm : 2 ≤ m) (hi : i < m) :
    1 ≤ pathLab m i ∧ pathLab m i ≤ m := by
  unfold pathLab
  split_ifs with h1 h2 <;> omega

private lemma pathLab_inj {m i j : ℕ} (hm : 2 ≤ m) (hi : i < m) (hj : j < m)
    (h : pathLab m i = pathLab m j) : i = j := by
  unfold pathLab at h
  split_ifs at h with h1 h2 h3 h4 h5 <;> omega

private lemma pathLab_surj {m k : ℕ} (hm : 2 ≤ m) (h1 : 1 ≤ k) (h2 : k ≤ m) :
    ∃ i, i < m ∧ pathLab m i = k := by
  by_cases hodd : m % 2 = 1
  · rcases (by omega : k = m ∨ k = m - 1 ∨ k ≤ m - 2) with hk | hk | hk
    · exact ⟨m - 2, by omega, by unfold pathLab; split_ifs <;> omega⟩
    · exact ⟨m - 1, by omega, by unfold pathLab; split_ifs <;> omega⟩
    · exact ⟨k - 1, by omega, by unfold pathLab; split_ifs <;> omega⟩
  · exact ⟨k - 1, by omega, by unfold pathLab; split_ifs <;> omega⟩



variable {m : ℕ}


/-- Vertex sums under `pathLabel`: endpoints carry a single label, interior
vertices the sum of the two beside them. -/
private lemma pathSum {m : ℕ} (hm : 2 ≤ m) (v : Fin (m + 1)) :
    (∑ e ∈ (pathGraph (m + 1)).incidenceFinset v, pathLabel m e)
      = if v.val = 0 then pathLab m 0
        else if v.val = m then pathLab m (m - 1)
        else pathLab m (v.val - 1) + pathLab m v.val := by
  classical
  rcases (by omega : v.val = 0 ∨ v.val = m ∨ (1 ≤ v.val ∧ v.val < m)) with h | h | ⟨h1, h2⟩
  · have hveq : v = ⟨0, by omega⟩ := Fin.ext (by omega)
    rw [hveq, incidence_zero (by omega : 1 ≤ m), Finset.sum_singleton,
      pathLabel_pathEdge]
    simp
  · have hveq : v = ⟨m, by omega⟩ := Fin.ext (by omega)
    rw [hveq, incidence_last (by omega : 1 ≤ m), Finset.sum_singleton,
      pathLabel_pathEdge]
    simp only []
    rw [ite_eq_right (by omega)]
    simp
  · have hv : v = ⟨v.val, by omega⟩ := Fin.ext rfl
    rw [hv, incidence_mid h1 h2]
    have hne : (pathEdge m ⟨v.val - 1, by omega⟩) ≠ pathEdge m ⟨v.val, by omega⟩ := by
      intro hEq
      have := pathEdge_injective hEq
      have := congrArg Fin.val this
      simp only [] at this
      omega
    rw [Finset.sum_insert (by simpa using hne), Finset.sum_singleton,
      pathLabel_pathEdge, pathLabel_pathEdge]
    simp only []
    rw [ite_eq_right (by omega), ite_eq_right (by omega)]

set_option maxHeartbeats 1000000 in
/-- **Paths are antimagic** for `m ≥ 2` edges (so at least 3 vertices).
`P₂ = K₂` is the excluded case, exactly as in the conjecture. -/
theorem isAntimagic_pathGraph {m : ℕ} (hm : 2 ≤ m) :
    IsAntimagic (pathGraph (m + 1)) := by
  classical
  have hcard : (pathGraph (m + 1)).edgeFinset.card = m := by
    rw [pathGraph_edgeFinset, Finset.card_image_of_injective _ pathEdge_injective,
      Finset.card_univ, Fintype.card_fin]
  refine ⟨pathLabel m, ?_, ?_⟩
  · rw [hcard, ← SimpleGraph.coe_edgeFinset, pathGraph_edgeFinset]
    refine ⟨?_, ?_, ?_⟩
    · rintro e he
      simp only [Finset.coe_image, Finset.coe_univ, Set.image_univ, Set.mem_range] at he
      obtain ⟨i, rfl⟩ := he
      rw [pathLabel_pathEdge]
      simp only [Set.mem_Icc]
      exact pathLab_mem hm i.isLt
    · rintro e₁ he₁ e₂ he₂ h
      simp only [Finset.coe_image, Finset.coe_univ, Set.image_univ, Set.mem_range] at he₁ he₂
      obtain ⟨i, rfl⟩ := he₁
      obtain ⟨j, rfl⟩ := he₂
      rw [pathLabel_pathEdge, pathLabel_pathEdge] at h
      exact congrArg (pathEdge m) (Fin.ext (pathLab_inj hm i.isLt j.isLt h))
    · rintro k hk
      simp only [Set.mem_Icc] at hk
      obtain ⟨i, hi, hlab⟩ := pathLab_surj hm hk.1 hk.2
      refine ⟨pathEdge m ⟨i, hi⟩, ?_, ?_⟩
      · simp only [Finset.coe_image, Finset.coe_univ, Set.image_univ, Set.mem_range]
        exact ⟨_, rfl⟩
      · rw [pathLabel_pathEdge]
        exact hlab
  · intro u v huv
    simp only [] at huv
    rw [pathSum hm u, pathSum hm v] at huv
    -- unfold the label into the three regimes and let omega finish
    have hu := u.isLt
    have hv := v.isLt
    unfold pathLab at huv
    refine Fin.ext ?_
    split_ifs at huv <;> omega

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
  have hcard : (starGraph (0 : Fin (m + 1))).edgeFinset.card = m :=
    starGraph_edgeFinset_card
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
