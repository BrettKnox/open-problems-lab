import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Combinatorics.SimpleGraph.Hasse

/-!
# Shared facts about path graphs

Decidable adjacency and the edge enumeration of `pathGraph (m+1)`, used by
both the graceful (`GracefulTrees.lean`) and antimagic (`Antimagic.lean`)
family theorems. The `DecidableRel` instance is what lets `edgeFinset` be
spoken about at all, and looks upstreamable to mathlib.
-/

namespace OpenProblems.PathFacts

open SimpleGraph

variable {m : ℕ}

/-- Adjacency in the path graph is decidable, so its edge set is a `Fintype`
through the usual chain (needed to talk about `edgeFinset` at all). -/
instance pathGraphDecidableAdj (n : ℕ) : DecidableRel (pathGraph n).Adj :=
  fun _ _ => decidable_of_iff _ pathGraph_adj.symm

/-- Edge enumeration of `pathGraph (m+1)`: edge `i` joins `i` to `i+1`. -/
def pathEdge (m : ℕ) (i : Fin m) : Sym2 (Fin (m + 1)) :=
  s(⟨i.val, by omega⟩, ⟨i.val + 1, by omega⟩)

lemma pathEdge_injective {m : ℕ} : Function.Injective (pathEdge m) := by
  intro i j h
  rcases Sym2.eq_iff.mp h with ⟨h1, -⟩ | ⟨h1, h2⟩
  · exact Fin.ext (by simpa using congrArg Fin.val h1)
  · exfalso
    have := congrArg Fin.val h1
    have := congrArg Fin.val h2
    simp only [] at *
    omega

lemma pathGraph_edgeFinset {m : ℕ} :
    (pathGraph (m + 1)).edgeFinset = Finset.image (pathEdge m) Finset.univ := by
  classical
  ext e
  refine e.ind fun a b => ?_
  simp only [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet, pathGraph_adj,
    Finset.mem_image, Finset.mem_univ, true_and, pathEdge]
  constructor
  · rintro (h | h)
    · exact ⟨⟨a.val, by omega⟩, by
        refine Sym2.eq_iff.mpr (Or.inl ⟨Fin.ext rfl, Fin.ext ?_⟩)
        simpa using h⟩
    · exact ⟨⟨b.val, by omega⟩, by
        refine Sym2.eq_iff.mpr (Or.inr ⟨Fin.ext rfl, Fin.ext ?_⟩)
        simpa using h⟩
  · rintro ⟨i, hi⟩
    rcases Sym2.eq_iff.mp hi with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · left
      have e1 := congrArg Fin.val h1
      have e2 := congrArg Fin.val h2
      simp only [] at e1 e2
      omega
    · right
      have e1 := congrArg Fin.val h1
      have e2 := congrArg Fin.val h2
      simp only [] at e1 e2
      omega



/-! ### Incidence sets

Which edges touch a given vertex: the endpoints carry one edge, every
interior vertex carries two. These are what any vertex-sum argument on paths
needs (antimagic labelings, degree computations). -/

lemma mem_pathEdge_iff {m : ℕ} (i : Fin m) (v : Fin (m + 1)) :
    v ∈ pathEdge m i ↔ v.val = i.val ∨ v.val = i.val + 1 := by
  simp only [pathEdge, Sym2.mem_iff]
  constructor
  · rintro (h | h) <;> [left; right] <;> exact congrArg Fin.val h
  · rintro (h | h) <;> [left; right] <;> exact Fin.ext h

lemma incidence_eq {m : ℕ} (v : Fin (m + 1)) :
    (pathGraph (m + 1)).incidenceFinset v
      = Finset.image (pathEdge m)
          ((Finset.univ : Finset (Fin m)).filter
            (fun i : Fin m => v.val = i.val ∨ v.val = i.val + 1)) := by
  classical
  ext e
  simp only [SimpleGraph.mem_incidenceFinset, SimpleGraph.incidenceSet,
    Set.mem_ofPred_eq, Finset.mem_image, Finset.mem_filter, Finset.mem_univ,
    true_and]
  constructor
  · rintro ⟨hmem, hin⟩
    rw [← SimpleGraph.mem_edgeFinset, pathGraph_edgeFinset] at hmem
    simp only [Finset.mem_image, Finset.mem_univ, true_and] at hmem
    obtain ⟨i, rfl⟩ := hmem
    exact ⟨i, (mem_pathEdge_iff i v).mp hin, rfl⟩
  · rintro ⟨i, hi, rfl⟩
    refine ⟨?_, (mem_pathEdge_iff i v).mpr hi⟩
    rw [← SimpleGraph.mem_edgeFinset, pathGraph_edgeFinset]
    simp only [Finset.mem_image, Finset.mem_univ, true_and]
    exact ⟨i, rfl⟩

/-- Vertex `0` touches exactly the first edge. -/
lemma incidence_zero {m : ℕ} (hm : 1 ≤ m) :
    (pathGraph (m + 1)).incidenceFinset ⟨0, by omega⟩
      = {pathEdge m ⟨0, by omega⟩} := by
  classical
  rw [incidence_eq]
  have : (Finset.univ : Finset (Fin m)).filter
      (fun i : Fin m => (0 : ℕ) = i.val ∨ (0 : ℕ) = i.val + 1)
      = {⟨0, by omega⟩} := by
    ext ⟨iv, hiv⟩
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton,
      Fin.mk.injEq]
    omega
  rw [this, Finset.image_singleton]

/-- The last vertex touches exactly the last edge. -/
lemma incidence_last {m : ℕ} (hm : 1 ≤ m) :
    (pathGraph (m + 1)).incidenceFinset ⟨m, by omega⟩
      = {pathEdge m ⟨m - 1, by omega⟩} := by
  classical
  rw [incidence_eq]
  have : (Finset.univ : Finset (Fin m)).filter
      (fun i : Fin m => m = i.val ∨ m = i.val + 1) = {⟨m - 1, by omega⟩} := by
    ext ⟨iv, hiv⟩
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton,
      Fin.mk.injEq]
    omega
  rw [this, Finset.image_singleton]

/-- An interior vertex touches exactly the two edges beside it. -/
lemma incidence_mid {m v : ℕ} (h1 : 1 ≤ v) (h2 : v < m) :
    (pathGraph (m + 1)).incidenceFinset ⟨v, by omega⟩
      = {pathEdge m ⟨v - 1, by omega⟩, pathEdge m ⟨v, by omega⟩} := by
  classical
  rw [incidence_eq]
  have hset : (Finset.univ : Finset (Fin m)).filter
      (fun i : Fin m => v = i.val ∨ v = i.val + 1)
      = {⟨v - 1, by omega⟩, ⟨v, by omega⟩} := by
    ext ⟨iv, hiv⟩
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
      Finset.mem_singleton, Fin.mk.injEq]
    omega
  rw [hset, Finset.image_insert, Finset.image_singleton]

end OpenProblems.PathFacts
