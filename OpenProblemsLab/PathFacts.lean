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



end OpenProblems.PathFacts
