import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Combinatorics.SimpleGraph.Star

/-!
# Shared facts about star graphs

Edge enumeration of `starGraph (0 : Fin (m+1))` used by both the antimagic
(`Antimagic.lean`) and graceful (`GracefulTrees.lean`) family theorems.
-/

namespace OpenProblems.StarFacts

open SimpleGraph

variable {m : ℕ}

/-- Edge enumeration of the star `K_{1,m}` on `Fin (m+1)` with center `0`:
the `i`-th edge joins the center to leaf `i + 1`. -/
def starEdge (m : ℕ) (i : Fin m) : Sym2 (Fin (m + 1)) :=
  s(0, i.succ)

lemma starEdge_injective : Function.Injective (starEdge m) := by
  intro i j h
  rcases Sym2.eq_iff.mp h with ⟨-, h2⟩ | ⟨h1, -⟩
  · exact Fin.succ_injective _ h2
  · exact absurd h1.symm (Fin.succ_ne_zero j)

lemma starGraph_edgeFinset :
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

lemma starGraph_edgeFinset_card :
    (starGraph (0 : Fin (m + 1))).edgeFinset.card = m := by
  rw [starGraph_edgeFinset, Finset.card_image_of_injective _ starEdge_injective,
    Finset.card_univ, Fintype.card_fin]

end OpenProblems.StarFacts
