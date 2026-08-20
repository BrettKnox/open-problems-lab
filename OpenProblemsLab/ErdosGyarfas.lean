import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Combinatorics.SimpleGraph.Paths
import Mathlib.Combinatorics.SimpleGraph.Acyclic

/-!
# Erdős–Gyárfás conjecture (cycles of length 2^k)

Every finite simple graph with minimum degree at least 3 contains a cycle
whose length is a power of two.

Status 2026-08-20 (records verified at source; the widely copied
"counterexample ≥ 17 vertices" is folklore with no primary source):
* all graphs, min deg ≥ 3: counterexample ≥ 16 (Royle, webpage, ≤ 2000,
  archived — checked all relevant graphs on ≤ 15 vertices); ≥ 32 (Balaji 2026,
  SAT computation, Zenodo 10.5281/zenodo.21190438, unrefereed).
* cubic: ≥ 30 (Markström, Congr. Numer. 171 (2004): all cubic graphs on ≤ 28
  vertices contain a C4, C8 or C16; exactly 4/23/251 cubic graphs on 24/26/28
  vertices avoid C4 and C8, each containing a C16).
* cubic bipartite: ≥ 60 (Tranquilli, arXiv:2608.02675, 2026).
* Proved for: claw-free with min degree conditions (Shauger 1998), planar
  claw-free (Daniel–Shauger 2001), 3-connected cubic planar
  (Heckman–Krakovski 2013), P₁₃-free (arXiv:2410.22842), diameter 2
  (arXiv:2508.19302). Minimal counterexamples are predominantly cubic
  (arXiv:2605.22844). Not in formal-conjectures.

## What is proved here

* `sweep_reduction` — **the search-space reduction used by every published
  computation, formalized**: if all C4-free graphs of min degree 3 on ≤ n
  vertices satisfy the conjecture, then all graphs of min degree 3 on ≤ n
  vertices do. (A C4 is itself a power-of-two cycle.) This is the formal
  warrant for generating only C4-free graphs (`geng -f`) in
  `computations/erdos_gyarfas/`.
* `exists_cycle_of_two_le_degree` — every finite graph with min degree ≥ 2
  contains a cycle. The base fact under the whole problem (min degree 3 gives
  cycles; the conjecture is about their lengths). Proved via mathlib's
  acyclic-component/tree-leaf machinery.

Attack lanes: extend the cubic record past Markström's 28 via C4-free cubic
generation; independently re-verify Balaji's unrefereed 17–31 range.
-/

namespace OpenProblems.ErdosGyarfas

/-- `G` contains a cycle whose length is a power of two. -/
def HasPow2Cycle {V : Type} (G : SimpleGraph V) : Prop :=
  ∃ (v : V) (w : G.Walk v v), w.IsCycle ∧ ∃ k : ℕ, w.length = 2 ^ k

/-- **Open conjecture** (Erdős–Gyárfás 1995): every finite graph with all
degrees ≥ 3 has a cycle of length `2^k` for some `k`. (Cycles have length
≥ 3, so such `k` is necessarily ≥ 2.) -/
def conjecture : Prop :=
  ∀ (V : Type) [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj],
    (∀ v : V, 3 ≤ G.degree v) → HasPow2Cycle G

/-- The conjecture restricted to graphs on at most `n` vertices. -/
def ConjectureUpTo (n : ℕ) : Prop :=
  ∀ (V : Type) [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj],
    Fintype.card V ≤ n → (∀ v : V, 3 ≤ G.degree v) → HasPow2Cycle G

/-- `G` has no 4-cycle. -/
def C4Free {V : Type} (G : SimpleGraph V) : Prop :=
  ∀ (v : V) (w : G.Walk v v), w.IsCycle → w.length ≠ 4

/-- **The sweep reduction**: to verify the conjecture on all graphs of at most
`n` vertices it suffices to check the C4-free ones — a graph containing a
4-cycle satisfies the conjecture outright, since `4 = 2^2`. This is the formal
justification for restricting exhaustive searches to C4-free generation. -/
theorem sweep_reduction (n : ℕ)
    (h : ∀ (V : Type) [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj],
      Fintype.card V ≤ n → (∀ v : V, 3 ≤ G.degree v) → C4Free G → HasPow2Cycle G) :
    ConjectureUpTo n := by
  intro V _ _ G _ hcard hdeg
  by_cases h4 : C4Free G
  · exact h V G hcard hdeg h4
  · simp only [C4Free, not_forall] at h4
    obtain ⟨v, w, hc, hl⟩ := h4
    exact ⟨v, w, hc, 2, by omega⟩

/-! ### Minimum degree 2 forces a cycle

The ground fact beneath the conjecture: high minimum degree guarantees cycles
exist at all; the conjecture is about their lengths. Proof: if `G` were
acyclic, each connected component is a tree (mathlib), a nontrivial tree has a
leaf, and a leaf contradicts min degree 2; a single-vertex component
contradicts it immediately. -/

/-- In the component graph of `C`, degrees agree with `G`: every `G`-neighbour
of a vertex of `C` lies in `C`. -/
private lemma degree_toSimpleGraph {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (C : G.ConnectedComponent)
    [Fintype C.supp] [DecidableRel C.toSimpleGraph.Adj] (u : C.supp) :
    C.toSimpleGraph.degree u = G.degree u.val := by
  rw [← SimpleGraph.card_neighborSet_eq_degree, ← SimpleGraph.card_neighborSet_eq_degree]
  refine Fintype.card_congr (Equiv.ofBijective (fun w => ⟨w.val.val, w.prop⟩) ⟨?_, ?_⟩)
  · rintro ⟨⟨a, ha⟩, hadj⟩ ⟨⟨b, hb⟩, hbdj⟩ hab
    have : a = b := congrArg Subtype.val hab
    subst this
    rfl
  · rintro ⟨x, hx⟩
    have hxC : x ∈ C.supp := by
      have hu : u.val ∈ C.supp := u.prop
      rw [SimpleGraph.ConnectedComponent.mem_supp_iff] at hu ⊢
      rw [← hu]
      exact SimpleGraph.ConnectedComponent.sound hx.symm.reachable
    exact ⟨⟨⟨x, hxC⟩, hx⟩, rfl⟩

/-- Every finite graph with minimum degree at least 2 contains a cycle. -/
theorem exists_cycle_of_two_le_degree {V : Type} [Fintype V] [DecidableEq V] [Nonempty V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (hdeg : ∀ v : V, 2 ≤ G.degree v) :
    ∃ (v : V) (w : G.Walk v v), w.IsCycle := by
  classical
  by_contra hno
  push Not at hno
  have hac : G.IsAcyclic := fun v w hw => hno v w hw
  obtain ⟨v₀⟩ := ‹Nonempty V›
  set C := G.connectedComponentMk v₀ with hC
  let _ : Fintype C.supp := Fintype.ofFinite _
  let _ : DecidableRel C.toSimpleGraph.Adj := Classical.decRel _
  have htree := hac.isTree_connectedComponent C
  -- `C` is nontrivial: `v₀` has a neighbour, which shares its component
  have hv₀ : v₀ ∈ C.supp := by rw [SimpleGraph.ConnectedComponent.mem_supp_iff]
  have hdegpos : 0 < G.degree v₀ := lt_of_lt_of_le Nat.zero_lt_two (hdeg v₀)
  rw [← SimpleGraph.card_neighborFinset_eq_degree] at hdegpos
  obtain ⟨u₀, hu₀⟩ := Finset.card_pos.mp hdegpos
  rw [SimpleGraph.mem_neighborFinset] at hu₀
  have hu₀C : u₀ ∈ C.supp := by
    rw [SimpleGraph.ConnectedComponent.mem_supp_iff, hC]
    exact SimpleGraph.ConnectedComponent.sound hu₀.symm.reachable
  have : Nontrivial C.supp :=
    ⟨⟨⟨v₀, hv₀⟩, ⟨u₀, hu₀C⟩, by
      simp only [ne_eq, Subtype.mk.injEq]
      exact G.ne_of_adj hu₀⟩⟩
  -- a nontrivial tree has a leaf, but component degrees equal `G` degrees ≥ 2
  obtain ⟨u, hu⟩ := htree.exists_vert_degree_one_of_nontrivial
  have h1 := degree_toSimpleGraph G C u
  have := hdeg u.val
  omega

end OpenProblems.ErdosGyarfas
