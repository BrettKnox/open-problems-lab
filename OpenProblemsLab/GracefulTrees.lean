import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Combinatorics.SimpleGraph.Star
import Mathlib.Combinatorics.SimpleGraph.Hasse
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


/-! ### Paths are graceful

The classical zigzag labeling: walk the path labelling `0, m, 1, m-1, 2, …`,
so vertex `i` gets `i/2` when `i` is even and `m - (i-1)/2` when odd. The edge
`{i, i+1}` then carries `m - i`, so the edge labels run `m, m-1, …, 1` — each
of `1..m` exactly once. -/

/-- Zigzag labeling of the path on `m + 1` vertices (so `m` edges). -/
def zig (m : ℕ) (i : Fin (m + 1)) : ℕ :=
  if i.val % 2 = 0 then i.val / 2 else m - (i.val - 1) / 2

private lemma zig_even {m : ℕ} (i : Fin (m + 1)) (h : i.val % 2 = 0) :
    zig m i = i.val / 2 := by simp [zig, h]

private lemma zig_odd {m : ℕ} (i : Fin (m + 1)) (h : i.val % 2 = 1) :
    zig m i = m - (i.val - 1) / 2 := by simp [zig, h]

/-- The zigzag labels are bounded by `m`. -/
private lemma zig_le {m : ℕ} (i : Fin (m + 1)) : zig m i ≤ m := by
  rcases Nat.even_or_odd i.val with he | ho
  · rw [zig_even i (Nat.even_iff.mp he)]
    have := i.isLt
    omega
  · rw [zig_odd i (Nat.odd_iff.mp ho)]
    omega

/-- Consecutive vertices differ by exactly `m - i`. -/
private lemma zig_step {m : ℕ} (i : ℕ) (hi : i < m)
    (hI : i < m + 1) (hJ : i + 1 < m + 1) :
    Nat.dist (zig m ⟨i, hI⟩) (zig m ⟨i + 1, hJ⟩) = m - i := by
  rcases Nat.even_or_odd i with he | ho
  · have h0 : i % 2 = 0 := Nat.even_iff.mp he
    have h1 : (i + 1) % 2 = 1 := by omega
    rw [zig_even ⟨i, hI⟩ h0, zig_odd ⟨i + 1, hJ⟩ h1]
    simp only []
    have : (i + 1 - 1) / 2 = i / 2 := by omega
    rw [this]
    have hhalf : i / 2 ≤ i := Nat.div_le_self i 2
    have : 2 * (i / 2) = i := by omega
    unfold Nat.dist
    omega
  · have h1 : i % 2 = 1 := Nat.odd_iff.mp ho
    have h0 : (i + 1) % 2 = 0 := by omega
    rw [zig_odd ⟨i, hI⟩ h1, zig_even ⟨i + 1, hJ⟩ h0]
    simp only []
    have hh : (i + 1) / 2 = (i - 1) / 2 + 1 := by omega
    rw [hh]
    have : 2 * ((i - 1) / 2) = i - 1 := by omega
    unfold Nat.dist
    omega


/-- The zigzag labeling is injective: even positions occupy the low half of
`{0..m}` and odd positions the high half, and each half is hit once. -/
private lemma zig_injective {m : ℕ} : Function.Injective (zig m) := by
  intro a b hab
  by_contra hne
  have hane : a.val ≠ b.val := fun h => hne (Fin.ext h)
  have ha := a.isLt
  have hb := b.isLt
  rcases Nat.even_or_odd a.val with hae | hao <;> rcases Nat.even_or_odd b.val with hbe | hbo
  · rw [zig_even a (Nat.even_iff.mp hae), zig_even b (Nat.even_iff.mp hbe)] at hab
    have hpa := Nat.even_iff.mp hae
    have hpb := Nat.even_iff.mp hbe
    obtain ⟨q, hq⟩ : ∃ q, a.val / 2 = q := ⟨_, rfl⟩
    obtain ⟨r, hr⟩ : ∃ r, b.val / 2 = r := ⟨_, rfl⟩
    rw [hq, hr] at hab
    have h2a : 2 * q = a.val := by omega
    have h2b : 2 * r = b.val := by omega
    omega
  · rw [zig_even a (Nat.even_iff.mp hae), zig_odd b (Nat.odd_iff.mp hbo)] at hab
    have hpa := Nat.even_iff.mp hae
    have hpb := Nat.odd_iff.mp hbo
    -- even index sits in the low half, odd index in the high half
    obtain ⟨q, hq⟩ : ∃ q, a.val / 2 = q := ⟨_, rfl⟩
    obtain ⟨r, hr⟩ : ∃ r, (b.val - 1) / 2 = r := ⟨_, rfl⟩
    rw [hq, hr] at hab
    have h2a : 2 * q = a.val := by omega
    have h2b : 2 * r = b.val - 1 := by omega
    omega
  · rw [zig_odd a (Nat.odd_iff.mp hao), zig_even b (Nat.even_iff.mp hbe)] at hab
    have hpa := Nat.odd_iff.mp hao
    have hpb := Nat.even_iff.mp hbe
    obtain ⟨q, hq⟩ : ∃ q, (a.val - 1) / 2 = q := ⟨_, rfl⟩
    obtain ⟨r, hr⟩ : ∃ r, b.val / 2 = r := ⟨_, rfl⟩
    rw [hq, hr] at hab
    have h2a : 2 * q = a.val - 1 := by omega
    have h2b : 2 * r = b.val := by omega
    omega
  · rw [zig_odd a (Nat.odd_iff.mp hao), zig_odd b (Nat.odd_iff.mp hbo)] at hab
    have hpa := Nat.odd_iff.mp hao
    have hpb := Nat.odd_iff.mp hbo
    obtain ⟨q, hq⟩ : ∃ q, (a.val - 1) / 2 = q := ⟨_, rfl⟩
    obtain ⟨r, hr⟩ : ∃ r, (b.val - 1) / 2 = r := ⟨_, rfl⟩
    rw [hq, hr] at hab
    have h2a : 2 * q = a.val - 1 := by omega
    have h2b : 2 * r = b.val - 1 := by omega
    omega

/-- Adjacency in the path graph is decidable, so its edge set is a `Fintype`
through the usual chain (needed to talk about `edgeFinset` at all). -/
instance pathGraphDecidableAdj (n : ℕ) : DecidableRel (pathGraph n).Adj :=
  fun _ _ => decidable_of_iff _ pathGraph_adj.symm

/-- Edge enumeration of `pathGraph (m+1)`: edge `i` joins `i` to `i+1`. -/
def pathEdge (m : ℕ) (i : Fin m) : Sym2 (Fin (m + 1)) :=
  s(⟨i.val, by omega⟩, ⟨i.val + 1, by omega⟩)

private lemma pathEdge_injective {m : ℕ} : Function.Injective (pathEdge m) := by
  intro i j h
  rcases Sym2.eq_iff.mp h with ⟨h1, -⟩ | ⟨h1, h2⟩
  · exact Fin.ext (by simpa using congrArg Fin.val h1)
  · exfalso
    have := congrArg Fin.val h1
    have := congrArg Fin.val h2
    simp only [] at *
    omega

private lemma pathGraph_edgeFinset {m : ℕ} :
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


/-- **Paths are graceful** — the zigzag labeling. Together with
`pathGraph_connected` and acyclicity this is a second infinite family
witnessing the Ringel–Kotzig conjecture. -/
theorem isGraceful_pathGraph {m : ℕ} : IsGraceful (pathGraph (m + 1)) := by
  classical
  have hcard : (pathGraph (m + 1)).edgeFinset.card = m := by
    rw [pathGraph_edgeFinset, Finset.card_image_of_injective _ pathEdge_injective,
      Finset.card_univ, Fintype.card_fin]
  have hlab : ∀ i : Fin m, edgeLabel (zig m) (pathEdge m i) = m - i.val := by
    intro i
    have := zig_step (m := m) i.val i.isLt (by omega) (by omega)
    simpa [edgeLabel, pathEdge] using this
  refine ⟨zig m, zig_injective, ?_, ?_⟩
  · intro v
    rw [hcard]
    exact zig_le v
  · rw [hcard, ← SimpleGraph.coe_edgeFinset, pathGraph_edgeFinset]
    refine ⟨?_, ?_, ?_⟩
    · rintro e he
      simp only [Finset.coe_image, Finset.coe_univ, Set.image_univ, Set.mem_range] at he
      obtain ⟨i, rfl⟩ := he
      rw [hlab]
      simp only [Set.mem_Icc]
      have := i.isLt
      omega
    · rintro e₁ he₁ e₂ he₂ h
      simp only [Finset.coe_image, Finset.coe_univ, Set.image_univ, Set.mem_range] at he₁ he₂
      obtain ⟨i, rfl⟩ := he₁
      obtain ⟨j, rfl⟩ := he₂
      rw [hlab, hlab] at h
      have hi := i.isLt
      have hj := j.isLt
      exact congrArg (pathEdge m) (Fin.ext (by omega))
    · rintro k hk
      simp only [Set.mem_Icc] at hk
      refine ⟨pathEdge m ⟨m - k, by omega⟩, ?_, ?_⟩
      · simp only [Finset.coe_image, Finset.coe_univ, Set.image_univ, Set.mem_range]
        exact ⟨_, rfl⟩
      · rw [hlab]
        show m - (m - k) = k
        omega

/-- Stars witness the conjecture: a genuine tree family, graceful. -/
theorem starGraph_isTree_and_graceful :
    (starGraph (0 : Fin (m + 1))).IsTree ∧ IsGraceful (starGraph (0 : Fin (m + 1))) :=
  ⟨isTree_starGraph 0, isGraceful_starGraph⟩

end OpenProblems.GracefulTrees
