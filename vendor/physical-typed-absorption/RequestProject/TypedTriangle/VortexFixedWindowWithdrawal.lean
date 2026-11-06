/-
Copyright (c) 2026 Juan Pablo Traverso Gianini.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module
public import RequestProject.TypedTriangle.G3UniformResources
set_option maxHeartbeats 4000000 -- build option (original: -DmaxHeartbeats=1600000; raised)
set_option maxRecDepth 16384 -- build option (original: -DmaxRecDepth=8192; raised)
@[expose] public section

open Finset Classical
noncomputable section
set_option maxHeartbeats 3200000

namespace TypedTriangle.Vortex
open CorePaid BasalIncidence SelSimul

/-- The positive selector can be placed on a prescribed prepared window. Its
old protected stock and its new completion stock are both kept disjoint from
the selector. The only geometric inputs are the route and completion pools on
this very window; the window is not selected anew. -/
theorem uniform_fixed_window_withdrawal {I : Type}
    (F : Set (Multiset I)) (α q ε : ℝ) (t : ℕ)
    (hα : 0 < α) (hq : 0 < q) (hε : 0 < ε)
    (ht : Odd t) (ht3 : 3 ≤ t) :
    ∃ θ : ℝ, 0 < θ ∧ ∀ τ : ℝ, 0 < τ →
      ∃ δ : ℝ, 0 < δ ∧ ∃ n₀ : ℕ,
      ∀ {V : Type} [Fintype V] (H : Host V I) (W : Finset V),
      IsPhysical H F (edges H) → n₀ ≤ Fintype.card V →
      q * Fintype.card V / 2 ≤ W.card →
      (∀ u v : V, u ≠ v → ∀ k : I,
        ({H.lab u, H.lab v, k} : Multiset I) ∈ F →
        q * α * Fintype.card V / 2 ≤ ((commonNbrs H k u v) ∩ W).card) →
      S07V27.RouteProp H.G H.lab F t ε W →
      ∀ (D : Finset (Finset V)) (T : Finset (Sym2 V)) (r b : ℕ),
        cover D ⊆ edges H → T ⊆ edges H →
        (∀ v, degIn (cover D) v ≤ r) →
        (∀ v, degIn T v ≤ b) →
        (r : ℝ) ≤ δ * Fintype.card V →
        (b : ℝ) ≤ θ * Fintype.card V →
        ∃ R : Finset (Sym2 V),
          Disjoint R (cover D ∪ T) ∧ Basal H F R ∧
          (∀ v, (edeg R v : ℝ) ≤ τ * Fintype.card V) ∧
          (∃ Y0 : Finset (Sym2 V), Basal H F Y0 ∧ Y0 ⊆ R ∧
            (∀ e ∈ Y0, ∀ v ∈ e, v ∈ W) ∧
            ∀ v, (edeg Y0 v : ℝ) ≤ τ * Fintype.card V) ∧
          ∀ L : Finset (Sym2 V), L ⊆ cover D → IsPhysical H F L →
            ∃ Ps Y : Finset (Sym2 V),
              R ∪ L = Ps ∪ Y ∧ Disjoint Ps Y ∧ Basal H F Ps ∧
              (∀ e ∈ Y, ∀ v ∈ e, v ∈ W) ∧
              (∀ v, (edeg Y v : ℝ) ≤ τ * Fintype.card V) ∧
              IsPhysical H F Y := by
  obtain ⟨θ,hθ,hWithdraw⟩ := fixed_core_positive_withdrawal_uniform α q ε t
    hα hq ht ht3 hε
  refine ⟨θ,hθ,?_⟩
  intro τ hτ
  obtain ⟨δ,n₀,hδ,hSel⟩ := hWithdraw τ hτ
  refine ⟨δ,hδ,n₀,?_⟩
  intro V _ H W h2 hn hW hpool hroute D T r b hD hT hdD hdT hr hb
  let X := SimpleGraph.fromEdgeSet (cover D : Set (Sym2 V))
  let B := SimpleGraph.fromEdgeSet (T : Set (Sym2 V))
  letI : DecidableRel X.Adj := Classical.decRel _
  letI : DecidableRel B.Adj := Classical.decRel _
  letI : Fintype X.edgeSet := X.fintypeEdgeSet
  letI : Fintype B.edgeSet := B.fintypeEdgeSet
  have hXmem (e : Sym2 V) : e ∈ X.edgeSet ↔ e ∈ cover D := by
    simp only [X, SimpleGraph.edgeSet_fromEdgeSet, Set.mem_sdiff, mem_coe,
      Sym2.mem_diagSet]
    exact ⟨And.left, fun he => ⟨he, edges_diagonal_free hD e he⟩⟩
  have hBmem (e : Sym2 V) : e ∈ B.edgeSet ↔ e ∈ T := by
    simp only [B, SimpleGraph.edgeSet_fromEdgeSet, Set.mem_sdiff, mem_coe,
      Sym2.mem_diagSet]
    exact ⟨And.left, fun he => ⟨he, edges_diagonal_free hT e he⟩⟩
  have hXd : ∀ v, X.degree v ≤ r := by
    intro v
    have hv := fromEdges_degree_le _ (edges_diagonal_free hD) hdD v
    convert hv using 1 <;> congr 2 <;> apply Subsingleton.elim
  have hBd : ∀ v, B.degree v ≤ b := by
    intro v
    have hv := fromEdges_degree_le _ (edges_diagonal_free hT) hdT v
    convert hv using 1 <;> congr 2 <;> apply Subsingleton.elim
  obtain ⟨R,hdis,hbasal,hdeg,hY0,hMode⟩ := hSel H F W h2 hn hW hpool hroute
    X B r b (fromEdges_le_host hD) hXd hBd hr hb
  refine ⟨R,?_,hbasal,hdeg,hY0,?_⟩
  · apply disjoint_left.mpr
    intro e heR he
    apply disjoint_left.mp hdis heR
    rcases mem_union.mp he with he | he
    · apply mem_union_left
      simpa only [SimpleGraph.mem_edgeFinset] using (hXmem e).mpr he
    · apply mem_union_right
      simpa only [SimpleGraph.mem_edgeFinset] using (hBmem e).mpr he
  · intro L hL hphys
    apply hMode L ?_ hphys
    intro e he
    simpa only [SimpleGraph.mem_edgeFinset] using (hXmem e).mpr (hL he)

#print axioms uniform_fixed_window_withdrawal

end TypedTriangle.Vortex
