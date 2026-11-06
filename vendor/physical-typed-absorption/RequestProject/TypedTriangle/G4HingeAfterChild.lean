/-
Copyright (c) 2026 Juan Pablo Traverso Gianini.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module
public import RequestProject.TypedTriangle.NativeSharedCorePreparation
public import RequestProject.S07V49.EdgePackage
set_option maxHeartbeats 4000000 -- build option (original: -DmaxHeartbeats=1600000; raised)
set_option maxRecDepth 16384 -- build option (original: -DmaxRecDepth=8192; raised)
@[expose] public section

/-! The edge-deletion hinge count of V49 implies ordinary H4 on the same
residual graph. The core used by V49 is only a counting witness; it need not
be the child used by the positive selector or dense reference. -/

open Finset Classical
noncomputable section
namespace TypedTriangle.StockEntry
open S07V49

theorem g4_hinge_after_graph_deletion {I : Type} (F : Set (Multiset I))
    (α C δ : ℝ) (h : ℕ) (hα : 0 < α) (hC : 0 < C) (hδ : 0 < δ)
    (hh : 6 ≤ h) :
    ∃ η : ℝ, 0 < η ∧ ∃ n₀ : ℕ,
      ∀ {V : Type} [Fintype V] (H : Host V I) (φ : Finset V → ℝ)
        (B : SimpleGraph V) (d : ℕ),
        n₀ ≤ Fintype.card V → IsDiffuseSeed H F C φ →
        CommonNbrCond H F α → HingeCond H F α h →
        (∀ v, B.degree v ≤ d) → (d:ℝ) ≤ η*Fintype.card V →
        HingeCond (⟨H.G\B,H.lab⟩ : Host V I) F
          (hingeConstB α 1 h) (2*h-3) := by
  obtain ⟨t,a,ε,σ,η,n₀,ht,ht3,ha,hε,hσ,hη,hMain⟩ :=
    S07_core_seed_edge_package α 1 C δ h hα (by norm_num) (by norm_num)
      hh hC hδ
  refine ⟨η,hη,n₀,?_⟩
  intro V _ H φ B d hn hSeed h3 h4 hB hd
  letI : DecidableEq V := Classical.decEq V
  letI : DecidableRel B.Adj := Classical.decRel B.Adj
  obtain ⟨W,hW⟩ := hMain V I H.G H.lab F
    ((commonNbrCond_iff_sparseEdge H F α).mp h3)
    ((hingeCond_iff_sparseEdge H F α h).mp h4) hn φ
    (CorePaid.diffuse_seed_for_sample hSeed)
  obtain ⟨hBase,hDelete⟩ := hW
  have hEmpty : ((∅ : Finset V).card:ℝ) ≤ σ*Fintype.card V := by
    simp only [card_empty, Nat.cast_zero]
    positivity
  obtain ⟨_,_,_,_,_,_,hHinge⟩ := hDelete ∅ hEmpty B d hB hd
  intro u v x y hxy hx hy
  have hTest : S07V24.HingeTest (H.G\B) H.lab F u v x y := ⟨hxy,hx,hy⟩
  obtain ⟨i,hi9,hiMax,hiCount⟩ := hHinge u v x y hTest
  refine ⟨i,by omega,hiMax,?_⟩
  change hingeConstB α 1 h * (Fintype.card V:ℝ) ^ (i-4) ≤
    (SparseEdge.hinges (H.G\B) H.lab F u v x y i).card
  exact hiCount.trans (by exact_mod_cast (Finset.card_filter_le _ _))

end TypedTriangle.StockEntry
