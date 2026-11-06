module
public import RequestProject.TypedTriangle.PaschProtectedLocalizedMoments
public import RequestProject.TypedTriangle.PaschProtectedTarget
set_option maxHeartbeats 4000000 -- build option (original: -DmaxHeartbeats=1600000; raised)
set_option maxRecDepth 16384 -- build option (original: -DmaxRecDepth=8192; raised)
@[expose] public section
open Finset Classical
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace TypedTriangle.Pasch
open ProtectedNibble LocalizedCover

/-- The protected physical nibble controls local edge moments and compares
its unoriented Pasch count with the ORIGINAL seed. The residual seed is
constructed exactly; its perturbation and the removed-domain loss are paid
before the packing is selected. -/
theorem protected_localized_packing_with_pasch {I : Type} (F : Set (Multiset I))
    (C α η τ L σ : ℝ) (h q : ℕ) (hC : 1 ≤ C) (hα : 0 < α) (hη : 0 < η)
    (hτ : 0 < τ) (hL : 0 < L) (hσ : 0 < σ) :
    ∃ ε : ℝ, 0 < ε ∧ ∃ n₀ : ℕ,
      ∀ {V : Type} [Fintype V] (H : Host V I) (φ : Finset V → ℝ)
        (R : Finset (Sym2 V)) (D : Finset (Finset V)) (d : ℕ),
      n₀ ≤ Fintype.card V → IsDiffuseSeed H F C φ → IsPhysical H F (edges H) →
      CommonNbrCond H F α → HingeCond H F α h → IsDecomposition H F R D →
      (∀ v, degIn R v ≤ d) → (d:ℝ) ≤ ε*Fintype.card V →
      ∀ (κ : Type) [Fintype κ] (bad : κ → Finset V) (lam : κ → Sym2 V → ℝ),
        (Fintype.card κ:ℝ) ≤ (Fintype.card V:ℝ)^q →
        (∀ k T, IsAllowed H F T → |triSum (lam k) T| ≤ 3*L*(T∩bad k).card) →
        ∃ P : Finset (Finset V), IsPacking H F P ∧ Disjoint (P.biUnion triEdges) R ∧
          IsPhysical H F ((edges H\R)\P.biUnion triEdges) ∧
          (∀ v, (((((edges H\R)\P.biUnion triEdges).filter (fun e => v ∈ e)).card):ℝ) ≤ η*Fintype.card V) ∧
          (∀ k, |edgeSum (lam k) ((edges H\R)\P.biUnion triEdges)| ≤
            τ*Fintype.card V*(bad k).card) ∧
          |(count P:ℝ)-target φ (allowed H F)| ≤ σ*(Fintype.card V:ℝ)^2 := by
  have hC0 : 0 < C := lt_of_lt_of_le zero_lt_one hC
  let K := ExplicitSeed.seedPointwiseCost α C h
  have hK : 0 ≤ K := ExplicitSeed.seedPointwiseCost_nonneg h hα hC0
  let δ := targetPaymentBudget C K σ
  have hδ : 0 < δ := targetPaymentBudget_pos hC0 hK hσ
  have hδbounds := targetPaymentBudget_bounds hC0 hK hσ
  obtain ⟨ε0,hε0,N0,hPack⟩ := protected_localized_packing_with_residual_pasch F C α η τ L (σ/2)
    h q hC hα hη hτ hL (by positivity)
  let ε := min ε0 δ
  refine ⟨ε,lt_min hε0 hδ,max 1 N0,?_⟩
  intro V _ H φ R D d hn hφ h2 h3 h4 hD hdeg hd κ _ bad lam hκ htri
  have hnNat : 0 < Fintype.card V := by omega
  have hn0 : 0 < (Fintype.card V:ℝ) := by exact_mod_cast hnNat
  have hd0 : (d:ℝ) ≤ ε0*Fintype.card V := hd.trans
    (mul_le_mul_of_nonneg_right (min_le_left _ _) hn0.le)
  have hdδ : (d:ℝ) ≤ δ*Fintype.card V := hd.trans
    (mul_le_mul_of_nonneg_right (min_le_right _ _) hn0.le)
  obtain ⟨ψ,P,hψ,hSupp,hClose,hP,hDis,hPhys,hSparse,hMoment,hPasch⟩ :=
    hPack H φ R D d ((le_max_right _ _).trans hn) hφ h2 h3 h4 hD hdeg hd0 κ bad lam hκ htri
  have hRsub : R ⊆ edges H := by
    rw [←hD.2.2]
    intro e he
    obtain ⟨T,hT,heT⟩ := mem_biUnion.mp he
    exact triEdges_subset_edges (hD.1 T hT) heT
  have hTransfer := protected_target_transfer hC0 hφ R hRsub K δ (d:ℝ) hK hδ.le hdδ
    hδbounds.1 (fun v => (show (degIn R v:ℝ) ≤ d by exact_mod_cast hdeg v).trans hdδ)
    hClose hn0
  have hPaid : |target ψ (allowed (residual H R) F)-target φ (allowed H F)| ≤
      (σ/2)*(Fintype.card V:ℝ)^2 := hTransfer.trans
    (mul_le_mul_of_nonneg_right hδbounds.2 (sq_nonneg _))
  refine ⟨P,hP,hDis,hPhys,hSparse,hMoment,?_⟩
  calc
    _ ≤ |(count P:ℝ)-target ψ (allowed (residual H R) F)|+
        |target ψ (allowed (residual H R) F)-target φ (allowed H F)| := abs_sub_le _ _ _
    _ ≤ (σ/2)*(Fintype.card V:ℝ)^2+(σ/2)*(Fintype.card V:ℝ)^2 := add_le_add hPasch hPaid
    _ = _ := by ring

#print axioms protected_localized_packing_with_pasch
end TypedTriangle.Pasch
