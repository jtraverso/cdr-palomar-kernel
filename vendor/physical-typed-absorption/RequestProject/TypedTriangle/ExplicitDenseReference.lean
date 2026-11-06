/-
Copyright (c) 2026 Juan Pablo Traverso Gianini.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module
public import RequestProject.TypedTriangle.ExplicitSeedPersistence
public import RequestProject.TypedTriangle.ExplicitNativeApproxPacking
public import RequestProject.TypedTriangle.NativeDenseReference
set_option maxHeartbeats 4000000 -- build option (original: -DmaxHeartbeats=1600000; raised)
set_option maxRecDepth 16384 -- build option (original: -DmaxRecDepth=8192; raised)
@[expose] public section
open Finset Classical
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace TypedTriangle.RawReference.Explicit

def stockBudget (a b α : ℝ) (h : ℕ) : ℝ := min (seedBudget a b α h) (1/(8*b))
def referencePackingPrecision (η : ℝ) : ℝ := min (η/2) (1/2)
def referenceWeightUpper (a b : ℝ) : ℝ := b+a/2
def referencePackingTolerance (η : ℝ) : ℝ := referencePackingPrecision η / 8
def referenceLoadTolerance (η : ℝ) : ℝ := min (referencePackingTolerance η/4) (1/4)
def referenceAvoidBudget (a b η : ℝ) : ℝ :=
  min (η/2) (referencePackingTolerance η/(8*referenceWeightUpper a b))
def referenceOrder (a b η : ℝ) : ℕ :=
  max (max (seedOrder b) (PartitionedTriangleAbsorption.Nibble.Explicit.approxPackingCut
    (referenceWeightUpper a b) (referencePackingPrecision η))) 1

theorem stockBudget_pos {a b α : ℝ} (h : ℕ)
    (ha : 0 < a) (hab : a ≤ b) (hα : 0 < α) : 0 < stockBudget a b α h := by
  have hb := ha.trans_le hab
  exact lt_min (seedBudget_pos h ha hab hα) (by positivity)

theorem referencePackingPrecision_pos {η : ℝ} (hη : 0 < η) :
    0 < referencePackingPrecision η := by unfold referencePackingPrecision; positivity

theorem referenceLoadTolerance_pos {η : ℝ} (hη : 0 < η) :
    0 < referenceLoadTolerance η := by
  have hξ := referencePackingPrecision_pos hη
  unfold referenceLoadTolerance referencePackingTolerance
  positivity

theorem referenceAvoidBudget_pos {a b η : ℝ} (ha : 0 < a) (hab : a ≤ b) (hη : 0 < η) :
    0 < referenceAvoidBudget a b η := by
  have hb := ha.trans_le hab
  have hξ := referencePackingPrecision_pos hη
  unfold referenceAvoidBudget referencePackingTolerance referenceWeightUpper
  positivity

/-- Dense reference containing the specified stock decomposition, with all
thresholds literal and the stock window fixed independently of hole precision. -/
theorem dense_reference_containing_stock_explicit {I : Type} (F : Set (Multiset I))
    (a b α : ℝ) (h : ℕ) (ha : 0 < a) (hab : a ≤ b) (hα : 0 < α) :
    ∀ η : ℝ, 0 < η →
        ∀ {V : Type} [Fintype V] (H : Host V I) (μ : Finset V → ℝ)
          (S B : Finset (Sym2 V)) (DS : Finset (Finset V)) (dS dB : ℕ),
          referenceOrder a b η ≤ Fintype.card V → HingeCond H F α h →
          (∀ T, IsAllowed H F T → a/Fintype.card V ≤ μ T ∧ μ T ≤ b/Fintype.card V) →
          (∀ e ∈ edges H, |bdry H F μ e-1| ≤ referenceLoadTolerance η) →
          S ⊆ edges H → IsDecomposition H F S DS → Disjoint S B →
          (∀ v, degIn S v ≤ dS) → (dS:ℝ) ≤ stockBudget a b α h*Fintype.card V →
          (∀ v, degIn B v ≤ dB) → (dB:ℝ) ≤ referenceAvoidBudget a b η*Fintype.card V →
          ∃ (E₀ : Finset (Sym2 V)) (D₀ : Finset (Finset V)),
            S ⊆ E₀ ∧ E₀ ⊆ edges H ∧ IsDecomposition H F E₀ D₀ ∧ DS ⊆ D₀ ∧
            Disjoint E₀ B ∧ ∀ v, (degIn (edges H\E₀) v:ℝ) ≤ η*Fintype.card V := by
  have hb : 0 < b := ha.trans_le hab
  let θS := seedBudget a b α h
  intro η hη
  let ξ := referencePackingPrecision η
  have hξ : 0 < ξ := lt_min (by positivity) (by norm_num)
  let b' := referenceWeightUpper a b
  have hb' : 0 < b' := by dsimp [b',referenceWeightUpper]; positivity
  let εP := referencePackingTolerance η
  have hεP : 0 < εP := div_pos (referencePackingPrecision_pos hη) (by norm_num)
  let ε := referenceLoadTolerance η
  have hε : 0 < ε := lt_min (by positivity) (by norm_num)
  intro V _ H μ S B DS dS dB hn h4 hμ hload hS hDS hSB hdS hdθ hdB hdγ
  have hn1 : (1:ℕ) ≤ Fintype.card V := (le_max_right _ _).trans hn
  have hn0 : (0:ℝ) < Fintype.card V := by exact_mod_cast (show 0 < Fintype.card V by omega)
  have hdθS : (dS:ℝ) ≤ θS*Fintype.card V := hdθ.trans
    (mul_le_mul_of_nonneg_right (min_le_left _ _) hn0.le)
  obtain ⟨ψ,hψsupp,hψ,hψload⟩ := seed_persistence_approx_explicit (F:=F) ha hab hα h H μ S DS dS ε
    ((le_max_left _ _).trans ((le_max_left _ _).trans hn)) h4 hμ hε.le
    ((min_le_right _ _).trans (by norm_num)) hload hS hDS hdS hdθS
  let J := residual H S
  have hJ : edges J = edges H\S := Residual.edges_subHost_eq sdiff_subset
  have hψ0 : ∀ T, IsAllowed J F T → 0 ≤ ψ T ∧ ψ T ≤ b'/Fintype.card V := by
    intro T hT
    have hh := hψ T hT
    exact ⟨(by positivity : (0:ℝ) ≤ a/(2*Fintype.card V)).trans hh.1,hh.2⟩
  have hfactor : 1+2*(dS:ℝ)*(4*b/Fintype.card V) ≤ 2 := by
    have hdsmall := hdθ.trans (mul_le_mul_of_nonneg_right (min_le_right _ _) hn0.le)
    have hscaled := mul_le_mul_of_nonneg_left hdsmall (show (0:ℝ) ≤ 8*b by positivity)
    have hid : (8*b)*(1/(8*b)*(Fintype.card V:ℝ)) = Fintype.card V := by field_simp
    rw [hid] at hscaled
    have hh : (8*b*dS)/Fintype.card V ≤ 1 := (div_le_one hn0).mpr (by nlinarith)
    calc
      1+2*(dS:ℝ)*(4*b/Fintype.card V) = 1+(8*b*dS)/Fintype.card V := by ring
      _ ≤ 2 := by linarith
  have hψerr : ∀ e ∈ edges J, |bdry J F ψ e-1| ≤ 2*ε := by
    intro e he
    obtain ⟨heH,heS⟩ := mem_sdiff.mp (hJ ▸ he)
    exact (hψload e heH heS).trans (by nlinarith [hε.le])
  have hJerr := load_after_deletion ψ B dB b' (2*ε) hn0 hb'.le hψ0 hdB hψerr
  have hBcost : 2*b'*(dB:ℝ)/Fintype.card V ≤ εP/4 := by
    have hdsmall := hdγ.trans (mul_le_mul_of_nonneg_right (min_le_right _ _) hn0.le)
    rw [div_le_iff₀ hn0]
    have hh := mul_le_mul_of_nonneg_left hdsmall (show (0:ℝ) ≤ 2*b' by positivity)
    have hid : (2*b')*(εP/(8*b')*(Fintype.card V:ℝ)) =
        εP/4*Fintype.card V := by field_simp; ring
    rw [hid] at hh
    nlinarith
  have herr : ∀ e ∈ edges (residual J B), |bdry (residual J B) F ψ e-1| ≤ εP := by
    intro e he
    have hh := hJerr e he
    have heps : ε ≤ εP/4 := min_le_left _ _
    linarith
  obtain ⟨P,hP,hleft⟩ := NativeNibble.Explicit.packing_of_approx_weights_explicit b' ξ hb' hξ
    ((min_le_right _ _).trans (by norm_num)) (residual J B) F ψ
    ((le_max_right _ _).trans ((le_max_left _ _).trans hn))
    (fun T hT => hψ0 T (isAllowed_mono (subHost_le J _) rfl hT)) herr
  have hPsub : P.biUnion triEdges ⊆ (edges H\S)\B := by
    have hh : P.biUnion triEdges ⊆ edges (residual J B) := by
      intro e he
      obtain ⟨T,hT,heT⟩ := mem_biUnion.mp he
      exact triEdges_subset_edges (hP.1 T hT) heT
    rwa [residual,Residual.edges_subHost_eq sdiff_subset,hJ] at hh
  have hPH : IsPacking H F P := ⟨fun T hT =>
    isAllowed_mono (subHost_le H _) rfl
      (isAllowed_mono (subHost_le J _) rfl (hP.1 T hT)),hP.2⟩
  have hSP : Disjoint S (P.biUnion triEdges) := disjoint_left.mpr fun e heS heP =>
    (mem_sdiff.mp (mem_sdiff.mp (hPsub heP)).1).2 heS
  refine ⟨S∪P.biUnion triEdges,DS∪P,subset_union_left,
    union_subset hS (hPsub.trans (sdiff_subset.trans sdiff_subset)),
    hDS.union hPH.isDecomposition hSP,subset_union_left,?_,?_⟩
  · rw [disjoint_union_left]
    exact ⟨hSB,disjoint_left.mpr fun e heP heB => (mem_sdiff.mp (hPsub heP)).2 heB⟩
  · intro v
    have hsub : ((edges H\(S∪P.biUnion triEdges)).filter (fun e => v ∈ e)) ⊆
        B.filter (fun e => v ∈ e) ∪
          ((edges (residual J B)\P.biUnion triEdges).filter (fun e => v ∈ e)) := by
      intro e he
      obtain ⟨he,hv⟩ := mem_filter.mp he
      obtain ⟨heH,heout⟩ := mem_sdiff.mp he
      have heS : e ∉ S := fun hh => heout (mem_union_left _ hh)
      have heP : e ∉ P.biUnion triEdges := fun hh => heout (mem_union_right _ hh)
      by_cases heB : e ∈ B
      · exact mem_union_left _ (mem_filter.mpr ⟨heB,hv⟩)
      · apply mem_union_right
        refine mem_filter.mpr ⟨mem_sdiff.mpr ⟨?_,heP⟩,hv⟩
        rw [residual,Residual.edges_subHost_eq sdiff_subset,hJ]
        exact mem_sdiff.mpr ⟨mem_sdiff.mpr ⟨heH,heS⟩,heB⟩
    have hcount : (degIn (edges H\(S∪P.biUnion triEdges)) v:ℝ) ≤
        degIn B v+(((edges (residual J B)\P.biUnion triEdges).filter (fun e => v ∈ e)).card:ℝ) := by
      exact_mod_cast (card_le_card hsub).trans (card_union_le _ _)
    have hbdeg : (degIn B v:ℝ) ≤ η/2*Fintype.card V :=
      (show (degIn B v:ℝ) ≤ dB by exact_mod_cast hdB v).trans
        (hdγ.trans (mul_le_mul_of_nonneg_right (min_le_left _ _) hn0.le))
    have hpk := (hleft v).trans (mul_le_mul_of_nonneg_right (min_le_left _ _) hn0.le)
    linarith


#print axioms dense_reference_containing_stock_explicit
end TypedTriangle.RawReference.Explicit
