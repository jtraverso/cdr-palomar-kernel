/-
Copyright (c) 2026 Juan Pablo Traverso Gianini.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module
public import RequestProject.TypedTriangle.NativeApproxPacking
public import RequestProject.TypedTriangle.RawSeedDeletion
set_option maxHeartbeats 4000000 -- build option (original: -DmaxHeartbeats=1600000; raised)
set_option maxRecDepth 16384 -- build option (original: -DmaxRecDepth=8192; raised)
@[expose] public section
open Finset Classical
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace TypedTriangle.RawReference

/-- Construct a dense basal reference containing a PRESCRIBED decomposition.
The stock window theta is fixed before the desired hole tolerance eta. Its
degree is NOT an additive error in the hole bound. The raw indicator need not
be physical, and a fractional decomposition of the raw host is not assumed.
Exactification on a robust core remains a separate obligation. -/
theorem dense_reference_containing_stock {I : Type} (F : Set (Multiset I))
    (a b α : ℝ) (h : ℕ) (ha : 0 < a) (hab : a ≤ b) (hα : 0 < α) :
    ∃ θ : ℝ, 0 < θ ∧ ∀ η : ℝ, 0 < η →
      ∃ ε γ : ℝ, 0 < ε ∧ 0 < γ ∧ ∃ n₀ : ℕ,
        ∀ {V : Type} [Fintype V] (H : Host V I) (μ : Finset V → ℝ)
          (S B : Finset (Sym2 V)) (DS : Finset (Finset V)) (dS dB : ℕ),
          n₀ ≤ Fintype.card V → HingeCond H F α h →
          (∀ T, IsAllowed H F T → a/Fintype.card V ≤ μ T ∧ μ T ≤ b/Fintype.card V) →
          (∀ e ∈ edges H, |bdry H F μ e-1| ≤ ε) →
          S ⊆ edges H → IsDecomposition H F S DS → Disjoint S B →
          (∀ v, degIn S v ≤ dS) → (dS:ℝ) ≤ θ*Fintype.card V →
          (∀ v, degIn B v ≤ dB) → (dB:ℝ) ≤ γ*Fintype.card V →
          ∃ (E₀ : Finset (Sym2 V)) (D₀ : Finset (Finset V)),
            S ⊆ E₀ ∧ E₀ ⊆ edges H ∧ IsDecomposition H F E₀ D₀ ∧ DS ⊆ D₀ ∧
            Disjoint E₀ B ∧ ∀ v, (degIn (edges H\E₀) v:ℝ) ≤ η*Fintype.card V := by
  have hb : 0 < b := ha.trans_le hab
  obtain ⟨θS,hθS,nS,hSeed⟩ := seed_persistence_approx (F:=F) ha hab hα h
  let θ := min θS (1/(8*b))
  have hθ : 0 < θ := lt_min hθS (by positivity)
  refine ⟨θ,hθ,?_⟩
  intro η hη
  let ξ := min (η/2) (1/2)
  have hξ : 0 < ξ := lt_min (by positivity) (by norm_num)
  let b' := b+a/2
  have hb' : 0 < b' := by dsimp [b']; positivity
  obtain ⟨εP,hεP,nP,hPack⟩ := NativeNibble.packing_of_approx_weights b' ξ hb' hξ
    ((min_le_right _ _).trans (by norm_num))
  let ε := min (εP/4) (1/4)
  let γ := min (η/2) (εP/(8*b'))
  have hε : 0 < ε := lt_min (by positivity) (by norm_num)
  have hγ : 0 < γ := lt_min (by positivity) (by positivity)
  refine ⟨ε,γ,hε,hγ,max (max nS nP) 1,?_⟩
  intro V _ H μ S B DS dS dB hn h4 hμ hload hS hDS hSB hdS hdθ hdB hdγ
  have hn1 : (1:ℕ) ≤ Fintype.card V := (le_max_right _ _).trans hn
  have hn0 : (0:ℝ) < Fintype.card V := by exact_mod_cast (show 0 < Fintype.card V by omega)
  have hdθS : (dS:ℝ) ≤ θS*Fintype.card V := hdθ.trans
    (mul_le_mul_of_nonneg_right (min_le_left _ _) hn0.le)
  obtain ⟨ψ,hψsupp,hψ,hψload⟩ := hSeed H μ S DS dS ε
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
  obtain ⟨P,hP,hleft⟩ := hPack (residual J B) F ψ
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

end TypedTriangle.RawReference
