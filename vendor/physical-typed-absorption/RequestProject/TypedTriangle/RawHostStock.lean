/-
Copyright (c) 2026 Juan Pablo Traverso Gianini.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module
public import RequestProject.TypedTriangle.NativeDenseReference
public import RequestProject.TypedTriangle.NativeBasalStock
public import RequestProject.TypedTriangle.RawHostWithdrawal
set_option maxHeartbeats 4000000 -- build option (original: -DmaxHeartbeats=1600000; raised)
set_option maxRecDepth 16384 -- build option (original: -DmaxRecDepth=8192; raised)
@[expose] public section
open Finset Classical
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 3200000
namespace TypedTriangle.BasalIncidence

/-- On a RAW host, build a thin completion stock avoiding both a prescribed
basal future stock and arbitrary small forbidden edges. Neither exact loads nor
H2 of the raw host are assumed. The future-stock and raw-profile windows are
fixed before the requested density rho of the new stock. -/
theorem reserve_from_raw_profile {I : Type} (F : Set (Multiset I))
    (a b α : ℝ) (h : ℕ) (ha : 0 < a) (hab : a ≤ b) (hα : 0 < α) :
    ∃ θ ε γ : ℝ, 0 < θ ∧ 0 < ε ∧ 0 < γ ∧
      ∀ ρ : ℝ, 0 < ρ → ∃ κ : ℝ, 0 < κ ∧ ∃ n₀ : ℕ,
        ∀ {V : Type} [Fintype V] (H : Host V I) (μ : Finset V → ℝ)
          (S B : Finset (Sym2 V)) (DS : Finset (Finset V)) (dS dB : ℕ),
          n₀ ≤ Fintype.card V → CommonNbrCond H F α → HingeCond H F α h →
          (∀ T, IsAllowed H F T → a/Fintype.card V ≤ μ T ∧ μ T ≤ b/Fintype.card V) →
          (∀ e ∈ edges H, |bdry H F μ e-1| ≤ ε) →
          S ⊆ edges H → IsDecomposition H F S DS → Disjoint S B →
          (∀ v, degIn S v ≤ dS) → (dS:ℝ) ≤ θ*Fintype.card V →
          (∀ v, degIn B v ≤ dB) → (dB:ℝ) ≤ γ*Fintype.card V →
          ∃ D : Finset (Finset V), IsDecomposition H F (cover D) D ∧
            Disjoint (cover D) (S∪B) ∧
            (∀ v, (degIn (cover D) v:ℝ) < ρ*Fintype.card V) ∧
            ∀ u v, H.G.Adj u v → κ*Fintype.card V ≤ (good H F D u v).card := by
  obtain ⟨θR,hθR,hRef⟩ := RawReference.dense_reference_containing_stock F a b α h ha hab hα
  obtain ⟨εR,γ,hεR,hγ,nR,hReference⟩ := hRef (α/8) (by positivity)
  let θ := min θR (α/8)
  let ε := min εR (1/2)
  have hθ : 0 < θ := lt_min hθR (by positivity)
  have hε : 0 < ε := lt_min hεR (by norm_num)
  refine ⟨θ,ε,γ,hθ,hε,hγ,?_⟩
  intro ρ hρ
  let q := min (ρ/12) (1/2)
  have hq : 0 < q := lt_min (by positivity) (by norm_num)
  obtain ⟨nSample,hSample⟩ := sample_packing q (α/2) hq
    ((min_le_right _ _).trans (by norm_num)) (by positivity)
  refine ⟨α/2*q^2/2,by positivity,max nR nSample,?_⟩
  intro V _ H μ S B DS dS dB hn h3 h4 hμ hload hS hDS hSB hdS hdθ hdB hdγ
  have hε1 : ε < 1 := (min_le_right _ _).trans_lt (by norm_num)
  have hCover := CorePaid.edge_covered_of_approx μ hε1 hload
  obtain ⟨E₀,D₀,hSE,hE,hD₀,hDS₀,hEB,hHoles⟩ :=
    hReference H μ S B DS dS dB ((le_max_left _ _).trans hn) h4 hμ
      (fun e he => (hload e he).trans (min_le_left _ _)) hS hDS hSB hdS
      (hdθ.trans (mul_le_mul_of_nonneg_right (min_le_left _ _) (by positivity))) hdB hdγ
  let P := D₀\DS
  have hPdec : IsDecomposition H F (E₀\S) P := by
    simpa only [hDS.2.2] using hD₀.sdiff_sub hDS₀
  have hPack : IsPacking H F P := ⟨hPdec.1,hPdec.2.1⟩
  have hPE : cover P = E₀\S := hPdec.2.2
  have hPdis : Disjoint (cover P) (S∪B) := by
    rw [hPE,disjoint_union_right]
    exact ⟨sdiff_disjoint,hEB.mono_left sdiff_subset⟩
  have hMissing : ∀ v, (((edges H\cover P).filter (fun e => v ∈ e)).card:ℝ) ≤
      (α/4)*Fintype.card V := by
    intro v
    have hs : (edges H\cover P).filter (fun e => v ∈ e) ⊆
        (edges H\E₀).filter (fun e => v ∈ e) ∪ S.filter (fun e => v ∈ e) := by
      intro e he
      obtain ⟨he,hv⟩ := mem_filter.mp he
      by_cases heS : e ∈ S
      · exact mem_union_right _ (mem_filter.mpr ⟨heS,hv⟩)
      · apply mem_union_left
        refine mem_filter.mpr ⟨mem_sdiff.mpr ⟨(mem_sdiff.mp he).1,?_⟩,hv⟩
        intro heE
        exact (mem_sdiff.mp he).2 (hPE.symm ▸ mem_sdiff.mpr ⟨heE,heS⟩)
    have hc : (((edges H\cover P).filter (fun e => v ∈ e)).card:ℝ) ≤
        degIn (edges H\E₀) v+degIn S v := by
      exact_mod_cast (card_le_card hs).trans (card_union_le _ _)
    have hstock : (degIn S v:ℝ) ≤ (α/8)*Fintype.card V :=
      (show (degIn S v:ℝ) ≤ dS by exact_mod_cast hdS v).trans
        (hdθ.trans (mul_le_mul_of_nonneg_right (min_le_right _ _) (by positivity)))
    nlinarith [hHoles v]
  let A := {uv : V×V // H.G.Adj uv.1 uv.2}
  let u : A → V := fun t => t.val.1
  let v : A → V := fun t => t.val.2
  have hA : Fintype.card A ≤ Fintype.card V^2 := by
    calc
      Fintype.card A ≤ Fintype.card (V×V) := Fintype.card_subtype_le _
      _ = _ := by rw [Fintype.card_prod]; ring
  have hSupply : ∀ t : A, (α/2)*Fintype.card V ≤ (good H F P (u t) (v t)).card := by
    intro t
    obtain ⟨T,hT,heT⟩ := hCover s(u t,v t) (by simpa [SparseEdge.edges] using t.property)
    obtain ⟨w,hw⟩ := eq_insert_of_mem_triEdges hT.1 heT
    have hTa : IsAllowed H F {u t,v t,w} := by
      rwa [tri_eq_insert_toFinset,←hw]
    have hh := good_supply h3 P hMissing hTa
    nlinarith only [hh]
  obtain ⟨D,hDP,hD,hSmall,hGood⟩ := hSample V I H F P hPack
    ((le_max_right _ _).trans hn) A u v hA hSupply
  refine ⟨D,hD,?_,?_,?_⟩
  · apply hPdis.mono_left
    intro e he
    obtain ⟨T,hT,heT⟩ := mem_biUnion.mp he
    exact mem_biUnion.mpr ⟨T,hDP hT,heT⟩
  · intro x
    have hh := hSmall x
    have hqρ : q ≤ ρ/12 := min_le_left _ _
    change (((cover D).filter (fun e => x ∈ e)).card:ℝ) < ρ*Fintype.card V
    nlinarith [mul_le_mul_of_nonneg_right hqρ (show (0:ℝ) ≤ Fintype.card V by positivity)]
  · intro x y hxy
    have hh := hGood ⟨(x,y),hxy⟩
    dsimp only [u,v] at hh
    nlinarith only [hh]

end TypedTriangle.BasalIncidence
