/-
Copyright (c) 2026 Juan Pablo Traverso Gianini.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module
public import RequestProject.TypedTriangle.NativeBasalStock
public import RequestProject.TypedTriangle.ProtectedSeedNibble
set_option maxHeartbeats 4000000 -- build option (original: -DmaxHeartbeats=1600000; raised)
set_option maxRecDepth 16384 -- build option (original: -DmaxRecDepth=8192; raised)
@[expose] public section
open Finset Classical
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace TypedTriangle.BasalIncidence

/-- Construct the actual completion stock AFTER a sparse basal terminal has
been fixed. The stock avoids that terminal and still supplies every original
host edge. No stock or completion-supply provider is a premise. -/
theorem reserve_avoiding_basal {I : Type} (F : Set (Multiset I))
    (C α ρ : ℝ) (h : ℕ) (hC : 1 ≤ C) (hα : 0 < α) (hρ : 0 < ρ) :
    ∃ ε κ : ℝ, 0 < ε ∧ 0 < κ ∧ ∃ n₀ : ℕ,
      ∀ {V : Type} [Fintype V] (H : Host V I) (φ : Finset V → ℝ)
        (T : Finset (Sym2 V)) (DT : Finset (Finset V)) (dT : ℕ),
        n₀ ≤ Fintype.card V → IsDiffuseSeed H F C φ →
        IsPhysical H F (edges H) → CommonNbrCond H F α → HingeCond H F α h →
        IsDecomposition H F T DT → (∀ v, SparseEdge.degIn T v ≤ dT) →
        (dT:ℝ) ≤ ε*Fintype.card V →
        ∃ D : Finset (Finset V), IsDecomposition H F (cover D) D ∧
          Disjoint (cover D) T ∧
          (∀ v, (SparseEdge.degIn (cover D) v:ℝ) < ρ*Fintype.card V) ∧
          ∀ u v, H.G.Adj u v → κ*Fintype.card V ≤ (good H F D u v).card := by
  let η := min (α/8) (1/2)
  have hη : 0 < η := lt_min (by positivity) (by norm_num)
  obtain ⟨εP,hεP,nP,hP⟩ := ProtectedNibble.packing_away_from_basal_reserve
    F C α η h hC hα hη ((min_le_right _ _).trans (by norm_num))
  let ε := min εP (α/8)
  let q := min (ρ/12) (1/2)
  have hε : 0 < ε := lt_min hεP (by positivity)
  have hq : 0 < q := lt_min (by positivity) (by norm_num)
  obtain ⟨nS,hS⟩ := sample_packing q (α/2) hq
    ((min_le_right _ _).trans (by norm_num)) (by positivity)
  refine ⟨ε,α/2*q^2/2,hε,by positivity,max nP nS,?_⟩
  intro V _ H φ T DT dT hn hseed h2 h3 h4 hT hTd hTs
  obtain ⟨P,hPack,hPT,_,hUd⟩ := hP H φ T DT dT ((le_max_left _ _).trans hn)
    hseed h2 h4 hT hTd (hTs.trans (mul_le_mul_of_nonneg_right
      (min_le_left _ _) (by positivity)))
  have hMiss : ∀ v, (((edges H\cover P).filter (fun e => v ∈ e)).card:ℝ) ≤
      (α/4)*Fintype.card V := by
    intro v
    have hsub : (edges H\cover P).filter (fun e => v ∈ e) ⊆
        T.filter (fun e => v ∈ e) ∪
          (((edges H\T)\P.biUnion triEdges).filter (fun e => v ∈ e)) := by
      intro e he
      obtain ⟨he,hv⟩ := mem_filter.mp he
      by_cases ht : e ∈ T
      · exact mem_union_left _ (mem_filter.mpr ⟨ht,hv⟩)
      · exact mem_union_right _ (mem_filter.mpr
          ⟨mem_sdiff.mpr ⟨mem_sdiff.mpr ⟨(mem_sdiff.mp he).1,ht⟩,(mem_sdiff.mp he).2⟩,hv⟩)
    have hc : (((edges H\cover P).filter (fun e => v ∈ e)).card:ℝ) ≤
        SparseEdge.degIn T v +
          ((((edges H\T)\P.biUnion triEdges).filter (fun e => v ∈ e)).card:ℝ) := by
      exact_mod_cast (card_le_card hsub).trans (card_union_le _ _)
    have hd : (SparseEdge.degIn T v:ℝ) ≤ (α/8)*Fintype.card V :=
      (show (SparseEdge.degIn T v:ℝ) ≤ dT by exact_mod_cast hTd v).trans
        (hTs.trans (mul_le_mul_of_nonneg_right (min_le_right _ _) (by positivity)))
    have hu := hUd v
    have hηa : η ≤ α/8 := min_le_left _ _
    nlinarith [mul_le_mul_of_nonneg_right hηa (show (0:ℝ) ≤ Fintype.card V by positivity)]
  let τ := {uv : V × V // H.G.Adj uv.1 uv.2}
  let u : τ → V := fun t => t.val.1
  let v : τ → V := fun t => t.val.2
  have hcount : Fintype.card τ ≤ Fintype.card V^2 := by
    calc
      Fintype.card τ ≤ Fintype.card (V×V) := Fintype.card_subtype_le _
      _ = _ := by rw [Fintype.card_prod]; ring
  have hSupply : ∀ t : τ, α/2*Fintype.card V ≤ (good H F P (u t) (v t)).card := by
    intro t
    obtain ⟨a,ha⟩ := edge_allowed_of_seed (by linarith : 0 < C) hseed t.property
    have hh := good_supply h3 P hMiss ha
    dsimp only [u,v]
    nlinarith only [hh]
  obtain ⟨D,hDP,hD,hsmall,hgood⟩ := hS V I H F P hPack ((le_max_right _ _).trans hn)
    τ u v hcount hSupply
  refine ⟨D,hD,?_,?_,?_⟩
  · apply hPT.mono_left
    intro e he
    obtain ⟨A,hA,heA⟩ := mem_biUnion.mp he
    exact mem_biUnion.mpr ⟨A,hDP hA,heA⟩
  · intro x
    have hx := hsmall x
    have hqρ : q ≤ ρ/12 := min_le_left _ _
    change (((cover D).filter (fun e => x ∈ e)).card:ℝ) < ρ*Fintype.card V
    nlinarith [mul_le_mul_of_nonneg_right hqρ (show (0:ℝ) ≤ Fintype.card V by positivity)]
  · intro x y hxy
    have hh := hgood ⟨(x,y),hxy⟩
    dsimp only [u,v] at hh
    nlinarith only [hh]
end TypedTriangle.BasalIncidence
