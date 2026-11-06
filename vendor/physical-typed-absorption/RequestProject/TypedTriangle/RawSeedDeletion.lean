/-
Copyright (c) 2026 Juan Pablo Traverso Gianini.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module
public import RequestProject.TypedTriangle.SeedPersistence
public import RequestProject.TypedTriangle.CoverDown
public import RequestProject.TypedTriangle.PhysicalResidual
set_option maxHeartbeats 4000000 -- build option (original: -DmaxHeartbeats=1600000; raised)
set_option maxRecDepth 16384 -- build option (original: -DmaxRecDepth=8192; raised)
@[expose] public section
open Finset Classical
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace TypedTriangle.RawReference
variable {V I : Type*} [Fintype V]

/-- At an intact edge, deleting maximum degree d destroys at most 2d allowed
triangles. No divisibility or basal structure of the deletion is required. -/
theorem lost_triangles {H : Host V I} {F : Set (Multiset I)}
    (B : Finset (Sym2 V)) (d : ℕ) (hd : ∀ v, degIn B v ≤ d)
    {e : Sym2 V} (he : e ∈ edges H) (heB : e ∉ B) :
    (triOn H F e \ triOn (residual H B) F e).card ≤ 2*d := by
  have hnd : ¬ e.IsDiag := H.G.not_isDiag_of_mem_edgeSet (by simpa [edges] using he)
  induction e using Sym2.ind with
  | _ x y =>
    have hsub : triOn H F s(x,y) \ triOn (residual H B) F s(x,y) ⊆
        (nbrIn B x ∪ nbrIn B y).image (fun w => insert w (s(x,y)).toFinset) := by
      intro T hT
      obtain ⟨hT,hTnot⟩ := mem_sdiff.mp hT
      obtain ⟨hTA,heT⟩ := mem_filter.mp hT
      have hAllow := isAllowed_of_mem_allowed hTA
      obtain ⟨w,hw⟩ := eq_insert_of_mem_triEdges hAllow.1 heT
      have hwout : w ∉ s(x,y) := by
        intro hwmem
        have hh : T = (s(x,y)).toFinset := by
          rw [hw]; exact insert_eq_of_mem (Sym2.mem_toFinset.mpr hwmem)
        have hc := hAllow.1
        rw [hh,Sym2.card_toFinset_of_not_isDiag _ hnd] at hc
        omega
      refine mem_image.mpr ⟨w,?_,hw.symm⟩
      by_contra hnot
      have hnot' : s(x,w) ∉ B ∧ s(y,w) ∉ B := by
        simpa only [mem_union,nbrIn,mem_filter,mem_univ,true_and,not_or] using hnot
      apply hTnot
      refine mem_filter.mpr ⟨?_,heT⟩
      apply (show IsAllowed (residual H B) F T → T ∈ allowed (residual H B) F by
        intro hh; simpa [allowed] using hh)
      apply isAllowed_subHost_of hAllow
      intro f hf
      refine mem_sdiff.mpr ⟨triEdges_subset_edges hAllow hf,?_⟩
      rw [hw] at hf
      rcases (mem_triEdges_insert hnd hwout).mp hf with rfl | ⟨z,hz,rfl⟩
      · exact heB
      · rcases Sym2.mem_iff.mp hz with rfl | rfl
        · exact hnot'.1
        · exact hnot'.2
    calc
      _ ≤ (nbrIn B x ∪ nbrIn B y).card := (card_le_card hsub).trans card_image_le
      _ ≤ (nbrIn B x).card + (nbrIn B y).card := card_union_le _ _
      _ ≤ 2*d := by
        have hx := (card_nbrIn_le B x).trans (hd x)
        have hy := (card_nbrIn_le B y).trans (hd y)
        omega

/-- Restriction of a raw approximate seed pays only the arbitrary forbidden
deletion. The basal stock is treated separately by seed transport. -/
theorem load_after_deletion {H : Host V I} {F : Set (Multiset I)}
    (μ : Finset V → ℝ) (B : Finset (Sym2 V)) (d : ℕ) (b ε : ℝ)
    (hn : 0 < (Fintype.card V:ℝ)) (hb : 0 ≤ b)
    (hμ : ∀ T, IsAllowed H F T → 0 ≤ μ T ∧ μ T ≤ b/Fintype.card V)
    (hd : ∀ v, degIn B v ≤ d)
    (hload : ∀ e ∈ edges H, |bdry H F μ e-1| ≤ ε) :
    ∀ e ∈ edges (residual H B),
      |bdry (residual H B) F μ e-1| ≤ ε+2*b*d/Fintype.card V := by
  intro e he
  have he' : e ∈ edges H ∧ e ∉ B := by
    rwa [residual,Residual.edges_subHost_eq sdiff_subset,mem_sdiff] at he
  have hsub : triOn (residual H B) F e ⊆ triOn H F e := by
    intro T hT
    obtain ⟨hT,heT⟩ := mem_filter.mp hT
    exact mem_filter.mpr ⟨by
      apply (show IsAllowed H F T → T ∈ allowed H F by intro hh; simpa [allowed] using hh)
      exact isAllowed_mono (subHost_le H _) rfl (isAllowed_of_mem_allowed hT),heT⟩
  let A := triOn H F e \ triOn (residual H B) F e
  have hA : A.card ≤ 2*d := lost_triangles B d hd he'.1 he'.2
  have hz : (0:ℝ) ≤ ∑ T ∈ A, μ T := sum_nonneg fun T hT =>
    (hμ T (isAllowed_of_mem_allowed (mem_filter.mp (mem_sdiff.mp hT).1).1)).1
  have hmass : ∑ T ∈ A, μ T ≤ 2*b*d/Fintype.card V := by
    calc
      _ ≤ ∑ _T ∈ A, b/Fintype.card V := sum_le_sum fun T hT =>
        (hμ T (isAllowed_of_mem_allowed (mem_filter.mp (mem_sdiff.mp hT).1).1)).2
      _ = (A.card:ℝ)*(b/Fintype.card V) := by rw [sum_const,nsmul_eq_mul]
      _ ≤ (2*d:ℝ)*(b/Fintype.card V) :=
        mul_le_mul_of_nonneg_right (by exact_mod_cast hA) (by positivity)
      _ = _ := by ring
  have heq : (∑ T ∈ A, μ T) + bdry (residual H B) F μ e = bdry H F μ e := by
    simpa only [bdry_eq_sum_triOn,A] using (sum_sdiff hsub (f:=μ))
  have hh := abs_le.mp (hload e he'.1)
  rw [abs_le]
  constructor <;> linarith

end TypedTriangle.RawReference
