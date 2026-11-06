/-
Copyright (c) 2026 Juan Pablo Traverso Gianini.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module
public import RequestProject.TypedTriangle.SeedPersistence
public import RequestProject.TypedTriangle.SeedMoment
public import RequestProject.TypedTriangle.PhysicalResidual
set_option maxHeartbeats 4000000 -- build option (original: -DmaxHeartbeats=1600000; raised)
set_option maxRecDepth 16384 -- build option (original: -DmaxRecDepth=8192; raised)
@[expose] public section
open Finset Classical
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace TypedTriangle.TriangleMonitors
variable {V I : Type*} [Fintype V]

theorem edge_card_le_of_degree_bound (B : Finset (Sym2 V)) (δ : ℝ)
    (hdeg : ∀ x, (degIn B x:ℝ) ≤ δ*Fintype.card V) :
    (B.card:ℝ) ≤ δ*(Fintype.card V:ℝ)^2 := by
  have h₁ : (B.card:ℝ) ≤ ∑ x : V, (degIn B x:ℝ) := by
    exact_mod_cast card_le_sum_degIn B
  have h₂ := sum_le_sum (fun x (_ : x ∈ (univ : Finset V)) => hdeg x)
  have hsum : (∑ _x : V, δ*(Fintype.card V:ℝ)) = δ*(Fintype.card V:ℝ)^2 := by
    simp [pow_two]; ring
  exact h₁.trans (hsum ▸ h₂)

/-- The complement in the original host is the reserve plus the nibble
complement. This uses the same P₀, without replacing its packing witness. -/
theorem original_complement_degree {H : Host V I}
    (B : Finset (Sym2 V)) (P₀ : Finset (Finset V)) (δ η : ℝ)
    (hB : ∀ x, (degIn B x:ℝ) ≤ δ*Fintype.card V)
    (hP : ∀ x, (degIn (edges (residual H B)\P₀.biUnion triEdges) x:ℝ) ≤ η*Fintype.card V) :
    ∀ x, (degIn (edges H\P₀.biUnion triEdges) x:ℝ) ≤ (η+δ)*Fintype.card V := by
  intro x
  have hJ : edges (residual H B) = edges H\B := Residual.edges_subHost_eq sdiff_subset
  have hSub : edges H\P₀.biUnion triEdges ⊆ B∪(edges (residual H B)\P₀.biUnion triEdges) := by
    intro e he
    by_cases heB : e ∈ B
    · exact mem_union_left _ heB
    · exact mem_union_right _ (mem_sdiff.mpr ⟨by rw [hJ]; exact mem_sdiff.mpr ⟨(mem_sdiff.mp he).1,heB⟩,
        (mem_sdiff.mp he).2⟩)
  have h₁ := card_le_card (filter_subset_filter (p := fun e => x ∈ e) hSub)
  have h₂ := card_union_le (B.filter (fun e => x ∈ e))
    ((edges (residual H B)\P₀.biUnion triEdges).filter (fun e => x ∈ e))
  rw [filter_union] at h₁
  have hh : (degIn (edges H\P₀.biUnion triEdges) x:ℝ) ≤
      (degIn B x:ℝ)+(degIn (edges (residual H B)\P₀.biUnion triEdges) x:ℝ) := by
    exact_mod_cast h₁.trans h₂
  nlinarith only [hh,hB x,hP x]

/-- Exact edge loads charge every removed triangle to an edge of B.
No pseudorandomness or bound on the number of triangles through an edge is needed. -/
theorem removed_seed_mass_le {H : Host V I} {F : Set (Multiset I)}
    {C : ℝ} {φ : Finset V → ℝ} (hC : 0 < C) (hφ : IsDiffuseSeed H F C φ)
    (B : Finset (Sym2 V)) (hB : B ⊆ edges H) :
    (∑ T ∈ allowed H F\allowed (residual H B) F, φ T) ≤ (B.card:ℝ) := by
  have hφ0 : ∀ T ∈ allowed H F, 0 ≤ φ T := by
    intro T hT
    exact (by positivity : (0:ℝ) ≤ 1/(C*Fintype.card V)).trans
      (hφ.1 T (isAllowed_of_mem_allowed hT)).1
  let f : Finset V → ℝ := fun T => if T ∈ allowed H F then φ T else 0
  have hf0 : ∀ T, 0 ≤ f T := by
    intro T
    dsimp only [f]
    split_ifs with hT
    · exact hφ0 T hT
    · exact le_rfl
  have hSub : allowed H F\allowed (residual H B) F ⊆ B.biUnion (triOn H F) := by
    intro T hT
    obtain ⟨hTH,hTJ⟩ := mem_sdiff.mp hT
    have hAllow := isAllowed_of_mem_allowed hTH
    have hDis : ¬Disjoint (triEdges T) B := by
      intro hD
      apply hTJ
      apply mem_filter.mpr
      refine ⟨mem_univ _,isAllowed_subHost_of hAllow ?_⟩
      intro e he
      exact mem_sdiff.mpr ⟨triEdges_subset_edges hAllow he,
        fun heB => disjoint_left.mp hD he heB⟩
    obtain ⟨e,heT,heB⟩ := not_disjoint_iff.mp hDis
    exact mem_biUnion.mpr ⟨e,heB,mem_filter.mpr ⟨hTH,heT⟩⟩
  calc (∑ T ∈ allowed H F\allowed (residual H B) F, φ T) =
      ∑ T ∈ allowed H F\allowed (residual H B) F, f T := by
        apply sum_congr rfl
        intro T hT
        simp only [f,if_pos (mem_sdiff.mp hT).1]
    _ ≤ ∑ T ∈ B.biUnion (triOn H F), f T :=
      sum_le_sum_of_subset_of_nonneg hSub (fun T _ _ => hf0 T)
    _ ≤ ∑ e ∈ B, ∑ T ∈ triOn H F e, f T := sum_biUnion_le_of_nonneg _ _ _ hf0
    _ = ∑ e ∈ B, (1:ℝ) := by
      apply sum_congr rfl
      intro e he
      have hload := hφ.bdry_eq_one (mem_filter.mp (hB he)).2
      rw [bdry_eq_sum_triOn] at hload
      calc
        (∑ T ∈ triOn H F e, f T) = (∑ T ∈ triOn H F e, φ T) := by
          apply sum_congr rfl
          intro T hT
          simp only [f,if_pos (mem_filter.mp hT).1]
        _ = 1 := hload
    _ = _ := by simp

/-- A pointwise O(κ/n) seed perturbation has O(κ n²) effect on every
bounded triangle statistic. Removed triangle mass costs at most |B|. -/
theorem triangle_seed_statistic_comparison {H : Host V I} {F : Set (Multiset I)}
    {C : ℝ} {φ ψ : Finset V → ℝ} (hC : 0 < C) (hφ : IsDiffuseSeed H F C φ)
    (B : Finset (Sym2 V)) (hB : B ⊆ edges H) (κ : ℝ) (hκ : 0 ≤ κ)
    (hn : 0 < Fintype.card V)
    (hClose : ∀ T, IsAllowed (residual H B) F T →
      |ψ T-φ T| ≤ κ/Fintype.card V)
    (w : Finset V → ℝ) (hw : ∀ T, IsAllowed H F T → |w T| ≤ 1) :
    |(∑ T ∈ allowed (residual H B) F, ψ T*w T)-
      (∑ T ∈ allowed H F, φ T*w T)| ≤ κ*(Fintype.card V:ℝ)^2+B.card := by
  let A := allowed H F
  let S := allowed (residual H B) F
  have hnR : (0:ℝ) < Fintype.card V := by exact_mod_cast hn
  have hSA : S ⊆ A := fun T hT => mem_filter.mpr ⟨mem_univ _,
    (residual_allowed (isAllowed_of_mem_allowed hT)).1⟩
  have hφ0 : ∀ T ∈ A, 0 ≤ φ T := by
    intro T hT
    exact (by positivity : (0:ℝ) ≤ 1/(C*Fintype.card V)).trans
      (hφ.1 T (isAllowed_of_mem_allowed hT)).1
  have hDifference : |∑ T ∈ S, (ψ T-φ T)*w T| ≤ κ*(Fintype.card V:ℝ)^2 := by
    have hCount : (S.card:ℝ) ≤ (Fintype.card V:ℝ)^3 := by
      exact_mod_cast card_allowed_le (residual H B) F
    calc |∑ T ∈ S, (ψ T-φ T)*w T| ≤ ∑ T ∈ S, |(ψ T-φ T)*w T| := abs_sum_le_sum_abs _ _
      _ ≤ ∑ _T ∈ S, κ/Fintype.card V := by
        apply sum_le_sum
        intro T hT
        rw [abs_mul]
        have hc := hClose T (isAllowed_of_mem_allowed hT)
        have hwT := hw T (isAllowed_of_mem_allowed (hSA hT))
        calc
          |ψ T-φ T| * |w T| ≤ |ψ T-φ T| * 1 := mul_le_mul_of_nonneg_left hwT (abs_nonneg _)
          _ ≤ κ/Fintype.card V := by simpa only [mul_one] using hc
      _ = (S.card:ℝ)*(κ/Fintype.card V) := by simp
      _ ≤ (Fintype.card V:ℝ)^3*(κ/Fintype.card V) :=
        mul_le_mul_of_nonneg_right hCount (div_nonneg hκ hnR.le)
      _ = κ*(Fintype.card V:ℝ)^2 := by field_simp
  have hRemoved : |∑ T ∈ A\S, φ T*w T| ≤ (B.card:ℝ) := by
    calc |∑ T ∈ A\S, φ T*w T| ≤ ∑ T ∈ A\S, |φ T*w T| := abs_sum_le_sum_abs _ _
      _ ≤ ∑ T ∈ A\S, φ T := by
        apply sum_le_sum
        intro T hT
        have hTA := (mem_sdiff.mp hT).1
        rw [abs_mul,abs_of_nonneg (hφ0 T hTA)]
        simpa only [mul_one] using mul_le_mul_of_nonneg_left
          (hw T (isAllowed_of_mem_allowed hTA)) (hφ0 T hTA)
      _ ≤ B.card := removed_seed_mass_le hC hφ B hB
  have hsplit := sum_sdiff hSA (f := fun T => φ T*w T)
  have heq : (∑ T ∈ S, ψ T*w T)-(∑ T ∈ A, φ T*w T) =
      (∑ T ∈ S, (ψ T-φ T)*w T)-(∑ T ∈ A\S, φ T*w T) := by
    simp_rw [sub_mul,sum_sub_distrib]
    linarith
  change |(∑ T ∈ S, ψ T*w T)-(∑ T ∈ A, φ T*w T)| ≤ _
  rw [heq]
  exact (abs_sub _ _).trans (add_le_add hDifference hRemoved)

#print axioms removed_seed_mass_le
#print axioms triangle_seed_statistic_comparison
end TypedTriangle.TriangleMonitors
