module
public import RequestProject.TypedTriangle.PaschTriangleFreeResidue
public import RequestProject.TypedTriangle.G1ZSplice
set_option maxHeartbeats 4000000 -- build option (original: -DmaxHeartbeats=1600000; raised)
set_option maxRecDepth 16384 -- build option (original: -DmaxRecDepth=8192; raised)
@[expose] public section
open Finset Classical
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1200000
namespace TypedTriangle.Pasch
variable {V I : Type*} [Fintype V]

/-- The existing slot construction already avoids every edge with both ends
in the root/certificate set. This sibling retains that genuine witness. -/
theorem fresh_slot_absorber_of_uniformCert {H : Host V I} {F : Set (Multiset I)}
    {α : ℝ} {h K : ℕ} (hα : 0 < α) (hH3 : CommonNbrCond H F α)
    (hH4 : HingeCond H F α h) (hcert : UniformCert H F K)
    (B : Finset (Sym2 V)) (d : ℕ) (hdeg : ∀ x, degIn B x ≤ d)
    (P : Finset (Sym2 V)) (hP : IsPhysical H F P) (Z : Finset V) (hPZ : Inside Z P) (Ub : ℕ)
    (hUb : Z.card+3*(K*P.card)+K*P.card*(2*h-2)+3*(K*P.card)*(2*h-3) ≤ Ub)
    (hwin1 : (Ub:ℝ)+3+4*d < α*Fintype.card V)
    (hwin2 : ((Ub:ℝ)+1+h+5*d)*2^h.choose 2 ≤ α/2*Fintype.card V) :
    ∃ (A : Finset (Sym2 V)) (U : Finset V), IsAbsorber H F A P ∧ Disjoint A B ∧
      Z ⊆ U ∧ U.card ≤ Z.card+3*(K*P.card) ∧ Inside U P ∧ Fresh U A ∧
        A.card ≤ K*P.card*(4*(2*h-2).choose 2+6) := by
  obtain ⟨c,hc,hcc⟩ := hcert (ind P) hP
  rw [l1E_ind] at hcc
  let S := allowed H F
  have hS : ∀ T ∈ S, IsAllowed H F T := fun T hT => (mem_filter.mp hT).2
  have hPc : ∀ e, ind P e = ∑ T ∈ S, c T*ind (triEdges T) e := by
    intro e
    rw [←hc]
    change (∑ T ∈ allowed H F, c T • ind (triEdges T)) e = _
    simp only [Finset.sum_apply,Pi.smul_apply,smul_eq_mul]
    rfl
  have hK : ∑ T ∈ S, (c T).natAbs ≤ K*P.card := by
    have h1 : ∑ T ∈ S, |c T| ≤ ∑ T, |c T| :=
      sum_le_sum_of_subset_of_nonneg (subset_univ _) (fun _ _ _ => abs_nonneg _)
    have h2 : ((∑ T ∈ S, (c T).natAbs : ℕ):ℤ) = ∑ T ∈ S, |c T| := by simp
    have h3 : ((∑ T ∈ S, (c T).natAbs : ℕ):ℤ) ≤ ((K*P.card:ℕ):ℤ) := by
      rw [h2]
      push_cast
      linarith only [h1,hcc]
    exact_mod_cast h3
  have hVerts : ((S.filter (fun T => c T ≠ 0)).biUnion id).card ≤ 3*(K*P.card) := by
    refine card_biUnion_le.trans ?_
    calc ∑ T ∈ S.filter (fun T => c T ≠ 0), (id T).card = ∑ _T ∈ S.filter (fun T => c T ≠ 0), 3 :=
        sum_congr rfl (fun T hT => (hS T (mem_filter.mp hT).1).1)
      _ = 3*(S.filter (fun T => c T ≠ 0)).card := by rw [sum_const,smul_eq_mul,mul_comm]
      _ ≤ 3*∑ T ∈ S, (c T).natAbs := by
        apply Nat.mul_le_mul_left
        rw [card_eq_sum_ones,sum_filter]
        exact sum_le_sum (fun T _ => by
          split_ifs with hT
          · exact Int.natAbs_pos.mpr hT
          · exact Nat.zero_le _)
      _ ≤ 3*(K*P.card) := Nat.mul_le_mul_left 3 hK
  let U := Z ∪ (S.filter (fun T => c T ≠ 0)).biUnion id
  have hZU : Z ⊆ U := subset_union_left
  have hUc : U.card ≤ Z.card+3*(K*P.card) :=
    (card_union_le _ _).trans (Nat.add_le_add_left hVerts Z.card)
  have hUb' : U.card+(K*P.card)*(2*h-2)+3*(K*P.card)*(2*h-3) ≤ Ub := by omega
  obtain ⟨A,hA,hAB,hFresh,_,hCard⟩ := slot_absorber_of_coeffs hα hH3 hH4 B d hdeg P S hS c hPc
    (K*P.card) hK Z hPZ Ub hUb' hwin1 hwin2
  exact ⟨A,U,hA,hAB,hZU,hUc,hPZ.mono hZU,hFresh,hCard⟩

theorem fresh_slot_absorber_modes {H : Host V I} {F : Set (Multiset I)}
    {A P : Finset (Sym2 V)} {U : Finset V}
    (hA : IsAbsorber H F A P) (hFresh : Fresh U A) (hFree : HasNoAllowedTriangle H F P) :
    ∀ T : Finset V, IsAllowed H F T → triEdges T ⊆ A∪P → ∃ v ∈ T, v ∉ U :=
  fun _ hT hSub => allowed_triangle_meets_outside_of_fresh hFresh hFree hT hSub

#print axioms fresh_slot_absorber_of_uniformCert
#print axioms fresh_slot_absorber_modes
end TypedTriangle.Pasch
