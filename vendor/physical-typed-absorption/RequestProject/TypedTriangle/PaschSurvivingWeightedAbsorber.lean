module
public import RequestProject.TypedTriangle.PaschSurvivingCertificateLift
public import RequestProject.TypedTriangle.PaschVertexAvoidingSlotAbsorber
set_option maxHeartbeats 4000000 -- build option (original: -DmaxHeartbeats=1600000; raised)
set_option maxRecDepth 16384 -- build option (original: -DmaxRecDepth=8192; raised)
@[expose] public section
open Finset Classical
noncomputable section
set_option autoImplicit false
namespace TypedTriangle.Pasch
variable {V I : Type*} [Fintype V]

/-! The certificate lives on the surviving subtype. The absorber and its
potential are constructed on the original host with the original previous
Pasch family. The saturated set occurs only in the geometric windows. -/

theorem surviving_certificate_weighted_absorber {H : Host V I} {F : Set (Multiset I)}
    {α : ℝ} {h K : ℕ} (hα : 0 < α) (hH3 : CommonNbrCond H F α)
    (hH4 : HingeCond H F α h) (Bad : Finset V)
    (hcert : UniformCert (restrictedHost H Bad) F K)
    (R : Finset (Finset V)) (L : ℕ) (hL : PairCodegreeBound R L)
    (B : Finset (Sym2 V)) (d : ℕ) (hdeg : ∀ x, degIn B x ≤ d)
    (P : Finset (Sym2 V)) (hP : IsPhysical (vertexDeleted H Bad) F P)
    (Z : Finset V) (hZBad : Disjoint Z Bad) (hPZ : Inside Z P) (Ub : ℕ)
    (hUb : Z.card + 3*(K*P.card) + K*P.card*(2*h-2) +
      3*(K*P.card)*(2*h-3) ≤ Ub)
    (hwin1 : (Ub:ℝ) + Bad.card + 3 + 4*d ≤ α/2*Fintype.card V)
    (hwin2 : ((Ub:ℝ) + Bad.card + 1 + h + 5*d)*2^h.choose 2 ≤ α/2*Fintype.card V) :
    ∃ (A : Finset (Sym2 V)) (U : Finset V), IsAbsorber H F A P ∧ Disjoint A B ∧
      Z ⊆ U ∧ U.card ≤ Z.card + 3*(K*P.card) ∧ Inside U P ∧ Fresh U A ∧
      A.card ≤ K*P.card*(4*(2*h-2).choose 2+6) ∧ (U ∪ support A).card ≤ Ub ∧
      (supportIncrementCost R U (support A):ℝ) ≤
        ((K*P.card:ℕ):ℝ)*absorptionPotentialCost α h Ub L ∧
      Disjoint U Bad ∧ Disjoint (support A) Bad := by
  obtain ⟨S, c, hS, hPc, hK⟩ := surviving_uniformCert_coefficients H F Bad K hcert P hP
  have hVerts : ((S.filter (fun T => c T ≠ 0)).biUnion id).card ≤ 3*(K*P.card) := by
    refine card_biUnion_le.trans ?_
    calc ∑ T ∈ S.filter (fun T => c T ≠ 0), (id T).card =
          ∑ _T ∈ S.filter (fun T => c T ≠ 0), 3 :=
        sum_congr rfl (fun T hT => (hS T (mem_filter.mp hT).1).1.1)
      _ = 3*(S.filter (fun T => c T ≠ 0)).card := by
        rw [sum_const, smul_eq_mul, mul_comm]
      _ ≤ 3*∑ T ∈ S, (c T).natAbs := by
        apply Nat.mul_le_mul_left
        rw [card_eq_sum_ones, sum_filter]
        exact sum_le_sum (fun T _ => by
          split_ifs with hT
          · exact Int.natAbs_pos.mpr hT
          · exact Nat.zero_le _)
      _ ≤ 3*(K*P.card) := Nat.mul_le_mul_left 3 hK
  let U := Z ∪ (S.filter (fun T => c T ≠ 0)).biUnion id
  have hZU : Z ⊆ U := subset_union_left
  have hUc : U.card ≤ Z.card + 3*(K*P.card) :=
    (card_union_le _ _).trans (Nat.add_le_add_left hVerts Z.card)
  have hUBad : Disjoint U Bad := by
    apply disjoint_union_left.mpr
    refine ⟨hZBad, ?_⟩
    rw [disjoint_left]
    intro v hv hvBad
    obtain ⟨T, hT, hvT⟩ := mem_biUnion.mp hv
    exact disjoint_left.mp (hS T (mem_filter.mp hT).1).2 hvT hvBad
  have hUb' : U.card + (K*P.card)*(2*h-2) + 3*(K*P.card)*(2*h-3) ≤ Ub := by omega
  obtain ⟨A, hA, hAB, hFresh, hSupport, hCard, hPay, hAvoid⟩ :=
    slot_absorber_of_coeffs_avoiding_vertices_with_support_budget hα hH3 hH4
      R L hL Bad B d hdeg P S (fun T hT => (hS T hT).1) c
      (fun T hT _ => (hS T hT).2) hPc (K*P.card) hK Z hZBad hPZ Ub hUb' hwin1 hwin2
  exact ⟨A, U, hA, hAB, hZU, hUc, hPZ.mono hZU, hFresh, hCard,
    hSupport.trans hUb', hPay, hUBad, hAvoid⟩

#print axioms surviving_certificate_weighted_absorber
end TypedTriangle.Pasch
