module
public import RequestProject.TypedTriangle.PreparedAbsorberSupply
public import RequestProject.TypedTriangle.RestrictedQuotientTransport
public import RequestProject.TypedTriangle.ExplicitNativeUniformCert
set_option maxHeartbeats 4000000 -- build option (original: -DmaxHeartbeats=1600000; raised)
set_option maxRecDepth 16384 -- build option (original: -DmaxRecDepth=8192; raised)
@[expose] public section
open Finset Classical
noncomputable section
set_option autoImplicit false
namespace TypedTriangle.Pasch
open Incidence
variable {V I : Type*} [Fintype V]

/-! Only the integer certificate is lifted. A previous Pasch family remains on
the original carrier; no restriction of that family is used here. -/

theorem lift_surviving_coefficient_certificate (H : Host V I) (F : Set (Multiset I))
    (Bad : Finset V) (S : Finset (Finset (Survivors Bad)))
    (hS : ∀ T ∈ S, IsAllowed (restrictedHost H Bad) F T)
    (c : Finset (Survivors Bad) → ℤ) (x : Sym2 (Survivors Bad) → ℤ)
    (hcert : ∀ e, x e = ∑ T ∈ S, c T * ind (triEdges T) e) :
    ∃ (S' : Finset (Finset V)) (c' : Finset V → ℤ),
      (∀ T ∈ S', IsAllowed H F T ∧ Disjoint T Bad) ∧
      (∀ e, edgeZeroExtend Bad x e = ∑ T ∈ S', c' T * ind (triEdges T) e) ∧
      (∑ T ∈ S', (c' T).natAbs) = ∑ T ∈ S, (c T).natAbs := by
  let S' := S.image (liftVertexSet Bad)
  let c' : Finset V → ℤ := fun T => c (T.subtype (fun v => v ∉ Bad))
  have hc' (T : Finset (Survivors Bad)) : c' (liftVertexSet Bad T) = c T := by
    dsimp only [c']
    rw [subtype_liftVertexSet]
  refine ⟨S', c', ?_, ?_, ?_⟩
  · intro T hT
    obtain ⟨U, hUS, rfl⟩ := mem_image.mp
      (show T ∈ S.image (liftVertexSet Bad) from hT)
    exact (isAllowed_vertexDeleted_iff H F Bad _).mp
      ((isAllowed_liftVertexSet_iff H F Bad U).mp (hS U hUS))
  · have hx : x = ∑ T ∈ S, c T • ind (triEdges T) := by
      funext e
      simpa only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul] using hcert e
    intro e
    rw [hx, map_sum]
    change (∑ T ∈ S, edgeZeroExtend Bad (c T • ind (triEdges T))) e = _
    simp only [map_smul, edgeZeroExtend_triangle_boundary, Finset.sum_apply,
      Pi.smul_apply, smul_eq_mul]
    dsimp only [S']
    rw [sum_image (fun T _ U _ hTU => liftVertexSet_injective Bad hTU)]
    exact sum_congr rfl (fun T _ => by rw [hc'])
  · dsimp only [S']
    rw [sum_image (fun T _ U _ hTU => liftVertexSet_injective Bad hTU)]
    exact sum_congr rfl (fun T _ => by rw [hc'])

/-- A certificate on the actual surviving subtype gives ambient coefficients
avoiding the deleted set, with the same uniform cost. Geometry is not asserted
on the ambient host with isolated vertices. -/
theorem surviving_uniformCert_coefficients (H : Host V I) (F : Set (Multiset I))
    (Bad : Finset V) (K : ℕ) (hU : UniformCert (restrictedHost H Bad) F K)
    (P : Finset (Sym2 V)) (hP : IsPhysical (vertexDeleted H Bad) F P) :
    ∃ (S : Finset (Finset V)) (c : Finset V → ℤ),
      (∀ T ∈ S, IsAllowed H F T ∧ Disjoint T Bad) ∧
      (∀ e, ind P e = ∑ T ∈ S, c T * ind (triEdges T) e) ∧
      (∑ T ∈ S, (c T).natAbs) ≤ K * P.card := by
  let x := edgeRestrict Bad (ind P)
  have hx : x ∈ lattice (restrictedHost H Bad) F :=
    edgeRestrict_mem_lattice H F Bad hP
  have hvanish : ∀ e, TouchZ Bad e → ind P e = 0 := by
    intro e he
    have hz := (lattice_le_localGroup (vertexDeleted H Bad) F hP).1
    apply hz e
    intro hedge
    obtain ⟨v, hv, hve⟩ := he
    exact ((edges_vertexDeleted_iff H Bad e).mp hedge).2 v hv hve
  have hzero : edgeZeroExtend Bad x = ind P :=
    edgeZeroExtend_restrict Bad (ind P) hvanish
  have hnorm : l1E x = (P.card : ℤ) := by
    rw [← l1E_edgeZeroExtend Bad x, hzero, l1E_ind]
  obtain ⟨c, hc, hcc⟩ := hU x hx
  let S := allowed (restrictedHost H Bad) F
  have hS : ∀ T ∈ S, IsAllowed (restrictedHost H Bad) F T :=
    fun T hT => (mem_filter.mp hT).2
  have hcert : ∀ e, x e = ∑ T ∈ S, c T * ind (triEdges T) e := by
    intro e
    rw [← hc]
    change (∑ T ∈ allowed (restrictedHost H Bad) F, c T • ind (triEdges T)) e = _
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    rfl
  obtain ⟨S', c', hS', hcert', hnorm'⟩ :=
    lift_surviving_coefficient_certificate H F Bad S hS c x hcert
  refine ⟨S', c', hS', ?_, ?_⟩
  · intro e
    rw [← hzero]
    exact hcert' e
  · rw [hnorm']
    have hsub : ∑ T ∈ S, |c T| ≤ ∑ T, |c T| :=
      sum_le_sum_of_subset_of_nonneg (subset_univ _) (fun _ _ _ => abs_nonneg _)
    have hcast : ((∑ T ∈ S, (c T).natAbs : ℕ) : ℤ) = ∑ T ∈ S, |c T| := by simp
    have hbound : ((∑ T ∈ S, (c T).natAbs : ℕ) : ℤ) ≤ ((K * P.card : ℕ) : ℤ) := by
      rw [hcast]
      rw [hnorm] at hcc
      push_cast
      exact hsub.trans hcc
    exact_mod_cast hbound

theorem surviving_coefficients_of_H3H4_explicit
    {V I : Type} [Fintype V] (H : Host V I) (F : Set (Multiset I))
    (Bad : Finset V) (α : ℝ) (h : ℕ) (hα : 0 < α)
    (hn : ExplicitSample.compressionOrder α h ≤ Fintype.card (Survivors Bad))
    (h3 : CommonNbrCond (restrictedHost H Bad) F α)
    (h4 : HingeCond (restrictedHost H Bad) F α h)
    (P : Finset (Sym2 V)) (hP : IsPhysical (vertexDeleted H Bad) F P) :
    ∃ (S : Finset (Finset V)) (c : Finset V → ℤ),
      (∀ T ∈ S, IsAllowed H F T ∧ Disjoint T Bad) ∧
      (∀ e, ind P e = ∑ T ∈ S, c T * ind (triEdges T) e) ∧
      (∑ T ∈ S, (c T).natAbs) ≤ ExplicitCertificate.uniformCertCost α h * P.card := by
  exact surviving_uniformCert_coefficients H F Bad _
    (ExplicitCertificate.uniformCert_of_H3H4_explicit α h hα
      (restrictedHost H Bad) F hn h3 h4) P hP

#print axioms lift_surviving_coefficient_certificate
#print axioms surviving_uniformCert_coefficients
#print axioms surviving_coefficients_of_H3H4_explicit
end TypedTriangle.Pasch
