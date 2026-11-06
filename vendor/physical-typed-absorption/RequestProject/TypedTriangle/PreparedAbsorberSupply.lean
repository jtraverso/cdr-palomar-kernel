/-
Copyright (c) 2026 Juan Pablo Traverso Gianini.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module
public import RequestProject.TypedTriangle.CoreBasalPayment
public import RequestProject.TypedTriangle.PreparedCoreConstruction
public import RequestProject.TypedTriangle.SampleConstruct
@[expose] public section

/-! Derive vertex-avoiding single-piece absorbers from the prepared physical
core and G2. No absorber-supply premise is assumed. -/
open Finset Classical
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace TypedTriangle.PreparedSupply
open CorePayment Dispersal
variable {V I : Type*} [Fintype V]

lemma lift_pull_eq (Z : Finset V) (P : Finset (Sym2 V))
    (hP : ∀ e ∈ P, ∀ v ∈ e, v ∉ Z) : liftEdges Z (pullEdges Z P) = P := by
  apply le_antisymm
  · intro e he
    obtain ⟨f,hf,rfl⟩ := mem_image.mp he
    exact mem_preimage.mp hf
  · intro e he
    let f : Sym2 (Survivors Z) := e.attachWith (hP e he)
    have hf : edgeLift Z f = e := Sym2.attachWith_map_subtypeVal _
    exact mem_image.mpr ⟨f,mem_preimage.mpr (hf.symm ▸ he),hf⟩

lemma pull_ind (Z : Finset V) (P : Finset (Sym2 V)) :
    ind (pullEdges Z P) = edgeRestrict Z (ind P) := by
  funext e
  simp only [ind, pullEdges, mem_preimage]
  rfl

lemma support_pull_inside (Z : Finset V) (P : Finset (Sym2 V)) :
    Inside ((support P).subtype (fun v => v ∉ Z)) (pullEdges Z P) := by
  intro e he v hv
  apply mem_subtype.mpr
  apply mem_filter.mpr
  refine ⟨mem_univ _,edgeLift Z e,mem_preimage.mp he,?_⟩
  exact (mem_edgeLift Z e v).mpr hv

lemma absorber_lift {H : Host V I} {F : Set (Multiset I)} (Z : Finset V)
    {A : Finset (Sym2 (Survivors Z))} {P : Finset (Sym2 V)}
    (hP : ∀ e ∈ P, ∀ v ∈ e, v ∉ Z)
    (hA : IsAbsorber (restrictedHost H Z) F A (pullEdges Z P)) :
    IsAbsorber H F (liftEdges Z A) P := by
  have hp := lift_pull_eq Z P hP
  refine ⟨?_,basal_lift Z hA.2.1,?_⟩
  · rw [← hp]
    exact disjoint_left.mpr fun e he hf => by
      obtain ⟨a,ha,hae⟩ := mem_image.mp he
      obtain ⟨b,hb,hbe⟩ := mem_image.mp hf
      have hab := edgeLift_injective Z (hae.trans hbe.symm)
      exact disjoint_left.mp hA.1 ha (hab ▸ hb)
  · have hh := basal_lift Z hA.2.2
    have hh' : Basal H F (liftEdges Z A ∪ liftEdges Z (pullEdges Z P)) := by
      simpa only [liftEdges,image_union] using hh
    rw [hp] at hh'
    exact hh'

lemma prepared_physical_pull {H : Host V I} {F : Set (Multiset I)}
    {α β : ℝ} {h N : ℕ} (Pc : PreparedCore H.G H.lab F α h N β)
    (P : Finset (Sym2 V)) (hP : IsPhysical H F P) (Z : Finset V)
    (hZ : (Z.card:ℝ) ≤ β*Fintype.card V)
    (havoid : ∀ e ∈ P, ∀ v ∈ e, v ∉ Z) :
    IsPhysical (restrictedHost H Z) F (pullEdges Z P) := by
  have hz : ∀ e : Sym2 V, (∃ z ∈ Z, z ∈ e) → ind P e = 0 := by
    rintro e ⟨v,hv,hve⟩
    have he : e ∉ P := fun he => havoid e he v hve hv
    simp [ind,he]
  have hh := Pc.lattice_persist Z hZ (ind P) hP hz
  change ind (pullEdges Z P) ∈ lattice (restrictedHost H Z) F
  rw [pull_ind]
  change edgeRestrict Z (ind P) ∈
    SparseEdge.lattice (restrictedHost H Z).G (restrictedHost H Z).lab F
  rw [restrictedHost_G_eq_dispersal,restrictedHost_lab_eq_dispersal]
  exact hh

/-- A genuine vertex-avoiding G2 absorber in the prepared core. The two
resource inequalities are exactly those of G2 in the surviving host. -/
theorem prepared_absorber_window (α : ℝ) (h : ℕ) (hα : 0 < α) :
    ∃ K N : ℕ, ∀ {V I : Type} [Fintype V] (H : Host V I)
      (F : Set (Multiset I)) (β : ℝ),
      PreparedCore H.G H.lab F α h N β →
      ∀ (P : Finset (Sym2 V)), IsPhysical H F P →
      ∀ (Z : Finset V), (Z.card:ℝ) ≤ β*Fintype.card V →
      (∀ e ∈ P, ∀ v ∈ e, v ∉ Z) →
      ∀ (B : Finset (Sym2 V)) (d Ub : ℕ), (∀ v, degIn B v ≤ d) →
      (support P).card + 3*(K*P.card) + K*P.card*(2*h-2) +
        3*(K*P.card)*(2*h-3) ≤ Ub →
      (Ub:ℝ)+3+4*d < α*Fintype.card (Survivors Z) →
      ((Ub:ℝ)+1+h+5*d)*2^(Nat.choose h 2) ≤ α/2*Fintype.card (Survivors Z) →
      ∃ A, IsAbsorber H F A P ∧ Disjoint A B ∧
        A.card ≤ K*P.card*(4*(2*h-2).choose 2+6) ∧
        ∀ e ∈ A, ∀ v ∈ e, v ∉ Z := by
  obtain ⟨K,N,hG2⟩ := slot_absorber_of_H3H4 α h hα
  refine ⟨K,N,?_⟩
  intro V I _ H F β Pc P hP Z hZ hav B d Ub hBd hUb hw1 hw2
  have h3 : CommonNbrCond (restrictedHost H Z) F α := by
    change SparseEdge.CommonNbrCond (restrictedHost H Z).G (restrictedHost H Z).lab F α
    rw [restrictedHost_G_eq_dispersal,restrictedHost_lab_eq_dispersal]
    exact Pc.h3 Z hZ
  have h4 : HingeCond (restrictedHost H Z) F α h := by
    change SparseEdge.HingeCond (restrictedHost H Z).G (restrictedHost H Z).lab F α h
    rw [restrictedHost_G_eq_dispersal,restrictedHost_lab_eq_dispersal]
    exact Pc.h4 Z hZ
  have hsize : (pullEdges Z P).card ≤ P.card := by
    rw [pullEdges,card_preimage]
    exact card_filter_le _ _
  have hroot : ((support P).subtype (fun v => v ∉ Z)).card ≤ (support P).card := by
    rw [card_subtype]
    exact card_filter_le _ _
  have hb : ∀ v, degIn (pullEdges Z B) v ≤ d := by
    intro v
    have hh := degree_pull_le Z B v
    simp only [edeg_eq_classical] at hh
    have hh' : degIn (pullEdges Z B) v ≤ degIn B v.1 := by
      simpa only [degIn,SelSimul.edeg] using hh
    exact hh'.trans (hBd v.1)
  have hp := prepared_physical_pull Pc P hP Z hZ hav
  have hu : ((support P).subtype (fun v => v ∉ Z)).card +
      3*(K*(pullEdges Z P).card) + K*(pullEdges Z P).card*(2*h-2) +
      3*(K*(pullEdges Z P).card)*(2*h-3) ≤ Ub := by
    have hK := Nat.mul_le_mul_left K hsize
    have h1 := Nat.mul_le_mul_left 3 hK
    have h2 := Nat.mul_le_mul_right (2*h-2) hK
    have h3 := Nat.mul_le_mul_right (2*h-3) h1
    omega
  obtain ⟨A,hA,hAB,hcard⟩ := hG2 (restrictedHost H Z) F (Pc.order Z hZ) h3 h4
    (pullEdges Z B) d hb (pullEdges Z P) hp
    ((support P).subtype (fun v => v ∉ Z)) (support_pull_inside Z P) Ub hu hw1 hw2
  refine ⟨liftEdges Z A,absorber_lift Z hav hA,?_,?_,liftEdges_avoids Z A⟩
  · apply disjoint_left.mpr
    intro e he heB
    obtain ⟨f,hf,rfl⟩ := mem_image.mp he
    exact disjoint_left.mp hAB hf (mem_preimage.mpr heB)
  · exact card_image_le.trans (hcard.trans (Nat.mul_le_mul_right _ (Nat.mul_le_mul_left K hsize)))

end TypedTriangle.PreparedSupply
