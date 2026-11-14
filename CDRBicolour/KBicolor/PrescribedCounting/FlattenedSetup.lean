/-
Copyright (c) 2026 Juan Pablo Traverso Gianini.
Released under Apache 2.0 license.
Authors: Juan Pablo Traverso Gianini
-/
module
public import CDRBicolour.KBicolor.PrescribedCounting.VariableCross
public import CDRBicolour.KBicolor.Wilson.SharpCounting

/-! # Flatten a placed Wilson group without changing its vertices or pairs -/
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace CDRBicolour.KBicolor.PrescribedCounting
open Finset Classical TypedTriangle
open CDRBicolour.KBicolor.Wilson
variable {A : Type*} [Fintype A] [DecidableEq A] {k n g t : ℕ}
variable {lab : Fin n → Fin k} {κ : A → Fin k}

abbrev groupOrder (A : Type*) [Fintype A] (t : ℕ) := Fintype.card (A × Fin t)
def groupEquiv (A : Type*) [Fintype A] (t : ℕ) : Fin (groupOrder A t) ≃ A × Fin t :=
  (Fintype.equivFin (A × Fin t)).symm
def groupLabels (κ : A → Fin k) (t : ℕ) : Fin (groupOrder A t) → Fin k :=
  fun a => κ (groupEquiv A t a).1
def groupEmbedding (h : Setup lab κ g t) : (Fin g × Fin (groupOrder A t)) ↪ Fin n where
  toFun p := h.embed (p.1,(groupEquiv A t p.2).1,(groupEquiv A t p.2).2)
  inj' := by
    intro p q he
    have hh := h.embed.injective he
    have hi : p.1=q.1 := congrArg (fun z : Fin g × A × Fin t => z.1) hh
    have hj : groupEquiv A t p.2=groupEquiv A t q.2 :=
      congrArg (fun z : Fin g × A × Fin t => z.2) hh
    exact Prod.ext hi ((groupEquiv A t).injective hj)

theorem groupEmbedding_label (h : Setup lab κ g t) (p : Fin g) (a : Fin (groupOrder A t)) :
    lab (groupEmbedding h (p,a))=groupLabels κ t a := h.label _ _ _

theorem groupOrder_eq : groupOrder A t=Fintype.card A*t := by
  simp only [groupOrder,Fintype.card_prod,Fintype.card_fin]

theorem groupLabels_size (X : Fin k) : Hilton.csize (groupLabels κ t) X=Hilton.csize κ X*t := by
  have he : {a : Fin (groupOrder A t) // groupLabels κ t a=X} ≃
      {p : A × Fin t // κ p.1=X} :=
    { toFun := fun a => ⟨groupEquiv A t a.1,a.2⟩
      invFun := fun p => ⟨(groupEquiv A t).symm p.1,by simpa only [groupLabels,Equiv.apply_symm_apply] using p.2⟩
      left_inv := fun a => Subtype.ext (Equiv.symm_apply_apply _ a.1)
      right_inv := fun p => Subtype.ext (Equiv.apply_symm_apply _ p.1) }
  have he' : {p : A × Fin t // κ p.1=X} ≃ {a : A // κ a=X} × Fin t :=
    { toFun := fun p => (⟨p.1.1,p.2⟩,p.1.2)
      invFun := fun p => ⟨(p.1.1,p.2),p.1.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  calc
    _ = Fintype.card {p : A × Fin t // κ p.1=X} := Fintype.card_congr he
    _ = Fintype.card ({a : A // κ a=X} × Fin t) := Fintype.card_congr he'
    _ = _ := by rw [Fintype.card_prod,Fintype.card_fin]

theorem flattened_cross_edges (h : Setup lab κ g t) {S : Finset (Finset (Fin g))}
    (hS : _root_.STS.IsSTS S) (Λ : VariableCross.Family S (groupOrder A t)) (Λ₀ : LFam A S t) :
    (VariableCross.packing (groupEmbedding h) Λ).biUnion triEdges=(crossP h Λ₀).biUnion triEdges := by
  ext f
  induction f using Sym2.ind with
  | _ u v =>
    rw [VariableCross.mem_edges _ hS,mem_crossEdges h hS]
    constructor
    · rintro ⟨p,q,a,b,hpq,rfl,rfl⟩
      exact ⟨p,q,(groupEquiv A t a).1,(groupEquiv A t b).1,
        (groupEquiv A t a).2,(groupEquiv A t b).2,hpq,rfl,rfl⟩
    · rintro ⟨p,q,P,Q,a,b,hpq,rfl,rfl⟩
      refine ⟨p,q,(groupEquiv A t).symm (P,a),(groupEquiv A t).symm (Q,b),hpq,?_,?_⟩
      · change h.embed (p,P,a)=h.embed (p,(groupEquiv A t ((groupEquiv A t).symm (P,a))).1,
          (groupEquiv A t ((groupEquiv A t).symm (P,a))).2)
        rw [Equiv.apply_symm_apply]
      · change h.embed (q,Q,b)=h.embed (q,(groupEquiv A t ((groupEquiv A t).symm (Q,b))).1,
          (groupEquiv A t ((groupEquiv A t).symm (Q,b))).2)
        rw [Equiv.apply_symm_apply]

def referenceTable (h : Setup lab κ g t) (l : Fin t → Fin t → Fin t) :
    Fin (groupOrder A t) → Fin (groupOrder A t) → Fin (groupOrder A t) := fun a b =>
  (groupEquiv A t).symm (h.tau (groupEquiv A t a).1 (groupEquiv A t b).1,
    l (groupEquiv A t a).2 (groupEquiv A t b).2)

theorem referenceTable_latin (h : Setup lab κ g t) (l : Fin t → Fin t → Fin t)
    (hl : _root_.STS.IsLatin l) : _root_.STS.IsLatin (referenceTable h l) := by
  constructor
  · intro a
    constructor
    · intro b c he
      have he' := (groupEquiv A t).symm.injective he
      have h1 := h.row _ (congrArg Prod.fst he')
      have h2 := (hl.1 _).1 (congrArg Prod.snd he')
      exact (groupEquiv A t).injective (Prod.ext h1 h2)
    · intro c
      obtain ⟨Q,hQ⟩ := h.row_surj (groupEquiv A t a).1 (groupEquiv A t c).1
      obtain ⟨b,hb⟩ := (hl.1 (groupEquiv A t a).2).2 (groupEquiv A t c).2
      refine ⟨(groupEquiv A t).symm (Q,b),?_⟩
      apply (groupEquiv A t).injective
      simp only [referenceTable,Equiv.apply_symm_apply,hQ,hb]
  · intro b
    constructor
    · intro a c he
      have he' := (groupEquiv A t).symm.injective he
      have h1 := h.col _ (congrArg Prod.fst he')
      have h2 := (hl.2 _).1 (congrArg Prod.snd he')
      exact (groupEquiv A t).injective (Prod.ext h1 h2)
    · intro c
      obtain ⟨P,hP⟩ := h.col_surj (groupEquiv A t b).1 (groupEquiv A t c).1
      obtain ⟨a,ha⟩ := (hl.2 (groupEquiv A t b).2).2 (groupEquiv A t c).2
      refine ⟨(groupEquiv A t).symm (P,a),?_⟩
      apply (groupEquiv A t).injective
      simp only [referenceTable,Equiv.apply_symm_apply,hP,ha]

theorem referenceTable_allowed (h : Setup lab κ g t) (l : Fin t → Fin t → Fin t)
    (a b : Fin (groupOrder A t)) :
    ({groupLabels κ t a,groupLabels κ t b,groupLabels κ t (referenceTable h l a b)} :
      Multiset (Fin k)) ∈ bicF k := by
  simpa only [groupLabels,referenceTable,Equiv.apply_symm_apply] using
    h.allowed (groupEquiv A t a).1 (groupEquiv A t b).1

end CDRBicolour.KBicolor.PrescribedCounting
