/-
Copyright (c) 2026 Juan Pablo Traverso Gianini.
Released under Apache 2.0 license.
Authors: Juan Pablo Traverso Gianini
-/
module
public import CDRIIILib.KBicolor.Wilson.Assembly
public import CDRIIILib.KBicolor.PrescribedCounting.OutlineEntropy

/-! # Full Latin tables on Wilson group blocks

The symbol-class pattern can vary independently on every group block.
The embedding and the covered pairs are fixed throughout.
-/
@[expose] public section
noncomputable section
set_option autoImplicit false
namespace CDRBicolour.KBicolor.PrescribedCounting.VariableCross
open Finset Classical TypedTriangle
open CDRBicolour.Absorption.Count.Wilson (OT mem_OT tri3 grp3 grp3_inj mem_tri3 tri3_inj exists_sorted mem_tE)
variable {n g B k : ℕ} {S : Finset (Finset (Fin g))}

abbrev Block (S : Finset (Finset (Fin g))) := {o // o ∈ OT S}
abbrev Family (S : Finset (Finset (Fin g))) (B : ℕ) :=
  Block S → {L : Fin B → Fin B → Fin B // _root_.STS.IsLatin L}
abbrev Cell (S : Finset (Finset (Fin g))) (B : ℕ) := Block S × Fin B × Fin B

def grp (x : Cell S B) (i : Fin 3) : Fin g := grp3 x.1.1 i
def slot (Λ : Family S B) (x : Cell S B) (i : Fin 3) : Fin B :=
  ![x.2.1,x.2.2,(Λ x.1).1 x.2.1 x.2.2] i
def pos (e : (Fin g × Fin B) ↪ Fin n) (Λ : Family S B) (x : Cell S B) (i : Fin 3) : Fin n :=
  e (grp x i,slot Λ x i)
def triangle (e : (Fin g × Fin B) ↪ Fin n) (Λ : Family S B) (x : Cell S B) : Finset (Fin n) :=
  {pos e Λ x 0,pos e Λ x 1,pos e Λ x 2}
def packing (e : (Fin g × Fin B) ↪ Fin n) (Λ : Family S B) : Finset (Finset (Fin n)) :=
  univ.image (triangle e Λ)

theorem grp_inj (x : Cell S B) : Function.Injective (grp x) := by
  intro i j he
  exact grp3_inj (mem_OT.mp x.1.2).1 (mem_OT.mp x.1.2).2.1 he

theorem pos_ne (e : (Fin g × Fin B) ↪ Fin n) (Λ : Family S B) (x : Cell S B)
    {i j : Fin 3} (hij : i ≠ j) : pos e Λ x i ≠ pos e Λ x j := by
  intro he
  exact hij (grp_inj x (congrArg Prod.fst (e.injective he)))

theorem mem_triangle (e : (Fin g × Fin B) ↪ Fin n) (Λ : Family S B) (x : Cell S B)
    (v : Fin n) : v ∈ triangle e Λ x ↔ ∃ i, pos e Λ x i=v := by
  constructor
  · intro hv
    simp only [triangle,mem_insert,mem_singleton] at hv
    rcases hv with rfl | rfl | rfl
    · exact ⟨0,rfl⟩
    · exact ⟨1,rfl⟩
    · exact ⟨2,rfl⟩
  · rintro ⟨i,rfl⟩
    fin_cases i <;> simp [triangle]

theorem share_two (e : (Fin g × Fin B) ↪ Fin n) (hS : _root_.STS.IsSTS S)
    {Λ Λ' : Family S B} {x y : Cell S B} {i j l m : Fin 3} (hij : i ≠ j)
    (hi : pos e Λ x i=pos e Λ' y l) (hj : pos e Λ x j=pos e Λ' y m) :
    x.1=y.1 ∧ i=l ∧ j=m := by
  have h1 := congrArg Prod.fst (e.injective hi)
  have h2 := congrArg Prod.fst (e.injective hj)
  change grp x i=grp y l at h1
  change grp x j=grp y m at h2
  have hne : grp x i ≠ grp x j := fun he => hij (grp_inj x he)
  have hx : tri3 x.1.1 ∈ S := (mem_OT.mp x.1.2).2.2
  have hy : tri3 y.1.1 ∈ S := (mem_OT.mp y.1.2).2.2
  obtain ⟨T,-,hT⟩ := hS.2 _ _ hne
  have ex : tri3 x.1.1=T := hT _ ⟨hx,mem_tri3.mpr ⟨i,rfl⟩,mem_tri3.mpr ⟨j,rfl⟩⟩
  have ey : tri3 y.1.1=T := hT _ ⟨hy,mem_tri3.mpr ⟨l,h1.symm⟩,mem_tri3.mpr ⟨m,h2.symm⟩⟩
  have hxy := tri3_inj (mem_OT.mp x.1.2).1 (mem_OT.mp x.1.2).2.1
    (mem_OT.mp y.1.2).1 (mem_OT.mp y.1.2).2.1 (ex.trans ey.symm)
  refine ⟨Subtype.ext hxy,grp_inj x ?_,grp_inj x ?_⟩
  · rw [h1]; simp only [grp,hxy]
  · rw [h2]; simp only [grp,hxy]

theorem cell_eq_01 (e : (Fin g × Fin B) ↪ Fin n) {Λ Λ' : Family S B}
    {x y : Cell S B} (ho : x.1=y.1)
    (h0 : pos e Λ x 0=pos e Λ' y 0) (h1 : pos e Λ x 1=pos e Λ' y 1) : x=y := by
  have hrow := congrArg Prod.snd (e.injective h0)
  have hcol := congrArg Prod.snd (e.injective h1)
  exact Prod.ext ho (Prod.ext hrow hcol)

theorem cell_eq_two (e : (Fin g × Fin B) ↪ Fin n) {Λ : Family S B}
    {x y : Cell S B} (ho : x.1=y.1) {i j : Fin 3} (hij : i ≠ j)
    (hi : pos e Λ x i=pos e Λ y i) (hj : pos e Λ x j=pos e Λ y j) : x=y := by
  wlog hlt : i<j generalizing i j
  · exact this hij.symm hj hi (lt_of_le_of_ne (not_lt.mp hlt) hij.symm)
  have h1 := congrArg Prod.snd (e.injective hi)
  have h2 := congrArg Prod.snd (e.injective hj)
  obtain ⟨o,r,c⟩ := x
  obtain ⟨o',r',c'⟩ := y
  simp only at ho
  subst ho
  fin_cases i <;> fin_cases j <;> simp at hlt
  · exact Prod.ext rfl (Prod.ext h1 h2)
  · have hr : r=r' := h1
    subst hr
    exact Prod.ext rfl (Prod.ext rfl ((Λ o).2.1 r |>.1 h2))
  · have hc : c=c' := h1
    subst hc
    exact Prod.ext rfl (Prod.ext ((Λ o).2.2 c |>.1 h2) rfl)

theorem packing_disjoint (e : (Fin g × Fin B) ↪ Fin n) (hS : _root_.STS.IsSTS S)
    (Λ : Family S B) : (packing e Λ : Set (Finset (Fin n))).PairwiseDisjoint triEdges := by
  intro T hT U hU hne
  obtain ⟨x,-,rfl⟩ := mem_image.mp hT
  obtain ⟨y,-,rfl⟩ := mem_image.mp hU
  rw [Function.onFun,Finset.disjoint_left]
  intro f hf hf'
  induction f using Sym2.ind with
  | _ u v =>
    obtain ⟨hu,hv,huv⟩ := mem_tE.mp hf
    obtain ⟨hu',hv',-⟩ := mem_tE.mp hf'
    obtain ⟨i,rfl⟩ := (mem_triangle e Λ x u).mp hu
    obtain ⟨j,hj⟩ := (mem_triangle e Λ x v).mp hv
    obtain ⟨l,hl⟩ := (mem_triangle e Λ y _).mp hu'
    obtain ⟨m,hm⟩ := (mem_triangle e Λ y v).mp hv'
    have hij : i ≠ j := by rintro rfl; exact huv hj
    obtain ⟨ho,rfl,rfl⟩ := share_two e hS hij hl.symm (hj.trans hm.symm)
    exact hne (congrArg (triangle e Λ) (cell_eq_two e ho hij hl.symm (hj.trans hm.symm)))

theorem packing_injective (e : (Fin g × Fin B) ↪ Fin n) (hS : _root_.STS.IsSTS S) :
    Function.Injective (packing (S := S) e) := by
  intro Λ Λ' he
  funext o
  apply Subtype.ext
  funext r c
  let x : Cell S B := (o,r,c)
  have hx : triangle e Λ x ∈ packing e Λ' := by
    rw [← he]; exact mem_image.mpr ⟨x,mem_univ _,rfl⟩
  obtain ⟨y,-,hy⟩ := mem_image.mp hx
  have hp : ∀ i, ∃ j, pos e Λ' y j=pos e Λ x i := by
    intro i
    apply (mem_triangle e Λ' y _).mp
    rw [hy]
    exact (mem_triangle e Λ x _).mpr ⟨i,rfl⟩
  obtain ⟨i0,h0⟩ := hp 0
  obtain ⟨i1,h1⟩ := hp 1
  obtain ⟨i2,h2⟩ := hp 2
  obtain ⟨ho,rfl,rfl⟩ := share_two e hS (by decide : (0 : Fin 3) ≠ 1) h0.symm h1.symm
  have hxy := cell_eq_01 e ho h0.symm h1.symm
  obtain ⟨-,-,rfl⟩ := share_two e hS (by decide : (0 : Fin 3) ≠ 2) h0.symm h2.symm
  have hs := congrArg Prod.snd (e.injective h2)
  rw [← hxy] at hs
  exact hs.symm

theorem cover (e : (Fin g × Fin B) ↪ Fin n) (hS : _root_.STS.IsSTS S)
    (Λ : Family S B) {p q : Fin g} (hpq : p ≠ q) (a b : Fin B) :
    ∃ x : Cell S B, e (p,a) ∈ triangle e Λ x ∧ e (q,b) ∈ triangle e Λ x := by
  obtain ⟨T,⟨hT,hp,hq⟩,-⟩ := hS.2 _ _ hpq
  obtain ⟨u,v,w,huv,huw,hvw,rfl⟩ := card_eq_three.mp (hS.1 T hT)
  obtain ⟨o,ho1,ho2,hoT⟩ := exists_sorted huv huw hvw
  have hoS : o ∈ OT S := mem_OT.mpr ⟨ho1,ho2,hoT ▸ hT⟩
  obtain ⟨i,hi⟩ := mem_tri3.mp (hoT ▸ hp : p ∈ tri3 o)
  obtain ⟨j,hj⟩ := mem_tri3.mp (hoT ▸ hq : q ∈ tri3 o)
  have hij : i ≠ j := by rintro rfl; exact hpq (hi.symm.trans hj)
  let ob : Block S := ⟨o,hoS⟩
  suffices hex : ∃ x : Cell S B, x.1=ob ∧ slot Λ x i=a ∧ slot Λ x j=b by
    obtain ⟨x,hxo,hxa,hxb⟩ := hex
    refine ⟨x,(mem_triangle e Λ x _).mpr ⟨i,?_⟩,(mem_triangle e Λ x _).mpr ⟨j,?_⟩⟩
    · simp only [pos,grp,hxo,ob,hi,hxa]
    · simp only [pos,grp,hxo,ob,hj,hxb]
  fin_cases i <;> fin_cases j <;> simp at hij
  · exact ⟨(ob,a,b),rfl,rfl,rfl⟩
  · obtain ⟨c,hc⟩ := ((Λ ob).2.1 a).2 b
    exact ⟨(ob,a,c),rfl,rfl,hc⟩
  · exact ⟨(ob,b,a),rfl,rfl,rfl⟩
  · obtain ⟨r,hr⟩ := ((Λ ob).2.2 a).2 b
    exact ⟨(ob,r,a),rfl,rfl,hr⟩
  · obtain ⟨c,hc⟩ := ((Λ ob).2.1 b).2 a
    exact ⟨(ob,b,c),rfl,hc,rfl⟩
  · obtain ⟨r,hr⟩ := ((Λ ob).2.2 b).2 a
    exact ⟨(ob,r,b),rfl,hr,rfl⟩

theorem mem_edges (e : (Fin g × Fin B) ↪ Fin n) (hS : _root_.STS.IsSTS S)
    (Λ : Family S B) (u v : Fin n) :
    s(u,v) ∈ (packing e Λ).biUnion triEdges ↔
      ∃ p q a b, p ≠ q ∧ u=e (p,a) ∧ v=e (q,b) := by
  constructor
  · intro he
    obtain ⟨T,hT,heT⟩ := mem_biUnion.mp he
    obtain ⟨x,-,rfl⟩ := mem_image.mp hT
    obtain ⟨hu,hv,huv⟩ := mem_tE.mp heT
    obtain ⟨i,rfl⟩ := (mem_triangle e Λ x u).mp hu
    obtain ⟨j,rfl⟩ := (mem_triangle e Λ x v).mp hv
    exact ⟨grp x i,grp x j,slot Λ x i,slot Λ x j,
      fun he => huv (congrArg (pos e Λ x) (grp_inj x he)),rfl,rfl⟩
  · rintro ⟨p,q,a,b,hpq,rfl,rfl⟩
    obtain ⟨x,hx,hy⟩ := cover e hS Λ hpq a b
    exact mem_biUnion.mpr ⟨_,mem_image.mpr ⟨x,mem_univ _,rfl⟩,
      mem_tE.mpr ⟨hx,hy,fun he => hpq (congrArg Prod.fst (e.injective he))⟩⟩

theorem edges_eq (e : (Fin g × Fin B) ↪ Fin n) (hS : _root_.STS.IsSTS S)
    (Λ Λ' : Family S B) :
    (packing e Λ).biUnion triEdges=(packing e Λ').biUnion triEdges := by
  ext f
  induction f using Sym2.ind with
  | _ u v => rw [mem_edges e hS,mem_edges e hS]

end CDRBicolour.KBicolor.PrescribedCounting.VariableCross
