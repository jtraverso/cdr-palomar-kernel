/-
Copyright (c) 2026 Juan Pablo Traverso Gianini.
Released under Apache 2.0 license.
Authors: Juan Pablo Traverso Gianini
-/
module
public import CDRBicolour.KBicolor.PrescribedCounting.CrossAssembly
public import CDRBicolour.KBicolor.PrescribedCounting.OutlineSymmetry
public import CDRBicolour.KBicolor.Pattern.Outline

/-! # Exact type contributions of the independently variable group tables -/
@[expose] public section
noncomputable section
set_option autoImplicit false
namespace CDRBicolour.KBicolor.PrescribedCounting
open Finset Classical TypedTriangle CDRBicolour.Absorption
variable {n g B k : ℕ}

theorem triple_indicator (a b c X Y : Fin k) (hXY : X ≠ Y) :
    (if ({a,b,c} : Multiset (Fin k))={X,X,Y} then 1 else 0 : ℕ) =
      (if a=X ∧ b=X ∧ c=Y then 1 else 0) +
      (if a=X ∧ b=Y ∧ c=X then 1 else 0) +
      (if a=Y ∧ b=X ∧ c=X then 1 else 0) := by
  by_cases he : ({a,b,c} : Multiset (Fin k))={X,X,Y}
  · have ha : a=X ∨ a=Y := by
      have hh : a ∈ ({X,X,Y} : Multiset (Fin k)) := he ▸ (by simp)
      simpa only [Multiset.insert_eq_cons,Multiset.mem_cons,Multiset.mem_singleton,or_self_left] using hh
    have hb : b=X ∨ b=Y := by
      have hh : b ∈ ({X,X,Y} : Multiset (Fin k)) := he ▸ (by simp)
      simpa only [Multiset.insert_eq_cons,Multiset.mem_cons,Multiset.mem_singleton,or_self_left] using hh
    have hc : c=X ∨ c=Y := by
      have hh : c ∈ ({X,X,Y} : Multiset (Fin k)) := he ▸ (by simp)
      simpa only [Multiset.insert_eq_cons,Multiset.mem_cons,Multiset.mem_singleton,or_self_left] using hh
    have hcnt := congrArg (Multiset.count X) he
    simp only [Multiset.insert_eq_cons,Multiset.count_cons,Multiset.count_singleton] at hcnt
    rcases ha with rfl | rfl <;> rcases hb with rfl | rfl <;> rcases hc with rfl | rfl <;>
      simp_all [Multiset.insert_eq_cons,Multiset.count_cons,Multiset.count_singleton]
  · have h1 : ¬(a=X ∧ b=X ∧ c=Y) := by rintro ⟨rfl,rfl,rfl⟩; exact he rfl
    have h2 : ¬(a=X ∧ b=Y ∧ c=X) := by
      rintro ⟨ha,hb,hc⟩
      apply he
      rw [ha,hb,hc]
      exact perm_aba X Y
    have h3 : ¬(a=Y ∧ b=X ∧ c=X) := by
      rintro ⟨ha,hb,hc⟩
      apply he
      rw [ha,hb,hc]
      exact perm_abb Y X
    rw [if_neg he,if_neg h1,if_neg h2,if_neg h3]

def latinTypeCount (κ : Fin B → Fin k) (L : Fin B → Fin B → Fin B) (X Y : Fin k) : ℕ :=
  ∑ r, ∑ c, if ({κ r,κ c,κ (L r c)} : Multiset (Fin k))={X,X,Y} then 1 else 0

theorem outlineMass_indicator (κ : Fin B → Fin k) (L : Fin B → Fin B → Fin B) (X Y Z : Fin k) :
    outlineMass κ L X Y Z = ∑ r, ∑ c,
      if κ r=X ∧ κ c=Y ∧ κ (L r c)=Z then 1 else 0 := by
  simp only [outlineMass,sum_filter]
  apply sum_congr rfl
  intro r _
  by_cases hr : κ r=X
  · simp only [hr,ite_true,true_and]
    apply sum_congr rfl
    intro c _
    by_cases hc : κ c=Y <;> simp [hc]
  · simp [hr]

theorem latinTypeCount_eq_outline (κ : Fin B → Fin k) (L : Fin B → Fin B → Fin B)
    (X Y : Fin k) (hXY : X ≠ Y) :
    latinTypeCount κ L X Y=outlineMass κ L X X Y+outlineMass κ L X Y X+outlineMass κ L Y X X := by
  simp only [latinTypeCount,triple_indicator _ _ _ X Y hXY,outlineMass_indicator,sum_add_distrib]

theorem latinTypeCount_of_tour (κ : Fin B → Fin k) (L : Fin B → Fin B → Fin B)
    {b : Fin k → ℕ} {x : Fin k → Fin k → ℕ} (hx : Pattern.IsTour b x)
    (hM : outlineMass κ L=Pattern.outline x) (X Y : Fin k) (hXY : X ≠ Y) :
    latinTypeCount κ L X Y=3*x X Y := by
  rw [latinTypeCount_eq_outline κ L X Y hXY,hM]
  simp only [Pattern.outline,hx.diag,hXY,hXY.symm,ite_true,ite_false,add_zero,zero_add]
  omega

namespace VariableCross
variable {S : Finset (Finset (Fin g))}

theorem triangle_injective (e : (Fin g × Fin B) ↪ Fin n) (hS : _root_.STS.IsSTS S)
    (Λ : Family S B) : Function.Injective (triangle e Λ) := by
  intro x y he
  have hp : ∀ i, ∃ j, pos e Λ y j=pos e Λ x i := by
    intro i
    apply (mem_triangle e Λ y _).mp
    rw [← he]
    exact (mem_triangle e Λ x _).mpr ⟨i,rfl⟩
  obtain ⟨i0,h0⟩ := hp 0
  obtain ⟨i1,h1⟩ := hp 1
  obtain ⟨ho,rfl,rfl⟩ := share_two e hS (by decide : (0 : Fin 3) ≠ 1) h0.symm h1.symm
  exact cell_eq_01 e ho h0.symm h1.symm

theorem packing_typeCount (e : (Fin g × Fin B) ↪ Fin n) (hS : _root_.STS.IsSTS S)
    (lab : Fin n → Fin k) (κ : Fin B → Fin k) (hlabel : ∀ p a, lab (e (p,a))=κ a)
    (Λ : Family S B) (X Y : Fin k) :
    kTypeCount lab (packing e Λ) X Y=∑ o, latinTypeCount κ (Λ o).1 X Y := by
  have hlabels : ∀ x : Cell S B, (triangle e Λ x).val.map lab=
      ({κ x.2.1,κ x.2.2,κ ((Λ x.1).1 x.2.1 x.2.2)} : Multiset (Fin k)) := by
    intro x
    rw [triangle,map_triple_lab lab (pos_ne e Λ x (by decide))
      (pos_ne e Λ x (by decide)) (pos_ne e Λ x (by decide))]
    simp only [pos,slot,hlabel,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.head_cons,
      Matrix.cons_val_two,Matrix.tail_cons]
  unfold kTypeCount packing
  rw [filter_image,card_image_of_injective _ (triangle_injective e hS Λ),card_eq_sum_ones,sum_filter]
  simp only [hlabels,Cell,Fintype.sum_prod_type,latinTypeCount]

end VariableCross
end CDRBicolour.KBicolor.PrescribedCounting
