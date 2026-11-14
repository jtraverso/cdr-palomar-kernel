/-
Copyright (c) 2026 Juan Pablo Traverso Gianini.
Released under Apache 2.0 license.
Authors: Juan Pablo Traverso Gianini
-/
module
public import CDRBicolour.KBicolor.PrescribedCounting.CrossTypeCounts

/-! # Prescribed STS entropy from actual residual quotas and full Latin tables -/
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace CDRBicolour.KBicolor.PrescribedCounting
open Finset Classical TypedTriangle CDRBicolour.Absorption
variable {n g B k m : ℕ}

theorem bic_mem_bicF {a b c : Fin k} (h : Pattern.bic a b c) :
    ({a,b,c} : Multiset (Fin k)) ∈ bicF k := by
  apply mem_bicF.mpr
  rcases h with ⟨he,hne⟩ | ⟨hne,he | he⟩
  · exact Or.inl ⟨he,by simpa only [he] using hne.symm⟩
  · exact Or.inr (Or.inl ⟨he.symm,hne⟩)
  · exact Or.inr (Or.inr ⟨he.symm,hne⟩)

theorem outline_entropy_at_minimum (κ : Fin B → Fin k) (x : Fin k → Fin k → ℕ)
    (hx : Pattern.IsTour (Hilton.csize κ) x) (hB : 0 < B) (hm : 0 < m)
    (hsize : ∀ i, m ≤ Hilton.csize κ i) :
    0 < (outlineTables Pattern.bic κ (Pattern.outline x)).card ∧
      (B : ℝ)^2*(Real.log m-2) ≤ Real.log (outlineTables Pattern.bic κ (Pattern.outline x)).card := by
  have hBR : (0 : ℝ) < B := by exact_mod_cast hB
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  obtain ⟨hp,hb⟩ := exact_outline_entropy Pattern.bic κ (Pattern.outline x)
    (Pattern.outline_cell hx) (Pattern.outline_row hx) (Pattern.outline_col hx)
    (Pattern.outline_zero hx) (div_pos hmR hBR) hB (by
      intro i
      rw [div_mul_cancel₀ _ hBR.ne']
      exact_mod_cast hsize i)
  refine ⟨hp,?_⟩
  convert hb using 1
  rw [Real.log_div hmR.ne' hBR.ne']
  ring

theorem prescribed_group_entropy {S : Finset (Finset (Fin g))}
    (e : (Fin g × Fin B) ↪ Fin n) (hS : _root_.STS.IsSTS S)
    (lab : Fin n → Fin k) (κ : Fin B → Fin k) (hlabel : ∀ p a, lab (e (p,a))=κ a)
    (Λ₀ : VariableCross.Family S B)
    (D : Finset (Finset (Fin n)))
    (hD : IsDecomposition (rHostK lab ((VariableCross.packing e Λ₀).biUnion triEdges))
      (bicF k) (edges (rHostK lab ((VariableCross.packing e Λ₀).biUnion triEdges))) D)
    (t : Fin k → Fin k → ℕ) (y : VariableCross.Block S → Fin k → Fin k → ℕ)
    (hy : ∀ o, Pattern.IsTour (Hilton.csize κ) (y o))
    (hquota : ∀ i j, i ≠ j → kTypeCount lab D i j+∑ o, 3*y o i j=t i j)
    (hB : 0 < B) (hm : 0 < m) (hsize : ∀ i, m ≤ Hilton.csize κ i) :
    let tv : TypeCoord k → ℕ := fun p => t p.1.1 p.1.2
    0 < exactTypeCount lab tv ∧
      (Fintype.card (VariableCross.Block S) : ℝ)*(B : ℝ)^2*(Real.log m-2) ≤
        Real.log (exactTypeCount lab tv) := by
  intro tv
  let tables := fun o : VariableCross.Block S => outlineTables Pattern.bic κ (Pattern.outline (y o))
  have hLatin : ∀ o L, L ∈ tables o → _root_.STS.IsLatin L := by
    intro o L hL
    exact (mem_filter.mp hL).2.1
  have hAllowed : ∀ f : VariableCross.Choices tables,
      ∀ T ∈ VariableCross.packing e (VariableCross.chosenFamily tables hLatin f),
        IsAllowed (kHost lab) (bicF k) T := by
    intro f
    apply VariableCross.packing_allowed e lab κ hlabel
    intro o a b
    exact bic_mem_bicF ((mem_filter.mp (f o).2).2.2.1 a b)
  have htype : ∀ f : VariableCross.Choices tables,
      typeVector lab (D ∪ VariableCross.packing e (VariableCross.chosenFamily tables hLatin f))=tv := by
    intro f
    let Λ := VariableCross.chosenFamily tables hLatin f
    have hDf : ∀ T ∈ D, IsAllowed (rHostK lab ((VariableCross.packing e Λ).biUnion triEdges)) (bicF k) T := by
      rw [VariableCross.edges_eq e hS Λ Λ₀]
      exact hD.1
    have hd := (VariableCross.packing_disjoint_residual e lab Λ hDf).symm
    funext p
    change kTypeCount lab (D ∪ VariableCross.packing e Λ) p.1.1 p.1.2=t p.1.1 p.1.2
    have he : kTypeCount lab (D ∪ VariableCross.packing e Λ) p.1.1 p.1.2=
        kTypeCount lab D p.1.1 p.1.2+kTypeCount lab (VariableCross.packing e Λ) p.1.1 p.1.2 := by
      unfold kTypeCount
      rw [filter_union,card_union_of_disjoint (disjoint_filter_filter hd)]
    rw [he,VariableCross.packing_typeCount e hS lab κ hlabel]
    have hc : ∀ o, latinTypeCount κ (Λ o).1 p.1.1 p.1.2=3*y o p.1.1 p.1.2 := by
      intro o
      exact latinTypeCount_of_tour κ _ (hy o) (mem_filter.mp (f o).2).2.2.2
        p.1.1 p.1.2 (mem_offDiag.mp p.2).2.2
    simp_rw [hc]
    exact hquota _ _ (mem_offDiag.mp p.2).2.2
  have hcard := VariableCross.family_count_le_exact e hS lab Λ₀ tv tables hLatin hAllowed D hD htype
  have hloc := fun o => outline_entropy_at_minimum κ (y o) (hy o) hB hm hsize
  have hp : 0 < ∏ o, (tables o).card := prod_pos (fun o _ => (hloc o).1)
  refine ⟨hp.trans_le hcard,?_⟩
  have hpR : (0 : ℝ) < ∏ o, ((tables o).card : ℝ) := by exact_mod_cast hp
  have hh := Real.log_le_log hpR (show (∏ o, ((tables o).card : ℝ)) ≤ exactTypeCount lab tv by
    exact_mod_cast hcard)
  rw [Real.log_prod (fun o _ => by exact_mod_cast ((hloc o).1.ne'))] at hh
  have hs := sum_le_sum (fun o (_ : o ∈ (univ : Finset (VariableCross.Block S))) => (hloc o).2)
  have he : (∑ _o : VariableCross.Block S, (B : ℝ)^2*(Real.log m-2))=
      (Fintype.card (VariableCross.Block S) : ℝ)*(B : ℝ)^2*(Real.log m-2) := by simp; ring
  rw [he] at hs
  exact hs.trans hh

end CDRBicolour.KBicolor.PrescribedCounting
