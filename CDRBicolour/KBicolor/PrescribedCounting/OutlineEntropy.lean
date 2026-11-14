/-
Copyright (c) 2026 Juan Pablo Traverso Gianini.
Released under Apache 2.0 license.
Authors: Juan Pablo Traverso Gianini
-/
module
public import CDRBicolour.KBicolor.PrescribedCounting.FixedClassEntropy
public import CDRBicolour.KBicolor.PrescribedCounting.HiltonExact

/-! # Optimal entropy for every feasible prescribed Latin outline

The outline is fixed in advance. Hilton realizes it, and the independent
symbol-class factorizations preserve every entry of that same outline.
-/
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace CDRBicolour.KBicolor.PrescribedCounting
open Finset Classical
variable {n k : ℕ}

def outlineMass (κ : Fin n → Fin k) (L : Fin n → Fin n → Fin n)
    (r c s : Fin k) : ℕ :=
  ∑ x ∈ univ.filter (fun x => κ x=r), ∑ y ∈ univ.filter (fun y => κ y=c),
    if κ (L x y)=s then 1 else 0

def outlineTables (ok : Fin k → Fin k → Fin k → Prop) (κ : Fin n → Fin k)
    (M : Fin k → Fin k → Fin k → ℕ) : Finset (Fin n → Fin n → Fin n) :=
  univ.filter (fun L => _root_.STS.IsLatin L ∧ (∀ x y, ok (κ x) (κ y) (κ (L x y))) ∧
    outlineMass κ L=M)

theorem exact_outline_entropy (ok : Fin k → Fin k → Fin k → Prop)
    (κ : Fin n → Fin k) (M : Fin k → Fin k → Fin k → ℕ)
    (h₁ : ∀ r c, ∑ s, M r c s=Hilton.csize κ r*Hilton.csize κ c)
    (h₂ : ∀ r s, ∑ c, M r c s=Hilton.csize κ r*Hilton.csize κ s)
    (h₃ : ∀ c s, ∑ r, M r c s=Hilton.csize κ c*Hilton.csize κ s)
    (h₀ : ∀ r c s, ¬ok r c s → M r c s=0)
    {δ : ℝ} (hδ : 0<δ) (hn : 0<n) (hsize : ∀ s, δ*n≤Hilton.csize κ s) :
    0<(outlineTables ok κ M).card ∧
      (n:ℝ)^2*(Real.log n+Real.log δ-2) ≤ Real.log (outlineTables ok κ M).card := by
  obtain ⟨L₀,hrow,hcol,hok,hM⟩ := Hilton.realize_exact ok κ κ κ M h₁ h₂ h₃ h₀
  have hL₀ : _root_.STS.IsLatin L₀ := ⟨hrow,hcol⟩
  let cls : Fin n → Fin n → Fin k := fun r c => κ (L₀ r c)
  have hreg : ∀ s, Regular (classGraph cls s) (Hilton.csize κ s) :=
    latin_class_graphs_regular κ L₀ hL₀
  obtain ⟨hpos,hbound⟩ := fixed_class_pattern_entropy κ cls hreg hδ hn hsize
  have hsub : classPatternTables κ cls ⊆ outlineTables ok κ M := by
    intro L hL
    obtain ⟨_,hLatin,hcls⟩ := mem_filter.mp hL
    apply mem_filter.mpr
    refine ⟨mem_univ _,hLatin,?_,?_⟩
    · intro r c
      rw [hcls r c]
      exact hok r c
    · funext r c s
      change (∑ x ∈ univ.filter (fun x => κ x=r), ∑ y ∈ univ.filter (fun y => κ y=c),
        if κ (L x y)=s then 1 else 0)=M r c s
      simp_rw [hcls]
      exact hM r c s
  have hle := card_le_card hsub
  refine ⟨hpos.trans_le hle,hbound.trans ?_⟩
  exact Real.log_le_log (by exact_mod_cast hpos) (by exact_mod_cast hle)

end CDRBicolour.KBicolor.PrescribedCounting
