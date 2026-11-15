/-
Copyright (c) 2026 Juan Pablo Traverso Gianini.
Released under Apache 2.0 license.
Authors: Juan Pablo Traverso Gianini
-/
module
public import CDRIIILib.KBicolor.PrescribedCounting.RegularEntropy
public import CDRIIILib.KBicolor.Pattern.Spread

/-! # Many Latin tables with the same cell-by-cell symbol-class pattern

The independent choices are ordered factorizations of the regular graphs
assigned to the individual symbol classes. Their union is decoded into a
Latin square injectively. No randomness or external counting input is used.
-/
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace CDRBicolour.KBicolor.PrescribedCounting
open Finset Classical
variable {n k : ℕ}

def classGraph (cls : Fin n → Fin n → Fin k) (s : Fin k) : Finset (Fin n × Fin n) :=
  univ.filter (fun p => cls p.1 p.2=s)

abbrev FactorFamily (κ : Fin n → Fin k) (cls : Fin n → Fin n → Fin k) :=
  ∀ s, PartialFactorization (classGraph cls s) (Hilton.csize κ s)

def classPermutation {κ : Fin n → Fin k} {cls : Fin n → Fin n → Fin k}
    (F : FactorFamily κ cls) (s : Fin k) (z : {z // κ z=s}) : Equiv.Perm (Fin n) :=
  (F s).1.1 (Fintype.equivFin {z // κ z=s} z)

def symbolPermutation {κ : Fin n → Fin k} {cls : Fin n → Fin n → Fin k}
    (F : FactorFamily κ cls) (z : Fin n) : Equiv.Perm (Fin n) :=
  classPermutation F (κ z) ⟨z,rfl⟩

theorem symbolPermutation_at_class {κ : Fin n → Fin k} {cls : Fin n → Fin n → Fin k}
    (F : FactorFamily κ cls) {z : Fin n} {s : Fin k} (hz : κ z=s) :
    symbolPermutation F z=classPermutation F s ⟨z,hz⟩ := by
  subst s
  rfl

theorem symbolPermutation_supported {κ : Fin n → Fin k} {cls : Fin n → Fin n → Fin k}
    (F : FactorFamily κ cls) (z v : Fin n) : cls v (symbolPermutation F z v)=κ z := by
  have hh := (F (κ z)).2 (Fintype.equivFin {w // κ w=κ z} ⟨z,rfl⟩) v
  exact (mem_filter.mp hh).2

theorem symbolPermutation_injective {κ : Fin n → Fin k} {cls : Fin n → Fin n → Fin k}
    (F : FactorFamily κ cls) (v : Fin n) : Function.Injective (fun z => symbolPermutation F z v) := by
  intro z z' he
  change symbolPermutation F z v=symbolPermutation F z' v at he
  have hc : κ z=κ z' := by
    rw [← symbolPermutation_supported F z v,← symbolPermutation_supported F z' v,he]
  rw [symbolPermutation_at_class F hc.symm] at he
  by_contra hzz
  have hi : Fintype.equivFin {w // κ w=κ z} ⟨z,rfl⟩ ≠
      Fintype.equivFin {w // κ w=κ z} ⟨z',hc.symm⟩ := by
    intro hh
    exact hzz (congrArg Subtype.val ((Fintype.equivFin _).injective hh))
  exact (F (κ z)).1.2 _ _ hi v he

def rowPermutation {κ : Fin n → Fin k} {cls : Fin n → Fin n → Fin k}
    (F : FactorFamily κ cls) (v : Fin n) : Equiv.Perm (Fin n) :=
  Equiv.ofBijective (fun z => symbolPermutation F z v)
    (Finite.injective_iff_bijective.mp (symbolPermutation_injective F v))

def tableFromFactors {κ : Fin n → Fin k} {cls : Fin n → Fin n → Fin k}
    (F : FactorFamily κ cls) (r c : Fin n) : Fin n := (rowPermutation F r).symm c

theorem table_at_symbol {κ : Fin n → Fin k} {cls : Fin n → Fin n → Fin k}
    (F : FactorFamily κ cls) (r z : Fin n) : tableFromFactors F r (symbolPermutation F z r)=z :=
  (rowPermutation F r).symm_apply_apply z

theorem symbol_at_table {κ : Fin n → Fin k} {cls : Fin n → Fin n → Fin k}
    (F : FactorFamily κ cls) (r c : Fin n) : symbolPermutation F (tableFromFactors F r c) r=c :=
  (rowPermutation F r).apply_symm_apply c

theorem tableFromFactors_latin {κ : Fin n → Fin k} {cls : Fin n → Fin n → Fin k}
    (F : FactorFamily κ cls) : _root_.STS.IsLatin (tableFromFactors F) := by
  refine ⟨fun r => (rowPermutation F r).symm.bijective,fun c => ?_⟩
  apply Finite.injective_iff_bijective.mp
  intro r r' he
  change tableFromFactors F r c=tableFromFactors F r' c at he
  have h₁ := symbol_at_table F r c
  have h₂ := symbol_at_table F r' c
  rw [he] at h₁
  exact (symbolPermutation F _).injective (h₁.trans h₂.symm)

theorem tableFromFactors_pattern {κ : Fin n → Fin k} {cls : Fin n → Fin n → Fin k}
    (F : FactorFamily κ cls) (r c : Fin n) : κ (tableFromFactors F r c)=cls r c := by
  have hh := symbolPermutation_supported F (tableFromFactors F r c) r
  simpa only [symbol_at_table] using hh.symm

theorem tableFromFactors_injective {κ : Fin n → Fin k} {cls : Fin n → Fin n → Fin k} :
    Function.Injective (tableFromFactors (κ:=κ) (cls:=cls)) := by
  intro F G hFG
  funext s
  apply Subtype.ext
  apply Subtype.ext
  funext i
  apply Equiv.ext
  intro r
  let z : {z // κ z=s} := (Fintype.equivFin {z // κ z=s}).symm i
  have hindex : Fintype.equivFin {z // κ z=s} z=i := (Fintype.equivFin _).apply_symm_apply i
  have hF : symbolPermutation F z.1=(F s).1.1 i := by
    rw [symbolPermutation_at_class F z.2]
    change (F s).1.1 (Fintype.equivFin _ z)=(F s).1.1 i
    rw [hindex]
  have hG : symbolPermutation G z.1=(G s).1.1 i := by
    rw [symbolPermutation_at_class G z.2]
    change (G s).1.1 (Fintype.equivFin _ z)=(G s).1.1 i
    rw [hindex]
  have hhF := table_at_symbol F r z.1
  have hhG := table_at_symbol G r z.1
  rw [hFG] at hhF
  have he := ((tableFromFactors_latin G).1 r).1 (hhF.trans hhG.symm)
  simpa only [hF,hG] using he

def classPatternTables (κ : Fin n → Fin k) (cls : Fin n → Fin n → Fin k) :
    Finset (Fin n → Fin n → Fin n) :=
  univ.filter (fun L => _root_.STS.IsLatin L ∧ ∀ r c, κ (L r c)=cls r c)

theorem classPatternTables_count (κ : Fin n → Fin k) (cls : Fin n → Fin n → Fin k) :
    (∏ s, Fintype.card (PartialFactorization (classGraph cls s) (Hilton.csize κ s))) ≤
      (classPatternTables κ cls).card := by
  let f : FactorFamily κ cls → ↥(classPatternTables κ cls) := fun F =>
    ⟨tableFromFactors F,mem_filter.mpr ⟨mem_univ _,tableFromFactors_latin F,tableFromFactors_pattern F⟩⟩
  have hh := Fintype.card_le_of_injective f (fun F G he =>
    tableFromFactors_injective (congrArg Subtype.val he))
  simpa only [Fintype.card_pi,Fintype.card_coe] using hh

end CDRBicolour.KBicolor.PrescribedCounting
