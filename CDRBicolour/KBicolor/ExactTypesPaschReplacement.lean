/-
Copyright (c) 2026 Juan Pablo Traverso Gianini.
Released under Apache 2.0 license.
Authors: Juan Pablo Traverso Gianini
-/
module
public import CDRBicolour.KBicolor.LatinMixedAverage
public import CDRBicolour.KBicolor.LatinPackingPaschCount
public import CDRBicolour.KBicolor.LatinIntercalateTransport
public import RequestProject.TypedTriangle.PaschModeUniverse

/-! # Simultaneous exact types and separated Pasch counts by Latin replacement

This finite assembly step has no asymptotic assumptions. Its numerical
input is a family of Latin tables whose intercalate counts are separated
by the proved mixed-configuration budget.
-/
@[expose] public section
noncomputable section
set_option autoImplicit false
namespace CDRBicolour.KBicolor.LatinPasch
open Finset Classical TypedTriangle TypedTriangle.Applications.Latin
variable {k n m : ℕ} {lab : Fin n → Fin k} {X Y : Fin k}
variable {r c s : Fin m → Fin n} (h : LatPlace lab X Y r c s)
include h

theorem exact_types_pasch_replacement {K : ℕ} (hm : 2 ≤ m)
    (L₀ : LatinSquare (Fin m)) (L : Fin K → LatinSquare (Fin m))
    (D₀ : Finset (Finset (Fin n)))
    (hD₀ : IsDecomposition (kHost lab) (bicF k) (edges (kHost lab)) D₀)
    (hsub : latPackK r c s L₀ ⊆ D₀)
    (hgap : ∀ i j : Fin K, i < j →
      ((intercalates (L j)).card : ℝ) + mixedBudget n m < (intercalates (L i)).card) :
    ∃ D : Fin K → Finset (Finset (Fin n)),
      (∀ i, IsDecomposition (kHost lab) (bicF k) (edges (kHost lab)) (D i)) ∧
      (∀ i A B, A ≠ B → kTypeCount lab (D i) A B = kTypeCount lab D₀ A B) ∧
      Function.Injective (fun i => Pasch.count (D i)) := by
  let R := D₀ \ latPackK r c s L₀
  have hRD : R ⊆ D₀ := sdiff_subset
  have hRcg : Pasch.PairCodegreeBound R 1 :=
    Pasch.pairCodegreeBound_of_linear ((Pasch.packing_linear ⟨hD₀.1,hD₀.2.1⟩).mono hRD)
  have hRtrip : ∀ T ∈ R, T.card=3 := fun T hT => (hD₀.1 T (hRD hT)).1
  have hRcard : R.card ≤ n^2 := (card_le_card hRD).trans
    (card_sts_le_sq (show _root_.STS.IsSTS D₀ from (mem_filter.mp (mem_kBlocks_of_decomp lab hD₀)).2.1))
  have hlatin : ∀ i, _root_.STS.IsLatin (L i) := fun i =>
    ⟨(L i).row_bijective,(L i).column_bijective⟩
  have hsmall := fun i => exists_isotopy_small_mixed h (L i) (hlatin i) hm R hRcg hRtrip hRcard
  choose ρ σ herr using hsmall
  let Q : Fin K → Finset (Finset (Fin n)) := fun i =>
    latPackK r c s (isotopyValue (L i) (ρ i) (σ i))
  let D : Fin K → Finset (Finset (Fin n)) := fun i => R ∪ Q i
  have hrepl := fun i => replace_latin_decomposition h L₀
    (isotopyValue (L i) (ρ i) (σ i)) ⟨L₀.row_bijective,L₀.column_bijective⟩
    (isotopy_isLatin h (L i) (hlatin i) (ρ i) (σ i)) hD₀ hsub
  have hRnone : ∀ T ∈ R, ¬ IsPartite (slotPart r c s) T := by
    intro T hTR hT
    exact disjoint_left.mp (residual_not_universe h L₀ hD₀ hsub) hTR
      ((partite_iff_universe h T).mp hT)
  have hQI : ∀ i, Pasch.count (Q i) = (intercalates (L i)).card := by
    intro i
    have hh := count_latin_packing h (isotopySquare (L i) (ρ i) (σ i))
    rw [intercalates_card_isotopy] at hh
    exact hh
  have hsplit : ∀ i, Pasch.count (D i) = Pasch.count R + (intercalates (L i)).card +
      #(Pasch.mixedConfigurations (Q i) R 1 ∅) + #(Pasch.mixedConfigurations (Q i) R 2 ∅) := by
    intro i
    have hh := count_union_four_terms (slotPart r c s) (Q i) R
      (hrepl i).2.1.symm hRnone (fun T hT =>
        (partite_iff_universe h T).mpr ((packing_subset_universe h _) hT))
    rw [hQI] at hh
    simpa only [D, union_comm] using hh
  refine ⟨D,fun i => (hrepl i).1,fun i => (hrepl i).2.2,?_⟩
  intro i j he
  by_contra hn
  have hneq : ∀ a b : Fin K, a < b → Pasch.count (D a) ≠ Pasch.count (D b) := by
    intro a b hab habeq
    have ha := hsplit a
    have hb := hsplit b
    have hg := hgap a b hab
    have hbe := herr b
    have hn₁ := Nat.cast_nonneg (α := ℝ) (#(Pasch.mixedConfigurations (Q a) R 1 ∅))
    have hn₂ := Nat.cast_nonneg (α := ℝ) (#(Pasch.mixedConfigurations (Q a) R 2 ∅))
    have habR : (Pasch.count (D a) : ℝ) = Pasch.count (D b) := by exact_mod_cast habeq
    have haR : (Pasch.count (D a) : ℝ) = (Pasch.count R : ℝ) + (intercalates (L a)).card +
        #(Pasch.mixedConfigurations (Q a) R 1 ∅) + #(Pasch.mixedConfigurations (Q a) R 2 ∅) := by exact_mod_cast ha
    have hbR : (Pasch.count (D b) : ℝ) = (Pasch.count R : ℝ) + (intercalates (L b)).card +
        #(Pasch.mixedConfigurations (Q b) R 1 ∅) + #(Pasch.mixedConfigurations (Q b) R 2 ∅) := by exact_mod_cast hb
    change (#(Pasch.mixedConfigurations (Q b) R 1 ∅) : ℝ) +
      #(Pasch.mixedConfigurations (Q b) R 2 ∅) ≤ mixedBudget n m at hbe
    linarith
  rcases lt_or_gt_of_ne hn with hij | hji
  · exact hneq i j hij he
  · exact hneq j i hji he.symm

end CDRBicolour.KBicolor.LatinPasch
