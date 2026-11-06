/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import RequestProject.TypedTriangle.Elimination

@[expose] public section

/-!
# Concrete reduction away from a small set of vertices

Local proof candidate, NOT kernel-checked in this campaign.
The two elimination events are copied from `compression_of_sample`; no sample
is needed for these events. This is not yet the local-group restriction bridge.
-/

open Finset
noncomputable section
open Classical

namespace TypedTriangle
open Incidence

variable {V I : Type*} [Fintype V] {H : Host V I} {F : Set (Multiset I)}

/-- Pivots remove internal Z edges; independent star corrections remove all remaining
Z incidences, with a linear signed correction. No physicality assumption on x is added. -/
theorem linear_reduction_away_vertices {α : ℝ} {h : ℕ}
    (hα : 0 < α) (hH3 : CommonNbrCond H F α) (hH4 : HingeCond H F α h)
    (Z : Finset V)
    (hw1 : (Z.card : ℝ) + 2 < α * Fintype.card V)
    (hw2 : ((Z.card : ℝ) + h) * 2 ^ Nat.choose h 2 ≤ α / 2 * Fintype.card V) :
    ∃ C : localGroup H F →ₗ[ℤ] (Finset V → ℤ), ∀ x : localGroup H F,
      x.1 - triBd H F (C x) ∈ localGroup H F ∧
      (∀ e, TouchZ Z e → (x.1 - triBd H F (C x)) e = 0) ∧
      (∑ T, |C x T|) ≤ (1 + 8 * compL2 α : ℕ) * l1E x.1 ∧
      l1E (x.1 - triBd H F (C x)) ≤ compN α * l1E x.1 := by
  set L := localGroup H F
  set M1 := L ⊓ vanishOn (· ∈ Z.sym2)
  set M2 := L ⊓ vanishOn (TouchZ Z)
  have hZ1 : (Z.card : ℝ) < α * Fintype.card V := by linarith
  set ps1 := piv1 hH3 Z hZ1
  have he1 : ∀ x : L, pivF ps1 x.1 ∈ M1 := by
    intro x
    refine ⟨pivF_mem ps1 x.2, fun e he => ?_⟩
    by_cases hS : e ∈ S1 H F Z
    · exact pivF_apply_mem ps1 x.1 hS
    · have hT : ¬ HasTri H F e := fun hT => hS (Finset.mem_filter.2 ⟨Finset.mem_univ _, he, hT⟩)
      exact localGroup_zero_of_not_hasTri (pivF_mem ps1 x.2) hT
  let e1 : L →ₗ[ℤ] M1 := LinearMap.codRestrict M1 ((pivL ps1).comp L.subtype) he1
  let c1 : L →ₗ[ℤ] (Finset V → ℤ) := (pivC ps1).comp L.subtype
  have hs1 : ∀ x : L, x.1 - (e1 x).1 = triBd H F (c1 x) := fun x => by
    change x.1 - pivF ps1 x.1 = _; simp [pivF, c1]
  have hc1 : ∀ x : L, ∑ T, |c1 x T| ≤ l1E x.1 := fun x => sum_abs_pivC_le ps1 x.1
  have hn1 : ∀ x : L, l1E (e1 x).1 ≤ 4 * l1E x.1 := fun x => l1E_pivF_le ps1 x.1
  ------------------------------------------------------------------ evento 2
  set D2 := 3 * ⌊2 / α⌋₊
  let G2 : V → SimpleGraph V := fun v => linkOn H F v (goodEdges H (Z.erase v) ∅)
  have hdeg0 : ∀ x, degIn (∅ : Finset (Sym2 V)) x ≤ 0 := fun x => by simp [degIn]
  have hcardE : ∀ v, ((Z.erase v).card : ℝ) ≤ Z.card := fun v => by
    exact_mod_cast Finset.card_erase_le
  have hhalf : (Z.card : ℝ) ≤ α / 2 * Fintype.card V := by
    have hp : (1 : ℝ) ≤ 2 ^ Nat.choose h 2 := one_le_pow₀ (by norm_num)
    have hz : (0 : ℝ) ≤ Z.card := by positivity
    have hh : (0 : ℝ) ≤ h := by positivity
    nlinarith [mul_nonneg (add_nonneg hz hh) (sub_nonneg.mpr hp)]
  obtain ⟨c2, hc2⟩ := star_event (M := M1) (H := H) (F := F) Z G2
    (fun v _ a b hab => hab.1)
    (by
      intro v _ a b hab hav
      have hgood := (Finset.mem_filter.1 (Finset.mem_filter.1 hab.2).1).2
      have hva : v ≠ a := (linkGraph_adj_ne hab.1).1
      exact hgood a (Finset.mem_erase.2 ⟨Ne.symm hva, hav⟩) (by simp))
    (D := D2)
    (fun v _ => linkOn_good_diamLe hα hH3 v (Z.erase v) ∅ hdeg0
      (by push_cast; linarith [hcardE v, hhalf]))
    (by
      intro x hx v hv
      have hvan : ∀ y ∈ Z.erase v, starProj v x y = 0 := by
        intro y hy
        rw [starProj_apply, if_neg (Finset.ne_of_mem_erase hy)]
        exact hx.2 _ (Finset.mem_sym2_iff.2 fun a ha => by
          rcases Sym2.mem_iff.1 ha with rfl | rfl
          · exact hv
          · exact Finset.mem_of_mem_erase hy)
      refine (link_image_robust hα hH3 hH4 (Z.erase v) (by simp) ∅ 0 hdeg0
        (by push_cast; linarith [hcardE v]) (by
          push_cast
          refine le_trans ?_ hw2
          have : (0 : ℝ) ≤ 2 ^ Nat.choose h 2 := by positivity
          nlinarith [hcardE v]) hvan).1 (starProj_mem_of_localGroup hx.1 v))
  have he2 : ∀ x : M1, x.1 - triBd H F (c2 x) ∈ M2 := by
    intro x
    refine ⟨Submodule.sub_mem _ x.2.1 (triBd_mem_localGroup H F _), fun e he => ?_⟩
    obtain ⟨z, hz, hze⟩ := he
    obtain ⟨-, hstar, -⟩ := hc2 x
    induction e using Sym2.ind with
    | _ a b =>
    have hmem := Submodule.sub_mem _ x.2.1 (triBd_mem_localGroup H F (c2 x))
    obtain ⟨y, hey⟩ : ∃ y, s(a, b) = s(z, y) := by
      rcases Sym2.mem_iff.1 hze with rfl | rfl
      · exact ⟨b, rfl⟩
      · exact ⟨a, Sym2.eq_swap⟩
    rw [hey]
    by_cases hyz : y = z
    · subst hyz; exact localGroup_zero_of_not_hasTri hmem (not_hasTri_diag y)
    · have := congrFun (hstar z hz) y
      rwa [starProj_apply, if_neg hyz] at this
  let e2 : M1 →ₗ[ℤ] M2 := LinearMap.codRestrict M2 (M1.subtype - (triBd H F).comp c2) he2
  have hs2 : ∀ x : M1, x.1 - (e2 x).1 = triBd H F (c2 x) := fun x => by
    change x.1 - (x.1 - triBd H F (c2 x)) = _; abel
  have hcc2 : ∀ x : M1, ∑ T, |c2 x T| ≤ compL2 α * (2 * l1E x.1) := fun x => by
    have := (hc2 x).2.2; simpa [compL2, D2] using this
  have hn2 : ∀ x : M1, l1E (e2 x).1 ≤ l1E x.1 + 3 * (compL2 α * (2 * l1E x.1)) := fun x => by
    change l1E (x.1 - triBd H F (c2 x)) ≤ _
    have := l1E_sub_le x.1 (triBd H F (c2 x))
    have := l1E_triBd_le H F (c2 x)
    linarith [hcc2 x]
  let C : L →ₗ[ℤ] (Finset V → ℤ) := c1 + c2.comp e1
  refine ⟨C, fun x => ?_⟩
  have heq : x.1 - triBd H F (C x) = (e2 (e1 x)).1 := by
    change x.1 - triBd H F (c1 x + c2 (e1 x)) = _
    rw [map_add, ← hs1 x, ← hs2 (e1 x)]
    abel
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [heq]
    exact (e2 (e1 x)).2.1
  · intro e he
    rw [heq]
    exact (e2 (e1 x)).2.2 e he
  · change (∑ T, |c1 x T + c2 (e1 x) T|) ≤ _
    have hscale := mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_left (hn1 x) (by norm_num : (0 : ℤ) ≤ 2))
      (by positivity : (0 : ℤ) ≤ compL2 α)
    calc
      (∑ T, |c1 x T + c2 (e1 x) T|) ≤
          (∑ T, |c1 x T|) + ∑ T, |c2 (e1 x) T| :=
        sum_abs_add_le (c1 x) (c2 (e1 x))
      _ ≤ l1E x.1 + (compL2 α : ℤ) * (2 * l1E (e1 x).1) :=
        add_le_add (hc1 x) (hcc2 (e1 x))
      _ ≤ l1E x.1 + (compL2 α : ℤ) * (2 * (4 * l1E x.1)) :=
        add_le_add (le_refl _) hscale
      _ = _ := by push_cast; ring
  · rw [heq]
    have hscale := mul_le_mul_of_nonneg_left (hn1 x)
      (by positivity : (0 : ℤ) ≤ 1 + 6 * (compL2 α : ℤ))
    have hy := hn2 (e1 x)
    simp only [compN]
    push_cast
    nlinarith

end TypedTriangle
