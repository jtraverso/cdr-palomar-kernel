/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license.
Authors: Juan Pablo Traverso Gianini
-/
module

public import CDRBicolour.Latin.ForbiddenCore
public import CDRBicolour.Latin.Recolour

/-!
# Forbidden Latin squares exist (Colbourn–Dinitz–Rosa 1999, Lemma 2.3)

`forbidden_latin`: if every class has at most half of the points, a forbidden Latin square exists.

Construction (CDR, p. 7–8), after rotating the classes so that `C` is the largest:
1. `exists_offdiag`: a Latin square `R` on `A ∪ B` with symbols `C ⊔ X`, `|X| = a + b - c`,
   whose off-diagonal blocks `A × B`, `B × A` avoid `X` (a cyclic subsquare on the smaller of
   `A`, `B` containing `X`, completed by Ryser's theorem);
2. replace `A × A` by a cyclic Latin square on `A`, and the `X`-cells of `B × B` by `B`-symbols
   with an equalized colouring (`exists_equalized`);
3. complete with `forbidden_of_prefix`.
-/

@[expose] public section

namespace CDRBicolour.Latin

open Finset

/-! ### The square with off-diagonal blocks avoiding `X` -/

theorem exists_offdiag {ρ β : Type*} [Fintype ρ] [DecidableEq ρ] [Fintype β] [DecidableEq β]
    (hβ : Fintype.card β = Fintype.card ρ) (D : Finset ρ) (hD : 2 * D.card ≤ Fintype.card ρ)
    (X : Finset β) (hX : X.card ≤ D.card) :
    ∃ R : ρ → ρ → β, IsLatin R ∧ ∀ r g, (r ∈ D ↔ g ∉ D) → R r g ∉ X := by
  classical
  set d := D.card with hd
  rcases Nat.eq_zero_or_pos d with hd0 | hdpos
  · have hX0 : X = ∅ := card_eq_zero.1 (by omega)
    obtain ⟨R, hR, -⟩ := ryser hβ (R := ∅) (K := ∅) (L := fun r _ => Classical.choice
      (Fintype.card_pos_iff.1 (hβ ▸ Fintype.card_pos_iff.2 ⟨r⟩)))
      ⟨by simp, by simp⟩ (fun σ => by simp)
    exact ⟨R, hR, fun r g _ => by rw [hX0]; simp⟩
  · haveI : NeZero d := ⟨hdpos.ne'⟩
    obtain ⟨S, hXS, -, hS⟩ := exists_subsuperset_card_eq (subset_univ X) hX
      (by rw [card_univ, hβ]; omega)
    let eD : D ≃ Fin d := D.equivFin
    let eS : Fin d ≃ S := (S.equivFinOfCardEq hS).symm
    let Q : ρ → ρ → β := fun r g =>
      if h : r ∈ D ∧ g ∈ D then (eS (eD ⟨r, h.1⟩ + eD ⟨g, h.2⟩)).1 else (eS 0).1
    have hQ : ∀ r g (h : r ∈ D ∧ g ∈ D), Q r g = (eS (eD ⟨r, h.1⟩ + eD ⟨g, h.2⟩)).1 :=
      fun r g h => dif_pos h
    have hlat : IsLatinRect D D Q := by
      refine ⟨fun r hr g hg g' hg' h => ?_, fun g hg r hr r' hr' h => ?_⟩
      · rw [hQ r g ⟨hr, hg⟩, hQ r g' ⟨hr, hg'⟩] at h
        have := add_left_cancel (eS.injective (Subtype.ext h))
        exact congrArg Subtype.val (eD.injective this)
      · simp only at h
        rw [hQ r g ⟨hr, hg⟩, hQ r' g ⟨hr', hg⟩] at h
        have := add_right_cancel (eS.injective (Subtype.ext h))
        exact congrArg Subtype.val (eD.injective this)
    obtain ⟨R, hR, hRQ⟩ := ryser hβ hlat (fun σ => by omega)
    refine ⟨R, hR, fun r g hrg ht => ?_⟩
    have htS : R r g ∈ S := hXS ht
    by_cases hr : r ∈ D
    · have hg : g ∉ D := hrg.1 hr
      set k := eS.symm ⟨R r g, htS⟩ - eD ⟨r, hr⟩
      set g' := (eD.symm k).1
      have hg' : g' ∈ D := (eD.symm k).2
      have hk : eD ⟨g', hg'⟩ = k := by show eD (eD.symm k) = k; exact Equiv.apply_symm_apply _ _
      have hval : R r g' = R r g := by
        rw [hRQ r hr g' hg', hQ r g' ⟨hr, hg'⟩, hk,
          show eD ⟨r, hr⟩ + k = eS.symm ⟨R r g, htS⟩ from add_sub_cancel _ _,
          Equiv.apply_symm_apply]
      have := hR.1 r (mem_univ _) (mem_coe.2 (mem_univ _)) (mem_coe.2 (mem_univ _)) hval
      exact hg (this ▸ hg')
    · have hg : g ∈ D := by by_contra hg; exact hr (hrg.2 hg)
      set k := eS.symm ⟨R r g, htS⟩ - eD ⟨g, hg⟩
      set r' := (eD.symm k).1
      have hr' : r' ∈ D := (eD.symm k).2
      have hk : eD ⟨r', hr'⟩ = k := by show eD (eD.symm k) = k; exact Equiv.apply_symm_apply _ _
      have hval : R r' g = R r g := by
        rw [hRQ r' hr' g hg, hQ r' g ⟨hr', hg⟩, hk,
          show k + eD ⟨g, hg⟩ = eS.symm ⟨R r g, htS⟩ from sub_add_cancel _ _,
          Equiv.apply_symm_apply]
      have := hR.2 g (mem_univ _) (mem_coe.2 (mem_univ _)) (mem_coe.2 (mem_univ _)) hval
      exact hr (this ▸ hr')

end CDRBicolour.Latin
