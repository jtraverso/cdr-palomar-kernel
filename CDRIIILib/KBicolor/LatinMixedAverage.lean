/-
Copyright (c) 2026 Juan Pablo Traverso Gianini.
Released under Apache 2.0 license.
Authors: Juan Pablo Traverso Gianini
-/
module

public import CDRIIILib.KBicolor.LatinPackingFrequencies

/-! # A Latin isotopy with bounded total mixed Pasch count

The constants deliberately reuse the general Paper III bounds. They give
an O(n^2) error for a linear-size reserved block, without changing the
profile or the exact target matrix.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false

namespace CDRBicolour.KBicolor.LatinPasch
open Finset Classical TypedTriangle
variable {k n m : ℕ} {lab : Fin n → Fin k} {X Y : Fin k}
variable {r c s : Fin m → Fin n} (h : LatPlace lab X Y r c s)
include h

theorem mixed_mono_left {Q Q' R : Finset (Finset (Fin n))} (hQQ : Q ⊆ Q') (j : ℕ) :
    Pasch.mixedConfigurations Q R j ∅ ⊆ Pasch.mixedConfigurations Q' R j ∅ := by
  intro S hS
  obtain ⟨hc, hout, hcard, hempty⟩ := Pasch.mixedConfigurations_data hS
  obtain ⟨hsub, hfour, hp⟩ := Pasch.mem_configurations.mp hc
  apply mem_filter.mpr
  refine ⟨Pasch.mem_configurations.mpr ⟨?_,hfour,hp⟩,hcard,hempty⟩
  intro T hT
  rcases mem_union.mp (hsub hT) with hQ | hR
  · exact mem_union_left _ (hQQ hQ)
  · exact mem_union_right _ hR

theorem card_as_indicator_sum {α : Type*} [DecidableEq α] (S T : Finset α) (hST : S ⊆ T) :
    (S.card : ℝ) = ∑ x ∈ T, if x ∈ S then (1 : ℝ) else 0 := by
  have hf : T.filter (fun x => x ∈ S) = S := by
    ext x
    simp only [mem_filter]
    exact ⟨fun hx => hx.2, fun hx => ⟨hST hx,hx⟩⟩
  rw [← sum_filter, hf]
  simp

theorem mixed_frequency_sum (l : Fin m → Fin m → Fin m) (R : Finset (Finset (Fin n)))
    (j : ℕ) (a : ℝ)
    (hfreq : ∀ S ∈ Pasch.mixedConfigurations (latinUniverse r c s) R j ∅,
      a * (∑ ρ : Equiv.Perm (Fin m), ∑ σ : Equiv.Perm (Fin m),
        if S ∈ Pasch.mixedConfigurations (latPackK r c s (isotopyValue l ρ σ)) R j ∅
          then (1 : ℝ) else 0) = (Fintype.card (Equiv.Perm (Fin m)) : ℝ)^2) :
    a * (∑ ρ : Equiv.Perm (Fin m), ∑ σ : Equiv.Perm (Fin m),
      (#(Pasch.mixedConfigurations (latPackK r c s (isotopyValue l ρ σ)) R j ∅) : ℝ)) =
      (Fintype.card (Equiv.Perm (Fin m)) : ℝ)^2 *
        #(Pasch.mixedConfigurations (latinUniverse r c s) R j ∅) := by
  let C := Pasch.mixedConfigurations (latinUniverse r c s) R j ∅
  have hcard : ∀ ρ σ : Equiv.Perm (Fin m),
      (#(Pasch.mixedConfigurations (latPackK r c s (isotopyValue l ρ σ)) R j ∅) : ℝ) =
        ∑ S ∈ C, if S ∈ Pasch.mixedConfigurations (latPackK r c s (isotopyValue l ρ σ)) R j ∅
          then (1 : ℝ) else 0 := by
    intro ρ σ
    exact card_as_indicator_sum h _ C (mixed_mono_left h (packing_subset_universe h _) j)
  simp_rw [hcard]
  have hswap : (∑ ρ : Equiv.Perm (Fin m), ∑ σ : Equiv.Perm (Fin m), ∑ S ∈ C,
      if S ∈ Pasch.mixedConfigurations (latPackK r c s (isotopyValue l ρ σ)) R j ∅
        then (1 : ℝ) else 0) =
      ∑ S ∈ C, ∑ ρ : Equiv.Perm (Fin m), ∑ σ : Equiv.Perm (Fin m),
      if S ∈ Pasch.mixedConfigurations (latPackK r c s (isotopyValue l ρ σ)) R j ∅
        then (1 : ℝ) else 0 := by
    calc
      _ = ∑ ρ : Equiv.Perm (Fin m), ∑ S ∈ C, ∑ σ : Equiv.Perm (Fin m),
          if S ∈ Pasch.mixedConfigurations (latPackK r c s (isotopyValue l ρ σ)) R j ∅
            then (1 : ℝ) else 0 := sum_congr rfl (fun _ _ => sum_comm)
      _ = _ := sum_comm
  rw [hswap, mul_sum]
  rw [sum_congr rfl (fun S hS => hfreq S hS)]
  simp [mul_comm]

def mixedBudget (n m : ℕ) : ℝ :=
  27*(n : ℝ)^3/m + 6*(n : ℝ)^4/((m*(m-1) : ℕ) : ℝ)

theorem exists_isotopy_small_mixed (l : Fin m → Fin m → Fin m) (hl : _root_.STS.IsLatin l)
    (hm : 2 ≤ m) (R : Finset (Finset (Fin n)))
    (hR : Pasch.PairCodegreeBound R 1) (htrip : ∀ T ∈ R, T.card = 3) (hcard : R.card ≤ n^2) :
    ∃ ρ σ : Equiv.Perm (Fin m),
      (#(Pasch.mixedConfigurations (latPackK r c s (isotopyValue l ρ σ)) R 1 ∅) : ℝ) +
        #(Pasch.mixedConfigurations (latPackK r c s (isotopyValue l ρ σ)) R 2 ∅) ≤ mixedBudget n m := by
  let P := Equiv.Perm (Fin m)
  let G : ℝ := (Fintype.card P : ℝ)^2
  have hG : 0 ≤ G := sq_nonneg _
  have hmR : (0 : ℝ) < m := by exact_mod_cast (show 0 < m by omega)
  have hD : (0 : ℝ) < ((m*(m-1) : ℕ) : ℝ) := by
    exact_mod_cast Nat.mul_pos (show 0 < m by omega) (show 0 < m-1 by omega)
  have h₁ := mixed_frequency_sum h l R 1 m (fun S hS => mixed_single_frequency h l R hS)
  have h₂ := mixed_frequency_sum h l R 2 (m*(m-1) : ℕ) (fun S hS => mixed_pair_frequency h l hl R hS)
  obtain ⟨hb₁, hb₂⟩ := mixed_candidate_bounds (latinUniverse r c s) R hR htrip
    (by simpa only [Fintype.card_fin] using hcard)
  have b₁ : (#(Pasch.mixedConfigurations (latinUniverse r c s) R 1 ∅) : ℝ) ≤ 27*(n : ℝ)^3 := by
    exact_mod_cast (show #(Pasch.mixedConfigurations (latinUniverse r c s) R 1 ∅) ≤ 27*n^3 by
      simpa only [Fintype.card_fin] using hb₁)
  have b₂ : (#(Pasch.mixedConfigurations (latinUniverse r c s) R 2 ∅) : ℝ) ≤ 6*(n : ℝ)^4 := by
    exact_mod_cast (show #(Pasch.mixedConfigurations (latinUniverse r c s) R 2 ∅) ≤ 6*n^4 by
      simpa only [Fintype.card_fin] using hb₂)
  have hsum₁ : (∑ ρ : P, ∑ σ : P,
      (#(Pasch.mixedConfigurations (latPackK r c s (isotopyValue l ρ σ)) R 1 ∅) : ℝ)) ≤
      G*(27*(n : ℝ)^3/m) := by
    rw [← mul_div_assoc]
    apply (le_div_iff₀ hmR).mpr
    have hh := mul_le_mul_of_nonneg_left b₁ hG
    nlinarith only [h₁,hh]
  have hsum₂ : (∑ ρ : P, ∑ σ : P,
      (#(Pasch.mixedConfigurations (latPackK r c s (isotopyValue l ρ σ)) R 2 ∅) : ℝ)) ≤
      G*(6*(n : ℝ)^4/((m*(m-1) : ℕ) : ℝ)) := by
    rw [← mul_div_assoc]
    apply (le_div_iff₀ hD).mpr
    have hh := mul_le_mul_of_nonneg_left b₂ hG
    nlinarith only [h₂,hh]
  let cost : P×P → ℝ := fun p =>
    (#(Pasch.mixedConfigurations (latPackK r c s (isotopyValue l p.1 p.2)) R 1 ∅) : ℝ) +
      #(Pasch.mixedConfigurations (latPackK r c s (isotopyValue l p.1 p.2)) R 2 ∅)
  have hcost : (∑ p : P×P, cost p) ≤ (Fintype.card (P×P) : ℝ)*mixedBudget n m := by
    simp only [cost, Fintype.sum_prod_type, sum_add_distrib,
      Fintype.card_prod, Nat.cast_mul, mixedBudget]
    dsimp [G] at hsum₁ hsum₂
    push_cast at hsum₁ hsum₂
    nlinarith only [hsum₁,hsum₂]
  obtain ⟨⟨ρ,σ⟩,hh⟩ := exists_cost_le_of_sum_le cost (mixedBudget n m) hcost
  exact ⟨ρ,σ,hh⟩

end CDRBicolour.KBicolor.LatinPasch
