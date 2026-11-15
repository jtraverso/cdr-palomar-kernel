/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license.
Authors: Juan Pablo Traverso Gianini
-/
module

public import CDRIIILib.KBicolor.Wilson.Reserve
public import CDRIIILib.KBicolor.Wilson.Placement

/-!
# Exact reserve sizes and quantitative slack in each colour

An embedded setup uses exactly `g * m_X * t` points of colour X. Its complement
therefore has `c_X - g*m_X*t` points in that colour, independently of the chosen
embedding. An approximation error `ρδ/4` and covered fraction at most `1-ρ/2`
leave at least `ρδn/4` reserved points of every colour.
-/

@[expose] public section

noncomputable section

namespace CDRBicolour.KBicolor.Wilson

open Finset

variable {A : Type*} [Fintype A] [DecidableEq A] {k n g t : ℕ}
variable {lab : Fin n → Fin k} {κ : A → Fin k}

theorem used_class_card (h : Setup lab κ g t) (X : Fin k) :
    #((univ.image h.embed).filter fun v => lab v = X) = g * Hilton.csize κ X * t := by
  rw [filter_image]
  have hf : (univ.filter fun u : Fin g × A × Fin t => lab (h.embed u) = X) =
      (univ.filter fun u => κ u.2.1 = X) := by
    ext u
    simp only [mem_filter, mem_univ, true_and]
    rw [h.label u.1 u.2.1 u.2.2]
  rw [hf, card_image_of_injective _ h.embed.injective]
  rw [← Fintype.card_subtype]
  exact card_slot_fibre κ X

/-- Exact conservation of the points of each colour. -/
theorem reserve_class_card (h : Setup lab κ g t) (X : Fin k) :
    #((reserve h).filter fun v => lab v = X) + g * Hilton.csize κ X * t = ksz lab X := by
  have hset : (reserve h).filter (fun v => lab v = X) =
      (univ.filter fun v => lab v = X) \ ((univ.image h.embed).filter fun v => lab v = X) := by
    ext v
    simp only [reserve, mem_filter, mem_sdiff, mem_univ, true_and]
    tauto
  have hsub : ((univ.image h.embed).filter fun v => lab v = X) ⊆
      (univ.filter fun v => lab v = X) := by
    intro v hv
    exact mem_filter.mpr ⟨mem_univ _, (mem_filter.mp hv).2⟩
  rw [hset, ← used_class_card h X]
  exact card_sdiff_add_card_eq_card hsub

/-- Slack from approximating proportions while reserving a fraction of every class. -/
theorem proportional_reserve {N m c n g t : ℕ} {δ ρ : ℝ}
    (hN : 0 < N) (hn : 0 < n) (hδ : 0 ≤ δ) (hρ : 0 ≤ ρ) (hρ1 : ρ ≤ 1)
    (hc : δ * n ≤ c)
    (hclose : (m : ℝ) / N ≤ (c : ℝ) / n + ρ * δ / 4)
    (hsize : (g : ℝ) * N * t ≤ (1 - ρ / 2) * n) :
    ρ * δ / 4 * n ≤ (c : ℝ) - (g : ℝ) * m * t := by
  have hNR : (0 : ℝ) < N := by exact_mod_cast hN
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hratio : 0 ≤ (m : ℝ) / N := by positivity
  have hbound : (g : ℝ) * m * t ≤ (1 - ρ / 2) * ((c : ℝ) + ρ * δ / 4 * n) := calc
    _ = ((g : ℝ) * N * t) * ((m : ℝ) / N) := by field_simp
    _ ≤ ((1 - ρ / 2) * n) * ((c : ℝ) / n + ρ * δ / 4) :=
      mul_le_mul hsize hclose hratio (mul_nonneg (by linarith) hnR.le)
    _ = _ := by field_simp
  have hscaled := mul_le_mul_of_nonneg_left hc hρ
  nlinarith [mul_nonneg hρ (mul_nonneg hρ (mul_nonneg hδ hnR.le))]

end CDRBicolour.KBicolor.Wilson
