/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license.
Authors: Juan Pablo Traverso Gianini
-/
module

public import CDRBicolour.Absorption.PaschSeed

/-!
# Octahedral Pasch configurations on `U × V × W`

For `u₁ ∈ U⁺, u₂ ∈ U⁻, v₁ ∈ V⁺, v₂ ∈ V⁻, w₁ ∈ W⁺, w₂ ∈ W⁻` (the halves of the parts, `m`
points each), the four triangles `u₁v₁w₁, u₁v₂w₂, u₂v₁w₂, u₂v₂w₁` form an allowed Pasch
configuration on which `∏ δ = 1`.  These `m⁶` configurations are distinct, and every allowed
Pasch configuration has `∏ δ ≥ 0`, so `∑_S ∏_{T∈S} δ T ≥ m⁶` (`family_bound`).
-/

@[expose] public section

namespace CDRBicolour.Absorption.PaschSeed

open Finset TypedTriangle CDRBicolour.Prefix CDRBicolour.Absorption CDRBicolour.Absorption.PaschTools

/-- The octahedral Pasch configuration on `Fin 6`, with antipodal pairs `{0,1}, {2,3}, {4,5}`. -/
def S6 : Finset (Finset (Fin 6)) := {{0, 2, 4}, {0, 3, 5}, {1, 2, 5}, {1, 3, 4}}

theorem isPasch_S6 : Pasch.IsPasch S6 := by
  refine ⟨by decide, by decide, by decide, by decide, ?_⟩
  intro A hA B hB hAB
  have key : ∀ A ∈ S6, ∀ B ∈ S6, A ≠ B → #(A ∩ B) ≤ 1 := by decide
  exact key A (mem_coe.mp hA) B (mem_coe.mp hB) hAB

/-- Parts of the six coordinates. -/
def P6 : Fin 6 → ℕ := ![1, 1, 2, 2, 3, 3]

/-- Labels of the six coordinates. -/
def L6 : Fin 6 → Fin 3 := ![0, 0, 0, 0, 1, 1]

theorem S6_pattern : ∀ T0 ∈ S6, T0.val.map P6 = ({1, 2, 3} : Multiset ℕ) := by decide

theorem S6_labels : ∀ T0 ∈ S6, Multiset.card (T0.val.map L6) = 3 ∧
    (T0.val.map L6).toFinset.card = 2 := by decide

theorem S6_cover : ∀ s : Fin 6, ∃ T0 ∈ S6, s ∈ T0 := by decide

variable {a b c m : ℕ}

/-- Start of the interval of coordinate `r`. -/
def lo6 (a m : ℕ) : Fin 6 → ℕ := ![0, m, 2 * m, 3 * m, a, a + m]

/-- The interval of coordinate `r`. -/
def I6 (a m : ℕ) (r : Fin 6) : Finset (Fin (a + b + c)) :=
  univ.filter fun i => lo6 a m r ≤ i.val ∧ i.val < lo6 a m r + m

theorem card_interval {n lo m : ℕ} (h : lo + m ≤ n) :
    #(univ.filter fun i : Fin n => lo ≤ i.val ∧ i.val < lo + m) = m := by
  have : (univ.filter fun i : Fin n => lo ≤ i.val ∧ i.val < lo + m).map Fin.valEmbedding =
      Ico lo (lo + m) := by
    ext v
    simp only [mem_map, mem_filter, mem_univ, true_and, Fin.valEmbedding_apply, mem_Ico]
    constructor
    · rintro ⟨i, hi, rfl⟩; exact hi
    · intro hv; exact ⟨⟨v, by omega⟩, hv, rfl⟩
  rw [← card_map, this, Nat.card_Ico]; omega

theorem card_I6 (H : Hyp a b m) (r : Fin 6) : #(I6 (b := b) (c := c) a m r) = m := by
  have := H.ha; have := H.hb
  unfold I6
  apply card_interval
  fin_cases r <;> simp [lo6] <;> omega

/-- The index set: one point in each half-part. -/
def Idx (a m : ℕ) : Finset (Fin 6 → Fin (a + b + c)) :=
  Fintype.piFinset fun r => I6 (b := b) (c := c) a m r

theorem card_Idx (H : Hyp a b m) : #(Idx (b := b) (c := c) a m) = m ^ 6 := by
  rw [Idx, Fintype.card_piFinset, prod_congr rfl (fun r _ => card_I6 H r), prod_const,
    card_univ, Fintype.card_fin]

section Coords

variable (H : Hyp a b m) {x : Fin 6 → Fin (a + b + c)} (hx : x ∈ Idx (b := b) (c := c) a m)
include H hx

theorem coord_range (r : Fin 6) : lo6 a m r ≤ (x r).val ∧ (x r).val < lo6 a m r + m := by
  have := Fintype.mem_piFinset.mp hx r
  exact (mem_filter.mp this).2

theorem ptv_coord (r : Fin 6) : ptv a m (x r).val = P6 r := by
  have h := coord_range H hx r
  have := H.ha; have := H.pos
  fin_cases r <;> simp [lo6, P6, ptv] at h ⊢ <;> split_ifs <;> omega

theorem col3_coord (r : Fin 6) : col3 a b c (x r) = L6 r := by
  have h := coord_range H hx r
  have := H.ha; have := H.hb
  fin_cases r <;> simp [lo6, L6, col3] at h ⊢ <;> split_ifs <;> first | rfl | omega

theorem coord_inj : Function.Injective x := by
  intro r s hrs
  have hr := coord_range H hx r
  have hs := coord_range H hx s
  rw [hrs] at hr
  have := H.ha; have := H.pos
  fin_cases r <;> fin_cases s <;> simp [lo6] at hr hs ⊢ <;> omega

end Coords

/-- The octahedral configuration of a tuple. -/
def Φ (x : Fin 6 → Fin (a + b + c)) : Finset (Finset (Fin (a + b + c))) :=
  S6.image fun T0 => T0.image x

section Family

variable (H : Hyp a b m) {x : Fin 6 → Fin (a + b + c)} (hx : x ∈ Idx (b := b) (c := c) a m)
include H hx

theorem Φ_eq_map :
    Φ x = S6.map (mapEmbedding ⟨x, coord_inj H hx⟩).toEmbedding := by
  unfold Φ
  rw [map_eq_image]
  refine image_congr fun T0 _ => ?_
  simp only [RelEmbedding.coe_toEmbedding, mapEmbedding_apply, map_eq_image]
  rfl

theorem Φ_mem_conf : Φ x ∈ Pasch.configurations (allowed (cdrHost a b c) cdrF) := by
  classical
  rw [Φ_eq_map H hx, Pasch.mem_configurations]
  refine ⟨fun T hT => ?_, by rw [card_map]; decide, isPasch_map _ isPasch_S6⟩
  obtain ⟨T0, hT0, rfl⟩ := mem_map.mp hT
  simp only [RelEmbedding.coe_toEmbedding, mapEmbedding_apply]
  unfold allowed
  refine mem_filter.mpr ⟨mem_univ _, ?_, fun u _ v _ huv => huv, ?_⟩
  · rw [card_map]; exact isPasch_S6.2.1 T0 hT0
  · show (T0.map ⟨x, coord_inj H hx⟩).val.map (col3 a b c) ∈ cdrF
    rw [map_val, Multiset.map_map]
    have : Multiset.map (col3 a b c ∘ ⇑(⟨x, coord_inj H hx⟩ : Fin 6 ↪ Fin (a + b + c))) T0.val =
        T0.val.map L6 := Multiset.map_congr rfl fun r _ => col3_coord H hx r
    rw [this]
    exact S6_labels T0 hT0

theorem prod_δ_Φ : ∏ T ∈ Φ x, δ a m T = 1 := by
  rw [Φ_eq_map H hx, prod_map]
  have hT : ∀ T0 ∈ S6, δ a m ((mapEmbedding ⟨x, coord_inj H hx⟩).toEmbedding T0) =
      ∏ p ∈ T0, sgnv a m (x p).val := by
    intro T0 hT0
    simp only [RelEmbedding.coe_toEmbedding, mapEmbedding_apply]
    unfold δ
    have hpat : (T0.map ⟨x, coord_inj H hx⟩).val.map (fun i => ptv a m i.val) =
        ({1, 2, 3} : Multiset ℕ) := by
      rw [map_val, Multiset.map_map, ← S6_pattern T0 hT0]
      exact Multiset.map_congr rfl fun r _ => ptv_coord H hx r
    rw [if_pos hpat, prod_map]
    rfl
  rw [prod_congr rfl hT, prod_prod_points]
  refine prod_eq_one fun p hp => ?_
  rw [isPasch_S6.2.2.2.1 p hp]
  apply sgnv_sq
  rw [ptv_coord H hx p]
  fin_cases p <;> simp [P6]

theorem mem_union_Φ (z : Fin (a + b + c)) : z ∈ (Φ x).biUnion id ↔ ∃ s, x s = z := by
  simp only [Φ, mem_biUnion, mem_image, id]
  constructor
  · rintro ⟨_, ⟨T0, _, rfl⟩, hz⟩
    obtain ⟨s, _, rfl⟩ := mem_image.mp hz
    exact ⟨s, rfl⟩
  · rintro ⟨s, rfl⟩
    obtain ⟨T0, hT0, hs⟩ := S6_cover s
    exact ⟨T0.image x, ⟨T0, hT0, rfl⟩, mem_image_of_mem x hs⟩

end Family

theorem Φ_injOn (H : Hyp a b m) :
    Set.InjOn Φ (↑(Idx (b := b) (c := c) a m) : Set (Fin 6 → Fin (a + b + c))) := by
  intro x hx y hy hxy
  funext r
  have hyr : y r ∈ (Φ x).biUnion id := by
    rw [hxy, mem_union_Φ H hy]; exact ⟨r, rfl⟩
  obtain ⟨s, hs⟩ := (mem_union_Φ H hx _).mp hyr
  have h1 := coord_range H hx s
  have h2 := coord_range H hy r
  rw [← hs] at h2
  have : s = r := by
    have := H.ha; have := H.pos
    fin_cases s <;> fin_cases r <;> simp [lo6] at h1 h2 ⊢ <;> omega
  rw [← hs, this]

/-- **Lower bound for the leading coefficient.** -/
theorem family_bound (H : Hyp a b m) :
    (m : ℝ) ^ 6 ≤ ∑ S ∈ Pasch.configurations (allowed (cdrHost a b c) cdrF), ∏ T ∈ S, δ a m T := by
  have hsub : (Idx (b := b) (c := c) a m).image Φ ⊆
      Pasch.configurations (allowed (cdrHost a b c) cdrF) := by
    intro S hS
    obtain ⟨x, hx, rfl⟩ := mem_image.mp hS
    exact Φ_mem_conf H hx
  have hnn : ∀ S ∈ Pasch.configurations (allowed (cdrHost a b c) cdrF), 0 ≤ ∏ T ∈ S, δ a m T := by
    intro S hS
    rw [Pasch.mem_configurations] at hS
    exact prod_nonneg_of_pasch hS.2.2 (fun p => sgnv a m p.val) _ fun T _ => δ_cases T
  calc (m : ℝ) ^ 6 = ∑ S ∈ (Idx (b := b) (c := c) a m).image Φ, ∏ T ∈ S, δ a m T := by
        rw [sum_image (Φ_injOn H), sum_congr rfl (fun x hx => prod_δ_Φ H hx), sum_const,
          card_Idx H, nsmul_eq_mul, mul_one]
        push_cast; ring
    _ ≤ _ := sum_le_sum_of_subset_of_nonneg hsub fun S hS _ => hnn S hS

end CDRBicolour.Absorption.PaschSeed
