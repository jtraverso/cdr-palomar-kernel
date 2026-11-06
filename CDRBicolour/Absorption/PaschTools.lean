/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license.
Authors: Juan Pablo Traverso Gianini
-/
module

public import RequestProject.TypedTriangle.PaschStatistics

/-!
# Tools for separating Pasch targets

* `isPasch_map`: Pasch configurations are transported by injective maps of points;
* `prod_nonneg_of_pasch`: if a triangle weight is a product of point weights on every triangle
  of a Pasch configuration, the product over the configuration is a product of squares;
* `even_quartic`: an even function of the form `∑_S ∏_{T ∈ S} (x T + t · y T)` over 4-sets is
  `F 0 + A₂ t² + (∑_S ∏_{T∈S} y T) t⁴`;
* `separated_values`: a quadratic `A₀ + A₂ s + A₄ s²` with `A₄ > 0` takes `K` pairwise
  `A₄ g²`-separated values on the grid `{0, g, …, 2K g}`.
-/

@[expose] public section

namespace CDRBicolour.Absorption.PaschTools

open Finset TypedTriangle

/-! ### Transport of Pasch configurations -/

section Transport

variable {V W : Type*} [DecidableEq V] [DecidableEq W]

theorem isPasch_map (f : V ↪ W) {S : Finset (Finset V)} (hS : Pasch.IsPasch S) :
    Pasch.IsPasch (S.map (mapEmbedding f).toEmbedding) := by
  obtain ⟨h4, h3, h6, h2, hint⟩ := hS
  have hU : (S.map (mapEmbedding f).toEmbedding).biUnion id = (S.biUnion id).map f := by
    ext w
    simp only [mem_biUnion, mem_map, id, RelEmbedding.coe_toEmbedding, mapEmbedding_apply]
    constructor
    · rintro ⟨_, ⟨T, hT, rfl⟩, hw⟩
      obtain ⟨v, hv, rfl⟩ := mem_map.mp hw
      exact ⟨v, ⟨T, hT, hv⟩, rfl⟩
    · rintro ⟨v, ⟨T, hT, hv⟩, rfl⟩
      exact ⟨T.map f, ⟨T, hT, rfl⟩, mem_map_of_mem f hv⟩
  refine ⟨by rw [card_map, h4], ?_, ?_, ?_, ?_⟩
  · intro T hT
    obtain ⟨T0, hT0, rfl⟩ := mem_map.mp hT
    simp [h3 T0 hT0]
  · rw [hU, card_map, h6]
  · intro w hw
    rw [hU] at hw
    obtain ⟨v, hv, rfl⟩ := mem_map.mp hw
    rw [← h2 v hv, filter_map, card_map]
    congr 1
    refine filter_congr fun T _ => ?_
    simp [Function.comp, mem_map' f]
  · intro A hA B hB hAB
    obtain ⟨A0, hA0, rfl⟩ := mem_map.mp (mem_coe.mp hA)
    obtain ⟨B0, hB0, rfl⟩ := mem_map.mp (mem_coe.mp hB)
    have hne : A0 ≠ B0 := fun h => hAB (h ▸ rfl)
    simp only [RelEmbedding.coe_toEmbedding, mapEmbedding_apply]
    rw [← map_inter, card_map]
    exact hint (mem_coe.mpr hA0) (mem_coe.mpr hB0) hne

theorem map_map_equiv (e : V ≃ W) (S : Finset (Finset V)) :
    (S.map (mapEmbedding e.toEmbedding).toEmbedding).map
      (mapEmbedding e.symm.toEmbedding).toEmbedding = S := by
  rw [map_map]
  convert map_refl (s := S)
  ext T x
  simp [mapEmbedding_apply, Finset.mem_map_equiv]

theorem mem_conf_map (e : V ≃ W) {D : Finset (Finset V)} {S : Finset (Finset V)}
    (hS : S ∈ Pasch.configurations D) :
    S.map (mapEmbedding e.toEmbedding).toEmbedding ∈
      Pasch.configurations (D.map (mapEmbedding e.toEmbedding).toEmbedding) := by
  rw [Pasch.mem_configurations] at hS ⊢
  exact ⟨map_subset_map.mpr hS.1, by rw [card_map, hS.2.1], isPasch_map _ hS.2.2⟩

/-- **The number of Pasch configurations is invariant under relabelling the points.** -/
theorem count_map_equiv (e : V ≃ W) (D : Finset (Finset V)) :
    Pasch.count (D.map (mapEmbedding e.toEmbedding).toEmbedding) = Pasch.count D := by
  unfold Pasch.count
  symm
  refine card_nbij' (fun S => S.map (mapEmbedding e.toEmbedding).toEmbedding)
    (fun S => S.map (mapEmbedding e.symm.toEmbedding).toEmbedding)
    (fun S hS => mem_conf_map e hS) (fun S hS => ?_) (fun S _ => map_map_equiv e S)
    (fun S _ => by simpa using map_map_equiv e.symm S)
  have := mem_conf_map e.symm hS
  rwa [map_map_equiv e D] at this

end Transport

/-! ### Products over a Pasch configuration -/

section Products

variable {V : Type*} [DecidableEq V]

/-- A product over the triangles of the point products is a product over points with
multiplicity. -/
theorem prod_prod_points (S : Finset (Finset V)) (f : V → ℝ) :
    ∏ T ∈ S, ∏ p ∈ T, f p = ∏ p ∈ S.biUnion id, f p ^ #(S.filter fun T => p ∈ T) := by
  have h1 : ∀ T ∈ S, ∏ p ∈ T, f p = ∏ p ∈ S.biUnion id, (if p ∈ T then f p else 1) := by
    intro T hT
    rw [prod_ite_mem]
    congr 1
    ext p
    simp only [mem_inter, mem_biUnion, id]
    exact ⟨fun hp => ⟨⟨T, hT, hp⟩, hp⟩, fun h => h.2⟩
  rw [prod_congr rfl h1, prod_comm]
  refine prod_congr rfl fun p _ => ?_
  rw [← prod_filter, prod_const]

/-- If every triangle weight of a Pasch configuration is either `0` somewhere or the product of
point weights everywhere, the product over the configuration is nonnegative. -/
theorem prod_nonneg_of_pasch {S : Finset (Finset V)} (hS : Pasch.IsPasch S) (f : V → ℝ)
    (δ : Finset V → ℝ) (hδ : ∀ T ∈ S, δ T = 0 ∨ δ T = ∏ p ∈ T, f p) :
    0 ≤ ∏ T ∈ S, δ T := by
  by_cases h0 : ∃ T ∈ S, δ T = 0
  · obtain ⟨T, hT, hT0⟩ := h0
    rw [prod_eq_zero hT hT0]
  · push_neg at h0
    have : ∏ T ∈ S, δ T = ∏ T ∈ S, ∏ p ∈ T, f p :=
      prod_congr rfl fun T hT => (hδ T hT).resolve_left (h0 T hT)
    rw [this, prod_prod_points]
    refine prod_nonneg fun p hp => ?_
    rw [hS.2.2.2.1 p hp]
    exact sq_nonneg _

end Products

/-! ### Even quartic expansions -/

section Quartic

variable {ι : Type*} [DecidableEq ι]

theorem prod_add_expand (S : Finset ι) (x y : ι → ℝ) (t : ℝ) :
    ∏ T ∈ S, (x T + t * y T) =
      ∑ R ∈ S.powerset, t ^ #R * ((∏ T ∈ R, y T) * ∏ T ∈ S \ R, x T) := by
  simp_rw [add_comm (x _)]
  rw [prod_add]
  refine sum_congr rfl fun R _ => ?_
  rw [prod_mul_distrib, prod_const]
  ring

/-- The coefficient of `t^k`. -/
noncomputable def coef (C : Finset (Finset ι)) (x y : ι → ℝ) (k : ℕ) : ℝ :=
  ∑ S ∈ C, ∑ R ∈ S.powerset.filter (fun R => #R = k), (∏ T ∈ R, y T) * ∏ T ∈ S \ R, x T

theorem quartic_expand (C : Finset (Finset ι)) (hC : ∀ S ∈ C, #S = 4) (x y : ι → ℝ) (t : ℝ) :
    ∑ S ∈ C, ∏ T ∈ S, (x T + t * y T) = ∑ k ∈ range 5, t ^ k * coef C x y k := by
  simp_rw [prod_add_expand, coef, mul_sum]
  rw [sum_comm]
  refine sum_congr rfl fun S hS => ?_
  rw [← sum_fiberwise_of_maps_to (g := fun R => #R) (t := range 5)]
  · refine sum_congr rfl fun k _ => ?_
    refine sum_congr rfl fun R hR => ?_
    rw [(mem_filter.mp hR).2]
  · intro R hR
    rw [mem_range, Nat.lt_succ_iff, ← hC S hS]
    exact card_le_card (mem_powerset.mp hR)

theorem coef_four (C : Finset (Finset ι)) (hC : ∀ S ∈ C, #S = 4) (x y : ι → ℝ) :
    coef C x y 4 = ∑ S ∈ C, ∏ T ∈ S, y T := by
  unfold coef
  refine sum_congr rfl fun S hS => ?_
  have : S.powerset.filter (fun R => #R = 4) = {S} := by
    ext R
    simp only [mem_filter, mem_powerset, mem_singleton]
    constructor
    · rintro ⟨hRS, hR⟩
      exact eq_of_subset_of_card_le hRS (by rw [hR, hC S hS])
    · intro h
      rw [h]
      exact ⟨subset_rfl, hC S hS⟩
  rw [this, sum_singleton, sdiff_self, bot_eq_empty, prod_empty, mul_one]

/-- **Even quartics.** -/
theorem even_quartic (C : Finset (Finset ι)) (hC : ∀ S ∈ C, #S = 4) (x y : ι → ℝ)
    (heven : ∀ t : ℝ, ∑ S ∈ C, ∏ T ∈ S, (x T + t * y T) =
      ∑ S ∈ C, ∏ T ∈ S, (x T + (-t) * y T)) :
    ∃ A₂ : ℝ, ∀ t : ℝ, ∑ S ∈ C, ∏ T ∈ S, (x T + t * y T) =
      (∑ S ∈ C, ∏ T ∈ S, (x T + 0 * y T)) + A₂ * t ^ 2 + (∑ S ∈ C, ∏ T ∈ S, y T) * t ^ 4 := by
  have hexp := quartic_expand C hC x y
  have e1 := heven 1
  have e2 := heven 2
  rw [hexp, hexp] at e1 e2
  simp only [sum_range_succ, sum_range_zero] at e1 e2
  have h1 : coef C x y 1 = 0 := by nlinarith
  have h3 : coef C x y 3 = 0 := by nlinarith
  refine ⟨coef C x y 2, fun t => ?_⟩
  rw [hexp, hexp, ← coef_four C hC x y]
  simp only [sum_range_succ, sum_range_zero, h1, h3]
  ring

end Quartic

/-! ### Separated values of a quadratic -/

/-- Among the grid points `0, g, …, 2K g`, `K` of them give pairwise `A₄ g²`-separated values of
`A₀ + A₂ s + A₄ s²`. -/
theorem separated_values (A₀ A₂ A₄ g : ℝ) (hA : 0 < A₄) (hg : 0 < g) (K : ℕ) :
    ∃ s : Fin K → ℝ, (∀ i, 0 ≤ s i ∧ s i ≤ 2 * K * g) ∧
      ∀ i j, i ≠ j → A₄ * g ^ 2 ≤
        |(A₀ + A₂ * s i + A₄ * s i ^ 2) - (A₀ + A₂ * s j + A₄ * s j ^ 2)| := by
  set m : ℝ := -A₂ / (2 * A₄) with hm
  have hA₂ : A₂ = -2 * A₄ * m := by rw [hm]; field_simp
  set I := range (2 * K + 1)
  set L := I.filter fun i : ℕ => m + g / 2 ≤ i * g
  set R := I.filter fun i : ℕ => (i : ℝ) * g ≤ m - g / 2
  set M := I.filter fun i : ℕ => ¬ (m + g / 2 ≤ i * g) ∧ ¬ ((i : ℝ) * g ≤ m - g / 2)
  have hM : #M ≤ 1 := by
    rw [card_le_one]
    intro i hi j hj
    simp only [M, mem_filter, not_le] at hi hj
    by_contra hne
    rcases lt_or_gt_of_ne hne with h | h
    · have : (i : ℝ) + 1 ≤ j := by exact_mod_cast h
      nlinarith
    · have : (j : ℝ) + 1 ≤ i := by exact_mod_cast h
      nlinarith
  have hsplit : #I = #L + #R + #M := by
    have h1 := card_filter_add_card_filter_not (s := I) (p := fun i : ℕ => m + g / 2 ≤ i * g)
    have h2 := card_filter_add_card_filter_not
      (s := I.filter fun i : ℕ => ¬ (m + g / 2 ≤ i * g)) (p := fun i : ℕ => (i : ℝ) * g ≤ m - g / 2)
    rw [filter_filter, filter_filter] at h2
    have hR : (I.filter fun i : ℕ => ¬ (m + g / 2 ≤ i * g) ∧ (i : ℝ) * g ≤ m - g / 2) = R := by
      refine filter_congr fun i _ => ⟨fun h => h.2, fun h => ⟨fun h' => ?_, h⟩⟩
      linarith
    rw [hR] at h2
    have hMeq : (I.filter fun i : ℕ => ¬ (m + g / 2 ≤ i * g) ∧ ¬ ((i : ℝ) * g ≤ m - g / 2)) = M :=
      rfl
    rw [hMeq] at h2
    have hLeq : (I.filter fun i : ℕ => m + g / 2 ≤ i * g) = L := rfl
    rw [hLeq] at h1
    omega
  have hI : #I = 2 * K + 1 := card_range _
  -- one side has at least `K` points
  have hside : ∃ J ⊆ I, #J = K ∧
      ((∀ i ∈ J, m + g / 2 ≤ (i : ℝ) * g) ∨ (∀ i ∈ J, (i : ℝ) * g ≤ m - g / 2)) := by
    by_cases hL : K ≤ #L
    · obtain ⟨J, hJ, hJc⟩ := exists_subset_card_eq hL
      exact ⟨J, hJ.trans (filter_subset _ _), hJc, Or.inl fun i hi => (mem_filter.mp (hJ hi)).2⟩
    · have hR : K ≤ #R := by omega
      obtain ⟨J, hJ, hJc⟩ := exists_subset_card_eq hR
      exact ⟨J, hJ.trans (filter_subset _ _), hJc, Or.inr fun i hi => (mem_filter.mp (hJ hi)).2⟩
  obtain ⟨J, hJI, hJc, hJside⟩ := hside
  let e := J.orderEmbOfFin hJc
  refine ⟨fun i => (e i : ℝ) * g, fun i => ⟨by positivity, ?_⟩, fun i j hij => ?_⟩
  · have hi : e i ∈ I := hJI (J.orderEmbOfFin_mem hJc i)
    have : (e i : ℝ) ≤ 2 * K := by
      have := mem_range.mp hi
      exact_mod_cast Nat.lt_succ_iff.mp this
    nlinarith
  · have hi := J.orderEmbOfFin_mem hJc i
    have hj := J.orderEmbOfFin_mem hJc j
    have hne : e i ≠ e j := fun h => hij (e.injective h)
    set x : ℝ := (e i : ℝ) * g
    set y : ℝ := (e j : ℝ) * g
    have hfac : (A₀ + A₂ * x + A₄ * x ^ 2) - (A₀ + A₂ * y + A₄ * y ^ 2) =
        (x - y) * (A₄ * (x + y - 2 * m)) := by rw [hA₂]; ring
    have hxy : g ≤ |x - y| := by
      rcases lt_or_gt_of_ne hne with h | h
      · have : (e i : ℝ) + 1 ≤ e j := by exact_mod_cast h
        rw [abs_of_neg (by simp only [x, y]; nlinarith)]
        simp only [x, y]; nlinarith
      · have : (e j : ℝ) + 1 ≤ e i := by exact_mod_cast h
        rw [abs_of_pos (by simp only [x, y]; nlinarith)]
        simp only [x, y]; nlinarith
    have hsum : g ≤ |x + y - 2 * m| := by
      rcases hJside with h | h
      · have := h _ hi; have := h _ hj
        rw [abs_of_nonneg (by linarith)]; linarith
      · have := h _ hi; have := h _ hj
        rw [abs_of_nonpos (by linarith)]; linarith
    rw [hfac, abs_mul, abs_mul, abs_of_pos hA]
    calc A₄ * g ^ 2 = g * (A₄ * g) := by ring
      _ ≤ |x - y| * (A₄ * |x + y - 2 * m|) := by
        apply mul_le_mul hxy (mul_le_mul_of_nonneg_left hsum hA.le) (by positivity)
          (abs_nonneg _)

end CDRBicolour.Absorption.PaschTools
