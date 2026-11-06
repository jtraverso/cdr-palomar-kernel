/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license.
Authors: Juan Pablo Traverso Gianini
-/
module

public import CDRBicolour.Absorption.PaschTools
public import CDRBicolour.Absorption.Host

/-!
# Signed perturbations of the CDR seed and their Pasch targets

Three disjoint parts of `2m` points each: `U = [0,2m)`, `V = [2m,4m)` inside class `A`, and
`W = [a, a+2m)` inside class `B`.  Each part has sign `+1` on its first half and `-1` on its
second half (`sgnv`).  The perturbation `δ T` is the product of the signs on the transversal
triangles `{u,v,w}` (one point in each part) and `0` otherwise.

* `swp k` swaps the two halves of part `k`: a label-preserving involution with
  `δ ∘ swp k = -δ` (`δ_swp`);
* hence `δ` sums to `0` over the triangles through any edge (`sum_δ_edge`), and
  `μ_t = μ₀ + t · δ / n` is again a diffuse seed (`pasch_seed_H1`, `C = 8` for `|t| ≤ 1/8`);
* `swp 1` maps `μ_t` to `μ_{-t}` and preserves the allowed Pasch configurations, so the Pasch
  target of `μ_t` is even in `t` (`target_even`);
* `∏_{T ∈ S} δ T ≥ 0` for every Pasch configuration, and the octahedral configurations on
  `U × V × W` give `∑_S ∏_{T∈S} δ T ≥ m⁶` (`family_bound`).
-/

@[expose] public section

namespace CDRBicolour.Absorption.PaschSeed

open Finset TypedTriangle CDRBicolour.Prefix CDRBicolour.Absorption CDRBicolour.Absorption.PaschTools

/-! ### Parts, signs and half-swaps on indices -/

/-- Part of an index: `1` on `[0,2m)`, `2` on `[2m,4m)`, `3` on `[a,a+2m)`, `0` otherwise. -/
def ptv (a m v : ℕ) : ℕ :=
  if v < 2 * m then 1 else if v < 4 * m then 2 else if a ≤ v ∧ v < a + 2 * m then 3 else 0

/-- Start of part `k`. -/
def lov (a m k : ℕ) : ℕ := if k = 1 then 0 else if k = 2 then 2 * m else a

/-- Sign: `+1` on the first half of each part, `-1` on the second half, `0` elsewhere. -/
noncomputable def sgnv (a m v : ℕ) : ℝ :=
  if ptv a m v = 0 then 0 else if v < lov a m (ptv a m v) + m then 1 else -1

/-- Half-swap of part `k` on indices. -/
def swpv (a m k v : ℕ) : ℕ :=
  if ptv a m v = k ∧ k ≠ 0 then (if v < lov a m k + m then v + m else v - m) else v

/-- Size constraints: the parts fit in their classes. -/
structure Hyp (a b m : ℕ) : Prop where
  pos : 1 ≤ m
  ha : 4 * m ≤ a
  hb : 2 * m ≤ b

variable {a b c m : ℕ}

theorem ptv_swpv (H : Hyp a b m) (k v : ℕ) : ptv a m (swpv a m k v) = ptv a m v := by
  have := H.ha
  unfold swpv ptv lov
  split_ifs <;> omega

theorem part_range (H : Hyp a b m) {k v : ℕ} (h : ptv a m v = k) (hk : k ≠ 0) :
    lov a m k ≤ v ∧ v < lov a m k + 2 * m := by
  have := H.ha
  subst h
  unfold ptv lov at *
  split_ifs at * <;> omega

theorem swpv_eq (H : Hyp a b m) {k v : ℕ} (h : ptv a m v = k) (hk : k ≠ 0) :
    swpv a m k v = if v < lov a m k + m then v + m else v - m := by
  unfold swpv; rw [if_pos ⟨h, hk⟩]

theorem swpv_swpv (H : Hyp a b m) (k v : ℕ) : swpv a m k (swpv a m k v) = v := by
  by_cases hk : ptv a m v = k ∧ k ≠ 0
  · have hp : ptv a m (swpv a m k v) = k := (ptv_swpv H k v).trans hk.1
    have hr := part_range H hk.1 hk.2
    rw [swpv_eq H hp hk.2, swpv_eq H hk.1 hk.2]
    split_ifs <;> omega
  · have : swpv a m k v = v := by unfold swpv; rw [if_neg hk]
    rw [this, this]

theorem swpv_lt (H : Hyp a b m) {v : ℕ} (k : ℕ) (hv : v < a + b + c) :
    swpv a m k v < a + b + c := by
  have := H.ha; have := H.hb
  unfold swpv ptv lov
  split_ifs <;> omega

theorem swpv_fix {k v : ℕ} (h : ptv a m v ≠ k) : swpv a m k v = v := by
  unfold swpv; rw [if_neg (fun h' => h h'.1)]

theorem swpv_lt_a (H : Hyp a b m) (k v : ℕ) : swpv a m k v < a ↔ v < a := by
  have := H.ha
  unfold swpv ptv lov
  split_ifs <;> omega

theorem swpv_lt_ab (H : Hyp a b m) (k v : ℕ) : swpv a m k v < a + b ↔ v < a + b := by
  have := H.ha; have := H.hb
  unfold swpv ptv lov
  split_ifs <;> omega

theorem sgnv_swpv (H : Hyp a b m) {k v : ℕ} (hk : k ≠ 0) (h : ptv a m v = k) :
    sgnv a m (swpv a m k v) = -sgnv a m v := by
  have hp := ptv_swpv H k v
  have := H.pos
  have hr := part_range H h hk
  unfold sgnv
  rw [hp, h, if_neg hk, swpv_eq H h hk]
  split_ifs <;> (try (exfalso; omega)) <;> norm_num

theorem sgnv_sq {v : ℕ} (h : ptv a m v ≠ 0) : sgnv a m v ^ 2 = 1 := by
  unfold sgnv; rw [if_neg h]; split_ifs <;> norm_num

theorem abs_sgnv_le (v : ℕ) : |sgnv a m v| ≤ 1 := by
  unfold sgnv; split_ifs <;> norm_num

/-! ### The half-swaps on points -/

section Points

variable (H : Hyp a b m)

/-- The half-swap of part `k` as a map of points. -/
def swp (k : ℕ) (i : Fin (a + b + c)) : Fin (a + b + c) := ⟨swpv a m k i.val, swpv_lt H k i.isLt⟩

theorem swp_swp (k : ℕ) (i : Fin (a + b + c)) : swp H k (swp H k i) = i :=
  Fin.ext (swpv_swpv H k i.val)

/-- The half-swap as an embedding. -/
def swpE (k : ℕ) : Fin (a + b + c) ↪ Fin (a + b + c) :=
  ⟨swp H k, fun i j h => by rw [← swp_swp H k i, h, swp_swp]⟩

theorem col3_swp (k : ℕ) (i : Fin (a + b + c)) : col3 a b c (swp H k i) = col3 a b c i := by
  have h1 := swpv_lt_a H k i.val
  have h2 := swpv_lt_ab H k i.val
  unfold col3 swp
  simp only
  split_ifs <;> simp_all

theorem map_col3_swp (k : ℕ) (T : Finset (Fin (a + b + c))) :
    (T.map (swpE H k)).val.map (col3 a b c) = T.val.map (col3 a b c) := by
  rw [map_val, Multiset.map_map]
  exact Multiset.map_congr rfl fun i _ => col3_swp H k i

theorem isAllowed_swp (k : ℕ) {T : Finset (Fin (a + b + c))}
    (hT : IsAllowed (cdrHost a b c) cdrF T) : IsAllowed (cdrHost a b c) cdrF (T.map (swpE H k)) := by
  obtain ⟨h3, -, hF⟩ := hT
  refine ⟨by rw [card_map, h3], fun x _ y _ hxy => hxy, ?_⟩
  show (T.map (swpE H k)).val.map (col3 a b c) ∈ cdrF
  rw [map_col3_swp]; exact hF

theorem mem_allowed_swp (k : ℕ) {T : Finset (Fin (a + b + c))}
    (hT : T ∈ allowed (cdrHost a b c) cdrF) : T.map (swpE H k) ∈ allowed (cdrHost a b c) cdrF := by
  classical
  unfold allowed at hT ⊢
  exact mem_filter.mpr ⟨mem_univ _, isAllowed_swp H k (mem_filter.mp hT).2⟩

theorem map_swp_swp (k : ℕ) (T : Finset (Fin (a + b + c))) :
    (T.map (swpE H k)).map (swpE H k) = T := by
  rw [map_map]
  convert map_refl (s := T)
  ext i
  exact congrArg Fin.val (swp_swp H k i)

end Points

/-! ### The perturbation `δ` -/

/-- Product of the signs on transversal triangles, `0` otherwise. -/
noncomputable def δ {n : ℕ} (a m : ℕ) (T : Finset (Fin n)) : ℝ :=
  if T.val.map (fun i => ptv a m i.val) = ({1, 2, 3} : Multiset ℕ) then ∏ p ∈ T, sgnv a m p.val
  else 0

theorem δ_cases {n : ℕ} (T : Finset (Fin n)) :
    δ a m T = 0 ∨ δ a m T = ∏ p ∈ T, sgnv a m p.val := by
  unfold δ; split_ifs <;> simp

theorem abs_δ_le {n : ℕ} (T : Finset (Fin n)) : |δ a m T| ≤ 1 := by
  rcases δ_cases (a := a) (m := m) T with h | h <;> rw [h]
  · simp
  · rw [abs_prod]
    exact prod_le_one₀ (fun _ _ => abs_nonneg _) fun p _ => abs_sgnv_le p.val

theorem count_pattern {k : ℕ} (hk : k = 1 ∨ k = 2 ∨ k = 3) :
    Multiset.count k ({1, 2, 3} : Multiset ℕ) = 1 := by
  rcases hk with rfl | rfl | rfl <;> decide

theorem δ_swp (H : Hyp a b m) {k : ℕ} (hk : k = 1 ∨ k = 2 ∨ k = 3)
    (T : Finset (Fin (a + b + c))) : δ a m (T.map (swpE H k)) = -δ a m T := by
  have hk0 : k ≠ 0 := by omega
  have hmap : (T.map (swpE H k)).val.map (fun i => ptv a m i.val) =
      T.val.map (fun i => ptv a m i.val) := by
    rw [map_val, Multiset.map_map]
    exact Multiset.map_congr rfl fun i _ => ptv_swpv H k i.val
  unfold δ
  rw [hmap]
  split_ifs with hpat
  · rw [prod_map]
    have hsw : ∀ p ∈ T, sgnv a m ((swpE H k) p).val =
        if ptv a m p.val = k then -sgnv a m p.val else sgnv a m p.val := by
      intro p _
      show sgnv a m (swpv a m k p.val) = _
      split_ifs with hp
      · exact sgnv_swpv H hk0 hp
      · rw [swpv_fix hp]
    rw [prod_congr rfl hsw, prod_ite, prod_neg]
    have hcard : #(T.filter fun p => ptv a m p.val = k) = 1 := by
      have := count_pattern hk
      rw [← hpat, Multiset.count_map] at this
      rw [← this, card_def, filter_val]
      congr 1
      exact Multiset.filter_congr fun p _ => eq_comm
    rw [hcard, pow_one, neg_one_mul, neg_mul, prod_filter_mul_prod_filter_not]
  · simp

/-! ### Sums over the triangles through an edge -/

/-- A sum over a set closed under an involution reversing the sign of the summand vanishes. -/
theorem sum_eq_zero_of_involution {α : Type*} (D : Finset α) (φ : α → α)
    (hφ : ∀ x ∈ D, φ x ∈ D) (hinv : ∀ x, φ (φ x) = x) (f : α → ℝ)
    (hf : ∀ x ∈ D, f (φ x) = -f x) : ∑ x ∈ D, f x = 0 := by
  have h : ∑ x ∈ D, f x = ∑ x ∈ D, f (φ x) :=
    sum_nbij' φ φ hφ hφ (fun x _ => hinv x) (fun x _ => hinv x) (fun x _ => by rw [hinv])
  rw [sum_congr rfl hf, sum_neg_distrib] at h
  linarith

theorem mem_triEdges_iff {n : ℕ} {T : Finset (Fin n)} {u v : Fin n} (huv : u ≠ v) :
    s(u, v) ∈ triEdges T ↔ u ∈ T ∧ v ∈ T := by
  simp [triEdges, mem_filter, mem_sym2_iff, Sym2.mem_iff, huv]

/-- `δ` sums to `0` over the allowed triangles through any edge. -/
theorem sum_δ_edge (H : Hyp a b m) {u v : Fin (a + b + c)} (huv : u ≠ v)
    (D : Finset (Finset (Fin (a + b + c))))
    (hD : ∀ T, T ∈ D ↔ T ∈ allowed (cdrHost a b c) cdrF ∧ s(u, v) ∈ triEdges T) :
    ∑ T ∈ D, δ a m T = 0 := by
  -- a part avoided by both endpoints
  obtain ⟨k, hk, hku, hkv⟩ : ∃ k : ℕ, (k = 1 ∨ k = 2 ∨ k = 3) ∧ ptv a m u.val ≠ k ∧
      ptv a m v.val ≠ k := by
    by_cases h1 : ptv a m u.val ≠ 1 ∧ ptv a m v.val ≠ 1
    · exact ⟨1, Or.inl rfl, h1⟩
    by_cases h2 : ptv a m u.val ≠ 2 ∧ ptv a m v.val ≠ 2
    · exact ⟨2, Or.inr (Or.inl rfl), h2⟩
    refine ⟨3, Or.inr (Or.inr rfl), ?_, ?_⟩ <;> omega
  have hfu : swpE H k u = u := Fin.ext (swpv_fix hku)
  have hfv : swpE H k v = v := Fin.ext (swpv_fix hkv)
  refine sum_eq_zero_of_involution D (fun T => T.map (swpE H k)) (fun T hT => ?_)
    (map_swp_swp H k) (δ a m) (fun T _ => δ_swp H hk T)
  obtain ⟨hTa, hTe⟩ := (hD T).mp hT
  refine (hD _).mpr ⟨mem_allowed_swp H k hTa, ?_⟩
  rw [mem_triEdges_iff huv] at hTe ⊢
  exact ⟨hfu ▸ mem_map_of_mem _ hTe.1, hfv ▸ mem_map_of_mem _ hTe.2⟩

/-! ### The perturbed seed -/

/-- The seed `μ_t = μ₀ + t · δ / n`. -/
noncomputable def μt (a b c m : ℕ) (t : ℝ) (T : Finset (Fin (a + b + c))) : ℝ :=
  wt a b c (T.val.map (col3 a b c)) + t * (δ a m T / (a + b + c : ℕ))

/-- **H1 for the perturbed seed**, `C = 8`, `|t| ≤ 1/8`. -/
theorem pasch_seed_H1 (H : Hyp a b m) (h : AdmissibleProfile a b c) (hn : 400 ≤ a + b + c)
    {t : ℝ} (ht : |t| ≤ 1 / 8) : IsDiffuseSeed (cdrHost a b c) cdrF 8 (μt a b c m t) := by
  classical
  obtain ⟨hbd, hsum⟩ := cdr_H1 h hn
  have hcard : (Fintype.card (Fin (a + b + c)) : ℝ) = ((a + b + c : ℕ) : ℝ) := by simp
  have hN : (400 : ℝ) ≤ ((a + b + c : ℕ) : ℝ) := by exact_mod_cast hn
  have hN0 : (0 : ℝ) < ((a + b + c : ℕ) : ℝ) := by linarith
  refine ⟨fun T hT => ?_, fun e he => ?_⟩
  · obtain ⟨hl, hu⟩ := hbd T hT
    rw [hcard] at hl hu ⊢
    simp only at hl hu
    have hδ := abs_δ_le (a := a) (m := m) T
    have hp : |t * (δ a m T / ((a + b + c : ℕ) : ℝ))| ≤ 1 / (8 * ((a + b + c : ℕ) : ℝ)) := by
      rw [abs_mul, abs_div, abs_of_pos hN0]
      calc |t| * (|δ a m T| / ((a + b + c : ℕ) : ℝ)) ≤ 1 / 8 * (1 / ((a + b + c : ℕ) : ℝ)) := by
            apply mul_le_mul ht (div_le_div_of_nonneg_right hδ hN0.le) (by positivity)
              (by norm_num)
        _ = 1 / (8 * ((a + b + c : ℕ) : ℝ)) := by field_simp
    rw [abs_le] at hp
    unfold μt
    have e1 : 1 / (8 * ((a + b + c : ℕ) : ℝ)) = 1 / (4 * ((a + b + c : ℕ) : ℝ)) -
        1 / (8 * ((a + b + c : ℕ) : ℝ)) := by field_simp; ring
    have e2 : 1 / (8 * ((a + b + c : ℕ) : ℝ)) ≤ 4 / ((a + b + c : ℕ) : ℝ) := by
      rw [div_le_div_iff₀ (by positivity) hN0]; nlinarith
    constructor
    · linarith
    · have : 4 / ((a + b + c : ℕ) : ℝ) + 4 / ((a + b + c : ℕ) : ℝ) = 8 / ((a + b + c : ℕ) : ℝ) := by
        ring
      linarith
  · induction e using Sym2.ind with
    | _ u v =>
    have huv : u ≠ v := he
    have h1 := hsum s(u, v) he
    simp only [μt]
    rw [sum_add_distrib, h1, ← mul_sum, ← sum_div]
    have key : ∀ D : Finset (Finset (Fin (a + b + c))),
        (∀ T, T ∈ D ↔ T ∈ allowed (cdrHost a b c) cdrF ∧ s(u, v) ∈ triEdges T) →
        1 + t * ((∑ i ∈ D, δ a m i) / ((a + b + c : ℕ) : ℝ)) = 1 := fun D hD => by
      rw [sum_δ_edge H huv D hD]; simp
    exact key _ (fun T => by simp only [mem_filter])

/-! ### Evenness of the Pasch target -/

theorem conf_swp (H : Hyp a b m) (k : ℕ) {S : Finset (Finset (Fin (a + b + c)))}
    (hS : S ∈ Pasch.configurations (allowed (cdrHost a b c) cdrF)) :
    S.map (mapEmbedding (swpE H k)).toEmbedding ∈
      Pasch.configurations (allowed (cdrHost a b c) cdrF) := by
  rw [Pasch.mem_configurations] at hS ⊢
  obtain ⟨hsub, h4, hP⟩ := hS
  refine ⟨fun T hT => ?_, by rw [card_map, h4], isPasch_map _ hP⟩
  obtain ⟨T0, hT0, rfl⟩ := mem_map.mp hT
  exact mem_allowed_swp H k (hsub hT0)

theorem map_conf_swp (H : Hyp a b m) (k : ℕ) (S : Finset (Finset (Fin (a + b + c)))) :
    (S.map (mapEmbedding (swpE H k)).toEmbedding).map (mapEmbedding (swpE H k)).toEmbedding = S := by
  rw [map_map]
  convert map_refl (s := S)
  ext T i
  simp only [Function.Embedding.trans_apply, RelEmbedding.coe_toEmbedding, mapEmbedding_apply,
    Function.Embedding.refl_apply]
  rw [map_swp_swp]

theorem wt_swp (H : Hyp a b m) (k : ℕ) (T : Finset (Fin (a + b + c))) :
    wt a b c ((T.map (swpE H k)).val.map (col3 a b c)) = wt a b c (T.val.map (col3 a b c)) := by
  rw [map_col3_swp]

/-- **The Pasch target of `μ_t` is even in `t`.** -/
theorem target_even (H : Hyp a b m) (t : ℝ) :
    ∑ S ∈ Pasch.configurations (allowed (cdrHost a b c) cdrF),
        ∏ T ∈ S, (wt a b c (T.val.map (col3 a b c)) + t * (δ a m T / (a + b + c : ℕ))) =
      ∑ S ∈ Pasch.configurations (allowed (cdrHost a b c) cdrF),
        ∏ T ∈ S, (wt a b c (T.val.map (col3 a b c)) + (-t) * (δ a m T / (a + b + c : ℕ))) := by
  set E := (mapEmbedding (swpE H 1)).toEmbedding
  refine sum_nbij' (fun S => S.map E) (fun S => S.map E) (fun S hS => conf_swp H 1 hS)
    (fun S hS => conf_swp H 1 hS) (fun S _ => map_conf_swp H 1 S)
    (fun S _ => map_conf_swp H 1 S) (fun S _ => ?_)
  rw [prod_map]
  refine prod_congr rfl fun T _ => ?_
  simp only [E, RelEmbedding.coe_toEmbedding, mapEmbedding_apply]
  rw [wt_swp, δ_swp H (Or.inl rfl)]
  ring

end CDRBicolour.Absorption.PaschSeed
