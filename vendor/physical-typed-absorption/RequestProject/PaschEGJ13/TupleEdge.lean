/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import RequestProject.PaschEGJ13.Theorem31
public import RequestProject.PaschEGJ13.TupleVertex
set_option maxHeartbeats 4000000 -- build option (original: -DmaxHeartbeats=1600000; raised)
set_option maxRecDepth 16384 -- build option (original: -DmaxRecDepth=8192; raised)

/-! # Step 2 of Theorem 1.3: tuple weights under a random edge colouring

The edges are coloured uniformly at random with `q` colours. For a function
`v : [ℓ] → [p] × [q]`, `zSum v` is the weight of the `ℓ`-sets `S` of edges such that every
`e ∈ S` lies in a part `A i` with `f(e) = j` for some `(i, j)` in the range of `v`. Using
Theorem 3.1 (applied to the colouring restricted to the edges of `H`), all `zSum v` are
small with high probability.
-/

@[expose] public section

namespace Pseudorandom

open Finset

/-! ## Marginals of product measures -/

section Marginal

variable {ι α : Type*} [Fintype ι] [DecidableEq ι] [Fintype α]

theorem pE_comp_subtype (P : ι → α → ℝ) (hP : IsPMF P) (s : ι → Prop) [DecidablePred s]
    [Fintype {i // s i}] (g : ({i // s i} → α) → ℝ) :
    pE P (fun ω => g (fun i => ω i.1)) = pE (fun i : {i // s i} => P i.1) g := by
  classical
  obtain rfl : ‹Fintype {i // s i}› = Subtype.fintype _ := Subsingleton.elim _ _
  set e := Equiv.piEquivPiSubtypeProd s (fun _ => α) with he
  unfold pE pw
  rw [← Fintype.sum_equiv e.symm (fun ab => (∏ i, P i (e.symm ab i)) * g (fun i => e.symm ab i.1))
    _ (fun _ => rfl)]
  rw [Fintype.sum_prod_type]
  refine Fintype.sum_congr _ _ fun a => ?_
  have h1 : ∀ b, (∏ i, P i (e.symm (a, b) i)) =
      (∏ i : {i // s i}, P i.1 (a i)) * ∏ i : {i // ¬ s i}, P i.1 (b i) := by
    intro b
    rw [← Fintype.prod_subtype_mul_prod_subtype s]
    congr 1
    · refine Fintype.prod_congr _ _ fun i => ?_
      simp [he, Equiv.piEquivPiSubtypeProd, i.2]
    · refine Fintype.prod_congr _ _ fun i => ?_
      simp [he, Equiv.piEquivPiSubtypeProd, i.2]
  have h2 : ∀ b, (fun i : {i // s i} => e.symm (a, b) i.1) = a := by
    intro b; funext i
    simp [he, Equiv.piEquivPiSubtypeProd, i.2]
  simp_rw [h1, h2]
  rw [← sum_mul, ← mul_sum]
  have h3 : ∑ b : {i // ¬ s i} → α, ∏ i : {i // ¬ s i}, P i.1 (b i) = 1 := by
    have := sum_pw (P := fun i : {i // ¬ s i} => P i.1) ⟨fun i a => hP.1 _ a, fun i => hP.2 _⟩
    simpa [pw] using this
  rw [h3, mul_one]

theorem pProb_comp_subtype (P : ι → α → ℝ) (hP : IsPMF P) (s : ι → Prop) [DecidablePred s]
    [Fintype {i // s i}] (B : ({i // s i} → α) → Prop) :
    pProb P (fun ω => B (fun i => ω i.1)) = pProb (fun i : {i // s i} => P i.1) B := by
  classical
  unfold pProb
  have := pE_comp_subtype P hP s (fun ω' => if B ω' then (1 : ℝ) else 0)
  convert this using 2

end Marginal

/-! ## Expectation of pattern weights -/

section PatternE

variable {ι : Type*} [Fintype ι] [LinearOrder ι] [DecidableEq ι]

theorem pE_patWeight {q : ℕ} (hq : 0 < q) (ℓ : ℕ) (ω : Finset ι → ℝ) (α : Fin ℓ → Fin q) :
    pE (unif ι q) (patWeight ℓ ω α) = (∑ e ∈ powersetCard ℓ univ, ω e) * (1 / (q : ℝ)) ^ ℓ := by
  classical
  unfold patWeight
  rw [pE_sum, sum_mul]
  refine sum_congr rfl fun e he => ?_
  rw [pE_const_mul]
  congr 1
  have hc : e.card = ℓ := (mem_powersetCard.mp he).2
  set x : ι → Fin q := fun v => (fun i : ℕ => if h : i < ℓ then α ⟨i, h⟩ else (⟨0, hq⟩ : Fin q))
    ((e.filter (· < v)).card) with hx
  have hcyl := pProb_cylinder (unif_isPMF (ι := ι) q hq) e x
  simp only [unif, prod_const, hc] at hcyl
  rw [← hcyl]
  unfold pProb
  congr 1
  funext f
  have := hasPattern_iff hq f α e hc
  by_cases h : HasPattern f α e
  · rw [if_pos h, if_pos (this.mp h)]
  · rw [if_neg h, if_neg (fun h' => h (this.mpr h'))]

end PatternE

/-! ## Transport of sums over `ℓ`-sets of edges to the subtype of edges -/

variable {V : Type*} [Fintype V] [DecidableEq V]

omit [Fintype V] in
theorem sum_powersetCard_subtype (H : Finset (Finset V)) (ℓ : ℕ) (F : Finset (Finset V) → ℝ) :
    ∑ S ∈ H.powersetCard ℓ, F S =
      ∑ T ∈ powersetCard ℓ (univ : Finset {e // e ∈ H}), F (T.map (Function.Embedding.subtype _)) := by
  have hU : (univ : Finset {e // e ∈ H}).map (Function.Embedding.subtype _) = H := by
    rw [univ_eq_attach, attach_map_val]
  conv_lhs => rw [← hU, powersetCard_map, sum_map]
  rfl

omit [Fintype V] in
theorem map_subtype_mem_powersetCard (H : Finset (Finset V)) (ℓ : ℕ) {T : Finset {e // e ∈ H}}
    (hT : T.card = ℓ) : T.map (Function.Embedding.subtype _) ∈ H.powersetCard ℓ := by
  rw [mem_powersetCard, card_map, hT]
  refine ⟨fun e he => ?_, rfl⟩
  obtain ⟨e', -, rfl⟩ := mem_map.mp he
  exact e'.2


/-! ## The norm bound for Theorem 3.1 -/

section Norm

variable (H : Finset (Finset V)) [LinearOrder {e // e ∈ H}]

omit [Fintype V] in
theorem tupleDeg_le_tdeg (ℓ : ℕ) (ω : Finset (Finset V) → ℝ)
    (hω0 : ∀ S ∈ H.powersetCard ℓ, 0 ≤ ω S) (ω' : Finset {e // e ∈ H} → ℝ)
    (hω' : ∀ T : Finset {e // e ∈ H}, T.card = ℓ → ω' T ≤ ω (T.map (Function.Embedding.subtype _)))
    (T : Finset {e // e ∈ H}) :
    tupleDeg ℓ ω' T ≤ tdeg ℓ ω H (T.map (Function.Embedding.subtype _)) := by
  classical
  unfold tupleDeg tdeg
  rw [sum_filter, sum_filter, sum_powersetCard_subtype H ℓ]
  refine sum_le_sum fun S hS => ?_
  have hc := (mem_powersetCard.mp hS).2
  simp only [map_subset_map]
  split_ifs
  · exact hω' S hc
  · exact le_rfl

omit [Fintype V] in
theorem thm31M_le (ℓ q : ℕ) (hℓ : 1 ≤ ℓ) (hq : 0 < q) (g Δ δ : ℝ) (hg : 0 ≤ g) (hΔ : 0 < Δ)
    (hqΔ : (q : ℝ) ≤ Δ) (hqg : q * g ≤ Δ) (ω : Finset (Finset V) → ℝ)
    (hω0 : ∀ S ∈ H.powersetCard ℓ, 0 ≤ ω S)
    (hnorm : ∀ j, 1 ≤ j → j ≤ ℓ → ∀ T ∈ H.powersetCard j,
      tdeg ℓ ω H T * Δ ^ ((j : ℝ) + δ) ≤ tweight ℓ ω H)
    (ω' : Finset {e // e ∈ H} → ℝ)
    (hω' : ∀ T : Finset {e // e ∈ H}, T.card = ℓ → ω' T ≤ ω (T.map (Function.Embedding.subtype _))) :
    thm31M q ℓ g ω' ≤ tweight ℓ ω H * Δ ^ (-δ) / (q : ℝ) ^ ℓ := by
  classical
  have htw0 : 0 ≤ tweight ℓ ω H := sum_nonneg fun S hS => hω0 S hS
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  unfold thm31M
  refine div_le_div_of_nonneg_right ?_ (by positivity)
  haveI : Nonempty (Fin ℓ) := ⟨⟨0, hℓ⟩⟩
  refine ciSup_le fun k => ?_
  have hj1 : 1 ≤ (k : ℕ) + 1 := by omega
  have hjl : (k : ℕ) + 1 ≤ ℓ := k.2
  have hpow : (0 : ℝ) < Δ ^ (((k : ℕ) + 1 : ℕ) : ℝ) * Δ ^ δ := by positivity
  have hN : tupleNorm ℓ ω' ((k : ℕ) + 1) ≤
      tweight ℓ ω H / (Δ ^ (((k : ℕ) + 1 : ℕ) : ℝ) * Δ ^ δ) := by
    unfold tupleNorm
    refine Real.iSup_le (fun T => ?_) (by positivity)
    refine (tupleDeg_le_tdeg H ℓ ω hω0 ω' hω' T.1).trans ?_
    have hmem : T.1.map (Function.Embedding.subtype _) ∈ H.powersetCard ((k : ℕ) + 1) :=
      map_subtype_mem_powersetCard H _ T.2
    have h := hnorm _ hj1 hjl _ hmem
    rw [Real.rpow_add hΔ] at h
    rw [le_div_iff₀ hpow]
    exact h
  have hX : (q : ℝ) ^ ((k : ℕ) + 1) * g ^ (k : ℕ) ≤ Δ ^ ((k : ℕ) + 1) := by
    calc (q : ℝ) ^ ((k : ℕ) + 1) * g ^ (k : ℕ) = q * (q * g) ^ (k : ℕ) := by ring
      _ ≤ Δ * Δ ^ (k : ℕ) := by
          apply mul_le_mul hqΔ (pow_le_pow_left₀ (by positivity) hqg _) (by positivity) hΔ.le
      _ = Δ ^ ((k : ℕ) + 1) := by ring
  have hX0 : 0 ≤ (q : ℝ) ^ ((k : ℕ) + 1) * g ^ (k : ℕ) := by positivity
  rw [Real.rpow_natCast] at hN
  calc tupleNorm ℓ ω' ((k : ℕ) + 1) * (q : ℝ) ^ ((k : ℕ) + 1) * g ^ (k : ℕ)
      = tupleNorm ℓ ω' ((k : ℕ) + 1) * ((q : ℝ) ^ ((k : ℕ) + 1) * g ^ (k : ℕ)) := by ring
    _ ≤ tweight ℓ ω H / (Δ ^ ((k : ℕ) + 1) * Δ ^ δ) *
        ((q : ℝ) ^ ((k : ℕ) + 1) * g ^ (k : ℕ)) := mul_le_mul_of_nonneg_right hN hX0
    _ ≤ tweight ℓ ω H / (Δ ^ ((k : ℕ) + 1) * Δ ^ δ) * Δ ^ ((k : ℕ) + 1) :=
        mul_le_mul_of_nonneg_left hX (by positivity)
    _ = tweight ℓ ω H * Δ ^ (-δ) := by
        rw [Real.rpow_neg hΔ.le]
        have : (0 : ℝ) < Δ ^ ((k : ℕ) + 1) := by positivity
        have : (0 : ℝ) < Δ ^ δ := by positivity
        field_simp

end Norm

/-! ## Covering `zSum` by pattern weights -/

section Cover

variable {p q : ℕ}

open Classical in
/-- The weight of the `ℓ`-sets of edges all of whose edges `e` lie in a part `A i` with colour
`f e = j` for some `(i, j)` in the range of `v`. -/
noncomputable def zSum {ℓ : ℕ} (H : Finset (Finset V)) (ω : Finset (Finset V) → ℝ)
    (A : Fin p → Finset (Finset V)) (v : Fin ℓ → Fin p × Fin q) (f : Finset V → Fin q) : ℝ :=
  ∑ S ∈ H.powersetCard ℓ, ω S * if ∀ e ∈ S, ∃ m, e ∈ A (v m).1 ∧ f e = (v m).2 then 1 else 0

variable (H : Finset (Finset V)) [LinearOrder {e // e ∈ H}]

open Classical in
/-- The tuple weight function used with Theorem 3.1 for the colour pattern `g`. -/
noncomputable def zW {ℓ : ℕ} (ω : Finset (Finset V) → ℝ) (A : Fin p → Finset (Finset V))
    (v : Fin ℓ → Fin p × Fin q) (g : Fin ℓ → Fin ℓ) (T : Finset {e // e ∈ H}) : ℝ :=
  if h : T.card = ℓ then ω (T.map (Function.Embedding.subtype _)) *
    (if ∀ j, (T.orderEmbOfFin h j).1 ∈ A (v (g j)).1 then 1 else 0) else 0

omit [Fintype V] in
theorem zW_nonneg {ℓ : ℕ} (ω : Finset (Finset V) → ℝ) (hω0 : ∀ S ∈ H.powersetCard ℓ, 0 ≤ ω S)
    (A : Fin p → Finset (Finset V)) (v : Fin ℓ → Fin p × Fin q) (g : Fin ℓ → Fin ℓ)
    (T : Finset {e // e ∈ H}) : 0 ≤ zW H ω A v g T := by
  unfold zW
  split_ifs with h h2
  · rw [mul_one]; exact hω0 _ (map_subtype_mem_powersetCard H ℓ h)
  · simp
  · simp

open Classical in
theorem zW_le {ℓ : ℕ} (ω : Finset (Finset V) → ℝ) (hω0 : ∀ S ∈ H.powersetCard ℓ, 0 ≤ ω S)
    (A : Fin p → Finset (Finset V)) (v : Fin ℓ → Fin p × Fin q) (g : Fin ℓ → Fin ℓ)
    (T : Finset {e // e ∈ H}) (hT : T.card = ℓ) :
    zW H ω A v g T ≤ ω (T.map (Function.Embedding.subtype _)) *
      if ∀ e ∈ T.map (Function.Embedding.subtype _), ∃ m, e ∈ A (v m).1 then 1 else 0 := by
  unfold zW
  rw [dif_pos hT]
  have h0 := hω0 _ (map_subtype_mem_powersetCard H ℓ hT)
  refine mul_le_mul_of_nonneg_left ?_ h0
  split_ifs with h1 h2 <;> try norm_num
  apply h2
  intro e he
  obtain ⟨e', he', rfl⟩ := mem_map.mp he
  have : e' ∈ Set.range (T.orderEmbOfFin hT) := by rw [range_orderEmbOfFin]; exact he'
  obtain ⟨j, rfl⟩ := this
  exact ⟨g j, h1 j⟩

theorem zSum_le_sum_patWeight {ℓ : ℕ} (ω : Finset (Finset V) → ℝ)
    (hω0 : ∀ S ∈ H.powersetCard ℓ, 0 ≤ ω S)
    (A : Fin p → Finset (Finset V)) (v : Fin ℓ → Fin p × Fin q) (f : Finset V → Fin q) :
    zSum H ω A v f ≤ ∑ g : Fin ℓ → Fin ℓ,
      patWeight ℓ (zW H ω A v g) (fun j => (v (g j)).2) (fun e : {e // e ∈ H} => f e.1) := by
  classical
  unfold zSum patWeight
  rw [sum_comm, sum_powersetCard_subtype H ℓ]
  refine sum_le_sum fun T hT => ?_
  have hc := (mem_powersetCard.mp hT).2
  have hnn : ∀ g : Fin ℓ → Fin ℓ, 0 ≤ zW H ω A v g T *
      (if HasPattern (fun e : {e // e ∈ H} => f e.1) (fun j => (v (g j)).2) T then 1 else 0) :=
    fun g => mul_nonneg (zW_nonneg H ω hω0 A v g T) (by split_ifs <;> norm_num)
  split_ifs with h
  · have hj : ∀ j : Fin ℓ, ∃ m, (T.orderEmbOfFin hc j).1 ∈ A (v m).1 ∧
        f (T.orderEmbOfFin hc j).1 = (v m).2 :=
      fun j => h _ (mem_map.mpr ⟨_, orderEmbOfFin_mem T hc j, rfl⟩)
    choose g hg using hj
    refine le_trans ?_ (single_le_sum (fun g _ => hnn g) (mem_univ g))
    unfold zW
    rw [dif_pos hc, if_pos (fun j => (hg j).1), if_pos ⟨hc, fun j => (hg j).2⟩]
    simp
  · rw [mul_zero]
    exact sum_nonneg fun g _ => hnn g

end Cover


/-! ## Positivity of `M` -/

section MPos

variable {ι : Type*} [Fintype ι] [LinearOrder ι]

theorem thm31M_pos_of_ne (q ℓ : ℕ) (hq : 0 < q) (hℓ : 1 ≤ ℓ) (g : ℝ) (ω : Finset ι → ℝ)
    (hω : ∀ T, 0 ≤ ω T) (T : Finset ι) (hT : T.card = ℓ) (hpos : 0 < ω T) :
    0 < thm31M q ℓ g ω := by
  classical
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  have hne : T.Nonempty := by rw [← card_pos, hT]; omega
  obtain ⟨t, ht⟩ := hne
  have h1 : ω T ≤ tupleDeg ℓ ω {t} := by
    unfold tupleDeg
    exact single_le_sum (f := ω) (fun e _ => hω e)
      (mem_filter.mpr ⟨mem_powersetCard.mpr ⟨subset_univ _, hT⟩, singleton_subset_iff.mpr ht⟩)
  have h2 : tupleDeg ℓ ω {t} ≤ tupleNorm ℓ ω 1 := by
    unfold tupleNorm
    exact le_ciSup (f := fun T : {T : Finset ι // T.card = 1} => tupleDeg ℓ ω T.1)
      (Set.finite_range _).bddAbove ⟨{t}, card_singleton t⟩
  have h3 : tupleNorm ℓ ω (((⟨0, hℓ⟩ : Fin ℓ) : ℕ) + 1) * (q : ℝ) ^ (((⟨0, hℓ⟩ : Fin ℓ) : ℕ) + 1) *
      g ^ ((⟨0, hℓ⟩ : Fin ℓ) : ℕ) ≤
      ⨆ k : Fin ℓ, tupleNorm ℓ ω (k + 1) * (q : ℝ) ^ ((k : ℕ) + 1) * g ^ (k : ℕ) :=
    le_ciSup (f := fun k : Fin ℓ => tupleNorm ℓ ω (k + 1) * (q : ℝ) ^ ((k : ℕ) + 1) * g ^ (k : ℕ))
      (Set.finite_range _).bddAbove ⟨0, hℓ⟩
  simp only [zero_add, pow_one, pow_zero, mul_one] at h3
  unfold thm31M
  have : 0 < tupleNorm ℓ ω 1 * q := by nlinarith
  exact div_pos (by linarith) (by positivity)

end MPos

/-! ## The bad event of Step 2 for one `v` -/

section Tail

variable {p q : ℕ} (H : Finset (Finset V)) [LinearOrder {e // e ∈ H}]

open Classical in
theorem zSum_tail (hq : 0 < q) {ℓ : ℕ} (hℓ : 1 ≤ ℓ) (ω : Finset (Finset V) → ℝ)
    (hω0 : ∀ S ∈ H.powersetCard ℓ, 0 ≤ ω S) (A : Fin p → Finset (Finset V))
    (v : Fin ℓ → Fin p × Fin q) (Ybd : ℝ)
    (hY : ∑ S ∈ H.powersetCard ℓ, ω S * (if ∀ e ∈ S, ∃ m, e ∈ A (v m).1 then 1 else 0) ≤ Ybd)
    (gg Mb : ℝ) (hMb : 0 < Mb) (hM : ∀ g, thm31M q ℓ gg (zW H ω A v g) ≤ Mb)
    (hgg : 24 * (ℓ : ℝ) ^ 3 * (ℓ + 1 + Real.log (Fintype.card {e // e ∈ H})) ≤ gg)
    (lam : ℝ) (hlam : 0 < lam) :
    pProb (unif (Finset V) q) (fun f => ¬ zSum H ω A v f ≤
        (ℓ : ℝ) ^ ℓ * (Ybd * (1 / (q : ℝ)) ^ ℓ + lam)) ≤
      (ℓ : ℝ) ^ ℓ * (2 ^ ℓ * Real.exp (-(lam ^ 2 / (12 * ℓ ^ 2 * Mb *
        (lam + Ybd * (1 / (q : ℝ)) ^ ℓ)))) + Real.exp (-(gg / (24 * ℓ ^ 2)))) := by
  classical
  have hPV := unif_isPMF (ι := Finset V) q hq
  have hPι := unif_isPMF (ι := {e // e ∈ H}) q hq
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  set X : (Fin ℓ → Fin ℓ) → ({e // e ∈ H} → Fin q) → ℝ :=
    fun g => patWeight ℓ (zW H ω A v g) (fun j => (v (g j)).2) with hX
  set E : (Fin ℓ → Fin ℓ) → ℝ := fun g => pE (unif {e // e ∈ H} q) (X g) with hE
  have hY0 : 0 ≤ Ybd := le_trans (sum_nonneg fun S hS => mul_nonneg (hω0 S hS)
    (by split_ifs <;> norm_num)) hY
  have hEle : ∀ g, E g ≤ Ybd * (1 / (q : ℝ)) ^ ℓ := by
    intro g
    simp only [hE, hX]
    rw [pE_patWeight hq]
    refine mul_le_mul_of_nonneg_right ?_ (by positivity)
    refine le_trans ?_ hY
    rw [sum_powersetCard_subtype H ℓ]
    exact sum_le_sum fun T hT => zW_le H ω hω0 A v g T (mem_powersetCard.mp hT).2
  have hE0 : ∀ g, 0 ≤ E g := fun g => pE_nonneg hPι fun f => sum_nonneg fun T _ =>
    mul_nonneg (zW_nonneg H ω hω0 A v g T) (by split_ifs <;> norm_num)
  -- the event is covered by the deviation events
  have hcov : ∀ f : Finset V → Fin q, ¬ zSum H ω A v f ≤ (ℓ : ℝ) ^ ℓ * (Ybd * (1 / (q : ℝ)) ^ ℓ + lam) →
      ∃ g ∈ (univ : Finset (Fin ℓ → Fin ℓ)), lam ≤ |X g (fun e : {e // e ∈ H} => f e.1) - E g| := by
    intro f hf
    by_contra hcon
    push_neg at hcon
    apply hf
    refine (zSum_le_sum_patWeight H ω hω0 A v f).trans ?_
    calc ∑ g : Fin ℓ → Fin ℓ, X g (fun e : {e // e ∈ H} => f e.1)
        ≤ ∑ _g : Fin ℓ → Fin ℓ, (Ybd * (1 / (q : ℝ)) ^ ℓ + lam) := by
          refine sum_le_sum fun g _ => ?_
          have h1 := hcon g (mem_univ g)
          have h2 := hEle g
          have := le_abs_self (X g (fun e : {e // e ∈ H} => f e.1) - E g)
          linarith
      _ = (ℓ : ℝ) ^ ℓ * (Ybd * (1 / (q : ℝ)) ^ ℓ + lam) := by
          rw [sum_const, card_univ, Fintype.card_fun, Fintype.card_fin, nsmul_eq_mul]
          push_cast; ring
  refine (pProb_mono hPV hcov).trans ((pProb_exists_le hPV _ _).trans ?_)
  have hbound : ∀ g : Fin ℓ → Fin ℓ, pProb (unif (Finset V) q)
      (fun f => lam ≤ |X g (fun e : {e // e ∈ H} => f e.1) - E g|) ≤
      2 ^ ℓ * Real.exp (-(lam ^ 2 / (12 * ℓ ^ 2 * Mb * (lam + Ybd * (1 / (q : ℝ)) ^ ℓ)))) +
        Real.exp (-(gg / (24 * ℓ ^ 2))) := by
    intro g
    rw [pProb_comp_subtype (unif (Finset V) q) hPV (· ∈ H)
      (fun f' => lam ≤ |X g f' - E g|)]
    have hunif : (fun i : {e // e ∈ H} => unif (Finset V) q i.1) = unif {e // e ∈ H} q := rfl
    rw [hunif]
    have hR0 : 0 ≤ 2 ^ ℓ * Real.exp (-(lam ^ 2 / (12 * ℓ ^ 2 * Mb *
        (lam + Ybd * (1 / (q : ℝ)) ^ ℓ)))) + Real.exp (-(gg / (24 * ℓ ^ 2))) := by positivity
    by_cases hz : ∀ T : Finset {e // e ∈ H}, T.card = ℓ → zW H ω A v g T = 0
    · have hX0 : ∀ f', X g f' = 0 := fun f' => sum_eq_zero fun T hT => by
        rw [hz T (mem_powersetCard.mp hT).2, zero_mul]
      have hE0' : E g = 0 := by
        show pE (unif {e // e ∈ H} q) (X g) = 0
        rw [show X g = fun _ => 0 from funext hX0]
        exact pE_const hPι 0
      have : pProb (unif {e // e ∈ H} q) (fun f' => lam ≤ |X g f' - E g|) = 0 := by
        unfold pProb pE
        refine sum_eq_zero fun f' _ => ?_
        dsimp only
        rw [if_neg (by rw [hX0, hE0', sub_zero, abs_zero]; linarith), mul_zero]
      rw [this]; exact hR0
    · push_neg at hz
      obtain ⟨T, hT, hTne⟩ := hz
      have hMpos := thm31M_pos_of_ne q ℓ hq hℓ gg (zW H ω A v g) (zW_nonneg H ω hω0 A v g) T hT
        (lt_of_le_of_ne (zW_nonneg H ω hω0 A v g T) (Ne.symm hTne))
      have h31 := theorem_3_1 q ℓ hq hℓ (fun j => (v (g j)).2) (zW H ω A v g)
        (fun T _ => zW_nonneg H ω hω0 A v g T) gg hgg lam hlam
      refine h31.trans ?_
      have hEg : pE (unif {e // e ∈ H} q) (patWeight ℓ (zW H ω A v g) fun j => (v (g j)).2) ≤
          Ybd * (1 / (q : ℝ)) ^ ℓ := hEle g
      have hEg0 : 0 ≤ pE (unif {e // e ∈ H} q) (patWeight ℓ (zW H ω A v g) fun j => (v (g j)).2) := hE0 g
      have hℓ0 : (0 : ℝ) < ℓ := by exact_mod_cast hℓ
      refine add_le_add ?_ le_rfl
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      apply Real.exp_le_exp.mpr
      apply neg_le_neg
      apply div_le_div_of_nonneg_left (by positivity) (by positivity)
      apply mul_le_mul (mul_le_mul_of_nonneg_left (hM g) (by positivity)) (by linarith)
        (by positivity) (by positivity)
  refine (sum_le_sum fun g _ => hbound g).trans (le_of_eq ?_)
  rw [sum_const, card_univ, Fintype.card_fun, Fintype.card_fin, nsmul_eq_mul]
  push_cast; ring

end Tail


/-! ## The bad event of Step 2 -/

open Classical in
/-- **Step 2 for tuple weights**: with high probability all `zSum v` are small. -/
theorem tuple_edge_bad {p q : ℕ} (hq : 0 < q) (H : Finset (Finset V)) [LinearOrder {e // e ∈ H}]
    (A : Fin p → Finset (Finset V)) (Δ δ gg : ℝ) (hΔ : 0 < Δ) (hgg0 : 0 ≤ gg)
    (hqΔ : (q : ℝ) ≤ Δ) (hqg : q * gg ≤ Δ)
    {κ : Type*} (K : Finset κ) (ℓ : κ → ℕ) (W : κ → Finset (Finset V) → ℝ)
    (hℓ1 : ∀ k ∈ K, 1 ≤ ℓ k)
    (hW0 : ∀ k ∈ K, ∀ S ∈ H.powersetCard (ℓ k), 0 ≤ W k S)
    (hpos : ∀ k ∈ K, 0 < tweight (ℓ k) (W k) H)
    (hnorm : ∀ k ∈ K, ∀ j, 1 ≤ j → j ≤ ℓ k → ∀ T ∈ H.powersetCard j,
      tdeg (ℓ k) (W k) H T * Δ ^ ((j : ℝ) + δ) ≤ tweight (ℓ k) (W k) H)
    (Ybd : κ → ℝ) (hYpos : ∀ k ∈ K, 0 < Ybd k)
    (hY : ∀ k ∈ K, ∀ u : Fin (ℓ k) → Fin p, ∑ S ∈ H.powersetCard (ℓ k),
      W k S * (if ∀ e ∈ S, ∃ m, e ∈ A (u m) then 1 else 0) ≤ Ybd k)
    (hgg : ∀ k ∈ K, 24 * (ℓ k : ℝ) ^ 3 * (ℓ k + 1 + Real.log (Fintype.card {e // e ∈ H})) ≤ gg) :
    pProb (unif (Finset V) q) (fun f => ∃ k ∈ K, ∃ v : Fin (ℓ k) → Fin p × Fin q,
        ¬ zSum H (W k) A v f ≤ 2 * (ℓ k : ℝ) ^ ℓ k * (Ybd k * (1 / (q : ℝ)) ^ ℓ k)) ≤
      ∑ k ∈ K, ((p : ℝ) * q) ^ ℓ k * ((ℓ k : ℝ) ^ ℓ k * (2 ^ ℓ k *
        Real.exp (-(Ybd k * (1 / (q : ℝ)) ^ ℓ k / (24 * (ℓ k : ℝ) ^ 2 *
          (tweight (ℓ k) (W k) H * Δ ^ (-δ) / (q : ℝ) ^ ℓ k)))) +
        Real.exp (-(gg / (24 * (ℓ k : ℝ) ^ 2))))) := by
  classical
  have hPV := unif_isPMF (ι := Finset V) q hq
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  refine (pProb_exists_le hPV _ _).trans (sum_le_sum fun k hk => ?_)
  have hall := (pProb_exists_le hPV (univ : Finset (Fin (ℓ k) → Fin p × Fin q)) (fun v f =>
      ¬ zSum H (W k) A v f ≤ 2 * (ℓ k : ℝ) ^ ℓ k * (Ybd k * (1 / (q : ℝ)) ^ ℓ k)))
  refine le_trans (pProb_mono hPV fun f ⟨v, hv⟩ => ⟨v, mem_univ _, hv⟩) (hall.trans ?_)
  have hℓ0 : (0 : ℝ) < ℓ k := by exact_mod_cast hℓ1 k hk
  set Mb := tweight (ℓ k) (W k) H * Δ ^ (-δ) / (q : ℝ) ^ ℓ k with hMb
  have hMb0 : 0 < Mb := by have := hpos k hk; positivity
  set lam := Ybd k * (1 / (q : ℝ)) ^ ℓ k with hlam
  have hlam0 : 0 < lam := by have := hYpos k hk; positivity
  have hv : ∀ v : Fin (ℓ k) → Fin p × Fin q, pProb (unif (Finset V) q) (fun f =>
      ¬ zSum H (W k) A v f ≤ 2 * (ℓ k : ℝ) ^ ℓ k * lam) ≤
      (ℓ k : ℝ) ^ ℓ k * (2 ^ ℓ k * Real.exp (-(lam / (24 * (ℓ k : ℝ) ^ 2 * Mb))) +
        Real.exp (-(gg / (24 * (ℓ k : ℝ) ^ 2)))) := by
    intro v
    have h := zSum_tail H hq (hℓ1 k hk) (W k) (hW0 k hk) A v (Ybd k)
      (hY k hk (fun m => (v m).1)) gg Mb hMb0
      (fun g => thm31M_le H (ℓ k) q (hℓ1 k hk) hq gg Δ δ hgg0 hΔ hqΔ hqg (W k) (hW0 k hk)
        (hnorm k hk) _ (fun T hT => (zW_le H (W k) (hW0 k hk) A v g T hT).trans (by
          have := hW0 k hk _ (map_subtype_mem_powersetCard H (ℓ k) hT)
          split_ifs <;> linarith)))
      (hgg k hk) lam hlam0
    have e1 : (ℓ k : ℝ) ^ ℓ k * (Ybd k * (1 / (q : ℝ)) ^ ℓ k + lam) =
        2 * (ℓ k : ℝ) ^ ℓ k * lam := by rw [hlam]; ring
    have e2 : lam ^ 2 / (12 * (ℓ k : ℝ) ^ 2 * Mb * (lam + Ybd k * (1 / (q : ℝ)) ^ ℓ k)) =
        lam / (24 * (ℓ k : ℝ) ^ 2 * Mb) := by
      rw [← hlam]; field_simp; ring
    rw [e1, e2] at h
    exact h
  refine (sum_le_sum fun v _ => hv v).trans (le_of_eq ?_)
  rw [sum_const, card_univ, Fintype.card_fun, Fintype.card_prod, Fintype.card_fin,
    Fintype.card_fin, Fintype.card_fin, nsmul_eq_mul]
  push_cast
  ring

end Pseudorandom
