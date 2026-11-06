/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import RequestProject.S07.Cheeger

@[expose] public section

/-!
# V24 / S07 §1: pointwise lower bound for `P^t(x,y)` and for walk counts

Smoothing BOTH endpoints: `P^(k+2) δ_y (x) = ⟨e_x, P^k (P δ_y)⟩`, where `e_x` is the
representer of `g ↦ (P g)(x)`. The exact `+1` direction (constants) and the exact `-1`
direction (`σ`) are separated; the rest contracts by `(1-κ²/2)^k`.

* `main_term_sq`: `(P^(k+2) δ_y (x) - 2 dg y / vol V)² ≤ λ^(2k) · (1/D²) · (M/D)` for `k` odd
  and `σ y = -σ x` (opposite sides), where `D ≤ deg ≤ M`.
* `Pop_pow_le_adj`: `P^m δ_y (x) ≤ (A^m)(x,y) / D^m`.
* `vol_expansion_of_count`: the vertex-count expansion `κ n |S| ≤ cut(S)` for `2|S| ≤ |V|`,
  with maximum degree `≤ n`, gives the volume form `κ vol S ≤ cut(S)` for `2 vol S ≤ vol V`.
-/

open Finset

namespace S07V24

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {H : SimpleGraph V} [DecidableRel H.Adj]

/-- Dirac function at `y` -/
noncomputable def dirac (y : V) : V → ℝ := fun v => if v = y then 1 else 0

lemma Pop_dirac (y v : V) : Pop H (dirac y) v = aw H v y / dg H v := by
  rw [Pop_apply]; congr 1; unfold dirac; simp [mul_ite]

omit [DecidableEq V] in
lemma sum_aw_col (y : V) : ∑ v, aw H v y = dg H y := by
  unfold dg; apply Finset.sum_congr rfl; intro v _; rw [aw_symm]

omit [DecidableEq V] in
lemma ip_one_sigma (σ : V → ℝ) (hσadj : ∀ v w, H.Adj v w → σ w = -σ v) :
    ip H (fun _ => 1) σ = 0 := by
  have h1 : ip H (fun _ => 1) σ = ∑ v, ∑ w, aw H v w * σ v := by
    rw [sum_aw_left]; unfold ip; apply Finset.sum_congr rfl; intro v _; ring
  have h2 : ∑ v, ∑ w, aw H v w * σ v = -∑ v, ∑ w, aw H v w * σ w := by
    rw [← Finset.sum_neg_distrib]; apply Finset.sum_congr rfl; intro v _
    rw [← Finset.sum_neg_distrib]; apply Finset.sum_congr rfl; intro w _
    unfold aw; split_ifs with h
    · rw [hσadj v w h]; ring
    · simp
  rw [sum_aw_right] at h2
  have h3 : ∑ v, ∑ w, aw H v w * σ v = ∑ v, dg H v * σ v := sum_aw_left _
  linarith

omit [DecidableEq V] in
lemma ip_one_one : ip H (fun _ => 1) (fun _ => 1) = vol H univ := by
  unfold ip vol; simp

omit [DecidableEq V] in
lemma ip_sigma_sigma (σ : V → ℝ) (hσ : ∀ v, σ v ^ 2 = 1) : ip H σ σ = vol H univ := by
  unfold ip vol; apply Finset.sum_congr rfl; intro v _
  rw [mul_assoc, ← sq, hσ, mul_one]

omit [DecidableEq V] in
lemma Pop_pow_one (hdg : ∀ v, 0 < dg H v) (k : ℕ) :
    (Pop H ^ k) (fun _ => (1 : ℝ)) = fun _ => 1 := by
  induction k with
  | zero => rfl
  | succ k ih => rw [pow_succ, Module.End.mul_apply, Pop_one hdg, ih]

omit [DecidableEq V] in
lemma Pop_pow_sigma (hdg : ∀ v, 0 < dg H v) (σ : V → ℝ)
    (hσadj : ∀ v w, H.Adj v w → σ w = -σ v) (k : ℕ) :
    (Pop H ^ k) σ = (-1 : ℝ) ^ k • σ := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ, Module.End.mul_apply, Pop_sigma hdg σ hσadj, show -σ = (-1 : ℝ) • σ by simp,
      map_smul, ih, smul_smul, pow_succ]; ring_nf

omit [DecidableEq V] in
/-- weighted Cauchy–Schwarz -/
lemma ip_cs (f g : V → ℝ) : ip H f g ^ 2 ≤ ip H f f * ip H g g := by
  have := Finset.sum_mul_sq_le_sq_mul_sq univ (fun v => Real.sqrt (dg H v) * f v)
    (fun v => Real.sqrt (dg H v) * g v)
  have hs : ∀ v, Real.sqrt (dg H v) ^ 2 = dg H v := fun v => Real.sq_sqrt (dg_nonneg v)
  unfold ip
  convert this using 2
  · apply Finset.sum_congr rfl; intro v _
    rw [show √(dg H v) * f v * (√(dg H v) * g v) = √(dg H v) ^ 2 * f v * g v by ring, hs]
  · apply Finset.sum_congr rfl; intro v _
    rw [show (√(dg H v) * f v) ^ 2 = √(dg H v) ^ 2 * f v * f v by ring, hs]
  · apply Finset.sum_congr rfl; intro v _
    rw [show (√(dg H v) * g v) ^ 2 = √(dg H v) ^ 2 * g v * g v by ring, hs]

/-- **Main pointwise estimate** (both endpoints smoothed, both exact directions removed). -/
theorem main_term_sq (hdg : ∀ v, 0 < dg H v) {κ : ℝ} (hκ : 0 ≤ κ) (hκ2 : κ ^ 2 < 2)
    (hexp : ∀ S : Finset V, 2 * vol H S ≤ vol H univ → κ * vol H S ≤ bdry H S)
    (σ : V → ℝ) (hσ : ∀ v, σ v ^ 2 = 1) (hσadj : ∀ v w, H.Adj v w → σ w = -σ v)
    {D M : ℝ} (hD : 0 < D) (hDle : ∀ v, D ≤ dg H v) (hM : ∀ v, dg H v ≤ M)
    (x y : V) (hxy : σ y = -σ x) (k : ℕ) (hk : Odd k) :
    ((Pop H ^ (k + 2)) (dirac y) x - 2 * dg H y / vol H univ) ^ 2 ≤
      ((1 - κ ^ 2 / 2) ^ 2) ^ k * (1 / D ^ 2) * (M / D) := by
  set U := vol H univ with hU
  have hUpos : 0 < U := by
    have : dg H y ≤ U := by
      unfold vol at hU; rw [hU]
      exact Finset.single_le_sum (fun v _ => dg_nonneg v) (mem_univ y)
    linarith [hdg y]
  set u := Pop H (dirac y) with hu
  set α := dg H y / U
  set β := -σ y * dg H y / U
  set one : V → ℝ := fun _ => 1
  set w := u - α • one - β • σ with hw
  have hu1 : ip H u one = dg H y := by
    unfold ip; rw [← sum_aw_col y]; apply Finset.sum_congr rfl; intro v _
    rw [hu, Pop_dirac]; simp only [one]; field_simp [(hdg v).ne']
  have huσ : ip H u σ = -σ y * dg H y := by
    have : ip H u σ = ∑ v, aw H v y * σ v := by
      unfold ip; apply Finset.sum_congr rfl; intro v _
      rw [hu, Pop_dirac]; field_simp [(hdg v).ne']
    rw [this, ← sum_aw_col y, Finset.mul_sum]; apply Finset.sum_congr rfl; intro v _
    unfold aw; split_ifs with h
    · rw [hσadj y v (H.adj_symm h)]; ring
    · simp
  have h1σ := ip_one_sigma (H := H) σ hσadj
  have hσ1 : ip H σ one = 0 := by rw [ip_comm]; exact h1σ
  have h11 : ip H one one = U := ip_one_one
  have hσσ := ip_sigma_sigma (H := H) σ hσ
  have hwW : InW (H := H) σ w := by
    constructor
    · rw [hw, ip_sub_left, ip_sub_left, ip_smul_left, ip_smul_left, hu1, h11, hσ1]
      simp only [α]; field_simp; ring
    · rw [hw, ip_sub_left, ip_sub_left, ip_smul_left, ip_smul_left, huσ, h1σ, hσσ]
      simp only [β]; field_simp; ring
  have hdecomp : u = w + α • one + β • σ := by rw [hw]; abel
  obtain ⟨hgW, hgnorm⟩ := iter_contraction hdg hκ hκ2 hexp σ hσ hσadj k w hwW
  set g := (Pop H ^ k) w
  have hPk : (Pop H ^ k) u = g + α • one - β • σ := by
    rw [hdecomp, map_add, map_add, map_smul, map_smul, Pop_pow_one hdg, Pop_pow_sigma hdg σ hσadj,
      hk.neg_one_pow]
    simp only [smul_smul]; ext v; simp [one]; ring
  have hval : (Pop H ^ (k + 2)) (dirac y) x = Pop H g x + (α + β * σ x) := by
    have e : (Pop H ^ (k + 2)) (dirac y) = Pop H ((Pop H ^ k) u) := by
      rw [hu, pow_succ', Module.End.mul_apply, pow_succ, Module.End.mul_apply]
    rw [e, hPk, map_sub, map_add, map_smul, map_smul, Pop_one hdg, Pop_sigma hdg σ hσadj]
    simp only [Pi.sub_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.neg_apply]; ring
  have hmain : α + β * σ x = 2 * dg H y / U := by
    have : α + β * σ x = dg H y / U * (1 + σ x ^ 2) := by simp only [α, β]; rw [hxy]; ring
    rw [this, hσ x]; ring
  rw [hval, hmain, add_sub_cancel_right]
  -- representer of evaluation after one smoothing step
  set e : V → ℝ := fun v => aw H x v / (dg H x * dg H v)
  have hrep : Pop H g x = ip H e g := by
    rw [Pop_apply]; unfold ip; rw [Finset.sum_div]; apply Finset.sum_congr rfl; intro v _
    simp only [e]; field_simp [(hdg v).ne', (hdg x).ne']
  have hee : ip H e e ≤ 1 / D ^ 2 := by
    have hx := hdg x
    have step : ip H e e ≤ ∑ v, aw H x v / (dg H x ^ 2 * D) := by
      unfold ip; apply Finset.sum_le_sum; intro v _
      simp only [e]
      have hv := hdg v
      have hav := aw_nonneg (H := H) x v
      have hsq := aw_sq (H := H) x v
      rw [show dg H v * (aw H x v / (dg H x * dg H v)) * (aw H x v / (dg H x * dg H v)) =
        aw H x v ^ 2 / (dg H x ^ 2 * dg H v) by field_simp, hsq]
      apply div_le_div_of_nonneg_left hav (by positivity)
      exact mul_le_mul_of_nonneg_left (hDle v) (by positivity)
    rw [← Finset.sum_div, ← dg] at step
    have : dg H x / (dg H x ^ 2 * D) ≤ 1 / D ^ 2 := by
      rw [div_le_div_iff₀ (by positivity) (by positivity)]
      have := hDle x
      nlinarith [mul_le_mul_of_nonneg_right this (le_of_lt hD), sq_nonneg D]
    linarith
  have huu : ip H u u ≤ M / D := by
    have step : ip H u u ≤ ∑ v, aw H v y / D := by
      unfold ip; apply Finset.sum_le_sum; intro v _
      rw [hu, Pop_dirac]
      have hv := hdg v
      have hav := aw_nonneg (H := H) v y
      rw [show dg H v * (aw H v y / dg H v) * (aw H v y / dg H v) = aw H v y ^ 2 / dg H v by
        field_simp, aw_sq]
      exact div_le_div_of_nonneg_left hav hD (hDle v)
    rw [← Finset.sum_div, sum_aw_col] at step
    have : dg H y / D ≤ M / D := div_le_div_of_nonneg_right (hM y) hD.le
    linarith
  have hww : ip H w w ≤ ip H u u := by
    have hw1 : ip H w one = 0 := hwW.1
    have hwσ : ip H w σ = 0 := hwW.2
    have : ip H u u = ip H w w + α ^ 2 * U + β ^ 2 * U := by
      rw [hdecomp]
      simp only [ip_add_left, ip_add_right, ip_smul_left, ip_smul_right]
      have h1σ' : ip H one σ = 0 := h1σ
      rw [ip_comm one w, ip_comm σ w, hw1, hwσ, h1σ', h11, hσσ, ← hU, hσ1]; ring
    rw [this]; nlinarith [sq_nonneg α, sq_nonneg β]
  rw [hrep]
  have hcs := ip_cs (H := H) e g
  have hpow : 0 ≤ ((1 - κ ^ 2 / 2) ^ 2) ^ k := by positivity
  have hee0 := ip_self_nonneg (H := H) e
  calc ip H e g ^ 2 ≤ ip H e e * ip H g g := hcs
    _ ≤ ip H e e * (((1 - κ ^ 2 / 2) ^ 2) ^ k * ip H u u) := by
        apply mul_le_mul_of_nonneg_left _ hee0
        exact hgnorm.trans (mul_le_mul_of_nonneg_left hww hpow)
    _ ≤ (1 / D ^ 2) * (((1 - κ ^ 2 / 2) ^ 2) ^ k * (M / D)) := by
        apply mul_le_mul hee (mul_le_mul_of_nonneg_left huu hpow) (by
          exact mul_nonneg hpow (ip_self_nonneg u)) (by positivity)
    _ = _ := by ring

/-- `P^m δ_y (x) ≤ (A^m)(x,y) / D^m` -/
theorem Pop_pow_le_adj (hdg : ∀ v, 0 < dg H v) {D : ℝ} (hD : 0 < D)
    (hDle : ∀ v, D ≤ dg H v) (y : V) :
    ∀ m : ℕ, ∀ x : V, 0 ≤ (Pop H ^ m) (dirac y) x ∧
      (Pop H ^ m) (dirac y) x ≤ (H.adjMatrix ℝ ^ m) x y / D ^ m := by
  intro m
  induction m with
  | zero =>
    intro x; simp only [pow_zero, Module.End.one_apply, div_one, Matrix.one_apply, dirac]
    constructor
    · split_ifs <;> norm_num
    · split_ifs <;> simp_all
  | succ m ih =>
    intro x
    rw [pow_succ', Module.End.mul_apply, Pop_apply]
    have hx := hdg x
    constructor
    · apply div_nonneg _ hx.le
      exact Finset.sum_nonneg fun w _ => mul_nonneg (aw_nonneg _ _) (ih w).1
    · rw [pow_succ', Matrix.mul_apply]
      have hsum : ∑ w, aw H x w * (Pop H ^ m) (dirac y) w ≤
          ∑ w, H.adjMatrix ℝ x w * (H.adjMatrix ℝ ^ m) w y / D ^ m := by
        apply Finset.sum_le_sum; intro w _
        have : H.adjMatrix ℝ x w = aw H x w := by
          simp [SimpleGraph.adjMatrix_apply, aw]
        rw [this, mul_div_assoc]
        exact mul_le_mul_of_nonneg_left (ih w).2 (aw_nonneg _ _)
      have hnn : 0 ≤ ∑ w, aw H x w * (Pop H ^ m) (dirac y) w :=
        Finset.sum_nonneg fun w _ => mul_nonneg (aw_nonneg _ _) (ih w).1
      rw [← Finset.sum_div] at hsum
      calc (∑ w, aw H x w * (Pop H ^ m) (dirac y) w) / dg H x
          ≤ (∑ w, aw H x w * (Pop H ^ m) (dirac y) w) / D :=
            div_le_div_of_nonneg_left hnn hD (hDle x)
        _ ≤ (∑ w, H.adjMatrix ℝ x w * (H.adjMatrix ℝ ^ m) w y) / D ^ m / D :=
            div_le_div_of_nonneg_right hsum hD.le
        _ = _ := by rw [pow_succ, div_div]

/-! ### Count form of the expansion -/

/-- number of edges with exactly one end in `S` -/
def cutCount (H : SimpleGraph V) [DecidableRel H.Adj] (S : Finset V) : ℕ :=
  ∑ v ∈ S, ((univ \ S).filter (H.Adj v)).card

lemma bdry_eq_cutCount (S : Finset V) : bdry H S = cutCount H S := by
  unfold bdry cutCount aw; push_cast
  apply Finset.sum_congr rfl; intro v _
  rw [Finset.sum_boole]

lemma bdry_compl (S : Finset V) : bdry H (univ \ S) = bdry H S := by
  unfold bdry
  rw [show univ \ (univ \ S) = S by simp]
  rw [Finset.sum_comm]; apply Finset.sum_congr rfl; intro v _; apply Finset.sum_congr rfl
  intro w _; rw [aw_symm]

/-- vertex-count expansion with ambient normalisation `n` gives the volume form -/
theorem vol_expansion_of_count {κ : ℝ} {n : ℝ} (hκ : 0 ≤ κ) (hM : ∀ v, dg H v ≤ n)
    (hexpc : ∀ S : Finset V, 2 * S.card ≤ Fintype.card V →
      κ * n * S.card ≤ cutCount H S) :
    ∀ S : Finset V, 2 * vol H S ≤ vol H univ → κ * vol H S ≤ bdry H S := by
  intro S hS
  have hvol : ∀ T : Finset V, vol H T ≤ n * T.card := by
    intro T; unfold vol
    calc ∑ v ∈ T, dg H v ≤ ∑ _v ∈ T, n := Finset.sum_le_sum fun v _ => hM v
      _ = n * T.card := by rw [Finset.sum_const, nsmul_eq_mul, mul_comm]
  by_cases hc : 2 * S.card ≤ Fintype.card V
  · rw [bdry_eq_cutCount]
    calc κ * vol H S ≤ κ * (n * S.card) := mul_le_mul_of_nonneg_left (hvol S) hκ
      _ = κ * n * S.card := by ring
      _ ≤ _ := hexpc S hc
  · push_neg at hc
    set T := univ \ S
    have hT : 2 * T.card ≤ Fintype.card V := by
      have := Finset.card_sdiff_of_subset (Finset.subset_univ S)
      simp only [T, Finset.card_univ] at this ⊢; omega
    rw [← bdry_compl, bdry_eq_cutCount]
    have hvT : vol H S ≤ vol H T := by simp only [T]; rw [vol_compl]; linarith
    calc κ * vol H S ≤ κ * vol H T := mul_le_mul_of_nonneg_left hvT hκ
      _ ≤ κ * (n * T.card) := mul_le_mul_of_nonneg_left (hvol T) hκ
      _ = κ * n * T.card := by ring
      _ ≤ _ := hexpc T hT

end S07V24
