/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license.
Authors: Juan Pablo Traverso Gianini
-/
module

public import CDRBicolour.Absorption.Corners.Inverse3
public import CDRBicolour.Absorption.Count.Wilson.Core

/-!
# H1 for residual majority-type hosts (item 3, corners)

The uniform seed `μ₀(T) = 1/|X+1|` on the majority triangles `XX(X+1)` covers every `XX` edge
exactly once, and every `X(X+1)` edge `(|X| − 1)/|X+1|` times (`Minc_mu0`).  For an admissible
profile the classes differ by `O(√n)`, so the deficit is `O(n^{-1/2})`.  With the bounded inverse
`bri3` and `multi_residual_seed`, every residual host `K_n − L` that is **balanced**
(`π_u(𝟏_{E∖L}) = 0` for all `u`) and whose leave has degree `≤ n/10¹³` has a diffuse seed of
majority triangles with constant `8`, once `n ≥ 10²⁴` (`corner_residual_seed`).
-/

@[expose] public section

noncomputable section

namespace CDRBicolour.Absorption.Corners

open Finset TypedTriangle CDRBicolour.Prefix CDRBicolour.Absorption CDRBicolour.Absorption.Refined

/-! ### Label facts -/

theorem majF_XX (X k : Fin 3) : ({X, X, k} : Multiset (Fin 3)) ∈ majF ↔ k = X + 1 := by
  show (∃ Y : Fin 3, _ = _) ↔ _
  revert X k; decide

theorem majF_X1 (X k : Fin 3) : ({X, X + 1, k} : Multiset (Fin 3)) ∈ majF ↔ k = X := by
  show (∃ Y : Fin 3, _ = _) ↔ _
  revert X k; decide

theorem maj_eq_iff (X Y : Fin 3) :
    ({X, X, X + 1} : Multiset (Fin 3)) = {Y, Y, Y + 1} ↔ Y = X := by
  revert X Y; decide

theorem multiset_X1X (X : Fin 3) : ({X, X + 1, X} : Multiset (Fin 3)) = {X, X, X + 1} := by
  revert X; decide

variable {V : Type*} [Fintype V] [DecidableEq V] (lab : V → Fin 3)

/-- The weight of a type: `1/|X+1|` on `XX(X+1)`. -/
def g3 (m : Multiset (Fin 3)) : ℝ :=
  ∑ X : Fin 3, if m = {X, X, X + 1} then 1 / (csz lab (X + 1) : ℝ) else 0

/-- The uniform majority seed. -/
def mu0 (T : Finset V) : ℝ := g3 lab (T.val.map lab)

theorem g3_maj (X : Fin 3) : g3 lab {X, X, X + 1} = 1 / (csz lab (X + 1) : ℝ) := by
  unfold g3
  simp only [maj_eq_iff]
  rw [Finset.sum_ite_eq']; simp

/-- Third vertices of a given label, avoiding two given vertices. -/
theorem card_third {u v : V} (k : Fin 3) (hu : lab u ≠ k) (hv : lab v ≠ k) :
    #(univ.filter fun z => z ≠ u ∧ z ≠ v ∧ lab z = k) = csz lab k := by
  unfold csz
  congr 1; ext z
  simp only [mem_filter, mem_univ, true_and]
  constructor
  · exact fun h => h.2.2
  · intro h
    exact ⟨fun e => hu (e ▸ h), fun e => hv (e ▸ h), h⟩

theorem card_third' {u v : V} (k : Fin 3) (hu : lab u = k) (hv : lab v ≠ k) :
    #(univ.filter fun z => z ≠ u ∧ z ≠ v ∧ lab z = k) = csz lab k - 1 := by
  have : (univ.filter fun z => z ≠ u ∧ z ≠ v ∧ lab z = k) =
      (univ.filter fun z => lab z = k).erase u := by
    ext z
    simp only [mem_filter, mem_univ, true_and, mem_erase]
    constructor
    · exact fun h => ⟨h.1, h.2.2⟩
    · intro h; exact ⟨h.1, fun e => hv (e ▸ h.2), h.2⟩
  rw [this, card_erase_of_mem (by simp [hu])]
  rfl

open Classical in
theorem Minc_mu0_sum {u v : V} (huv : u ≠ v) (e : E0 V) (he : e.1 = s(u, v)) :
    MincG lab majF (mu0 lab) e = ∑ k, if ({lab u, lab v, k} : Multiset (Fin 3)) ∈ majF then
      (#(univ.filter fun z => z ≠ u ∧ z ≠ v ∧ lab z = k) : ℝ) * g3 lab {lab u, lab v, k}
      else 0 := by
  have h0 : MincG lab majF (mu0 lab) e = ∑ z ∈ univ.filter (fun z => z ≠ u ∧ z ≠ v ∧
      ({lab u, lab v, lab z} : Multiset (Fin 3)) ∈ majF), g3 lab {lab u, lab v, lab z} := by
    simp only [MincG, LinearMap.coe_mk, AddHom.coe_mk, mu0]
    rw [he]
    exact edge_sum_top' lab majF (g3 lab) huv _ (fun T => by simp [triG, mem_filter])
  rw [h0, sum_by_label lab (fun k => ({lab u, lab v, k} : Multiset (Fin 3)) ∈ majF)
    (fun k => g3 lab {lab u, lab v, k})]

/-- An `XX` edge is covered exactly once. -/
theorem Minc_mu0_same (hpos : ∀ k, 0 < csz lab k) {u v : V} (huv : u ≠ v) (e : E0 V)
    (he : e.1 = s(u, v)) (h1 : lab v = lab u) : MincG lab majF (mu0 lab) e = 1 := by
  classical
  rw [Minc_mu0_sum lab huv e he]
  simp only [h1, majF_XX]
  rw [Finset.sum_ite_eq']
  simp only [mem_univ, if_true]
  have hX : lab u ≠ lab u + 1 := (fin3_ne_add1 _).symm
  rw [card_third lab _ hX (h1 ▸ hX), g3_maj]
  have := hpos (lab u + 1)
  field_simp

/-- An `X(X+1)` edge is covered `(|X| − 1)/|X+1|` times. -/
theorem Minc_mu0_succ (hpos : ∀ k, 0 < csz lab k) {u v : V} (huv : u ≠ v) (e : E0 V)
    (he : e.1 = s(u, v)) (h1 : lab v = lab u + 1) :
    MincG lab majF (mu0 lab) e = ((csz lab (lab u) : ℝ) - 1) / csz lab (lab u + 1) := by
  classical
  rw [Minc_mu0_sum lab huv e he]
  simp only [h1, majF_X1]
  rw [Finset.sum_ite_eq']
  simp only [mem_univ, if_true]
  rw [card_third' lab _ rfl (by rw [h1]; exact fin3_ne_add1 _), multiset_X1X, g3_maj]
  have h := hpos (lab u)
  rw [Nat.cast_sub (by omega)]
  push_cast
  ring

/-- **The deficit of the uniform seed.** -/
theorem abs_Minc_mu0 (hpos : ∀ k, 0 < csz lab k) {η : ℝ}
    (hη : ∀ X, |(csz lab X : ℝ) - 1 - csz lab (X + 1)| ≤ η * csz lab (X + 1)) (e : E0 V) :
    |MincG lab majF (mu0 lab) e - 1| ≤ η := by
  obtain ⟨e, hed⟩ := e
  induction e using Sym2.ind with
  | _ u v =>
  have huv : u ≠ v := by simpa using hed
  have key : ∀ {p q : V}, p ≠ q → s(p, q) = s(u, v) → lab q = lab p + 1 →
      |MincG lab majF (mu0 lab) ⟨s(u, v), hed⟩ - 1| ≤ η := by
    intro p q hpq hpqe h1
    rw [Minc_mu0_succ lab hpos hpq ⟨s(u, v), hed⟩ hpqe.symm h1]
    have hs : (0 : ℝ) < csz lab (lab p + 1) := by exact_mod_cast hpos _
    rw [show ((csz lab (lab p) : ℝ) - 1) / csz lab (lab p + 1) - 1 =
      ((csz lab (lab p) : ℝ) - 1 - csz lab (lab p + 1)) / csz lab (lab p + 1) by field_simp]
    rw [abs_div, abs_of_pos hs, div_le_iff₀ hs]
    exact hη _
  have hη0 : 0 ≤ η := by
    have h := hη 0
    have hs : (0 : ℝ) < csz lab (0 + 1) := by exact_mod_cast hpos _
    by_contra hneg
    push Not at hneg
    have : η * csz lab (0 + 1) < 0 := mul_neg_of_neg_of_pos hneg hs
    linarith [abs_nonneg ((csz lab 0 : ℝ) - 1 - csz lab (0 + 1))]
  by_cases h1 : lab v = lab u
  · rw [Minc_mu0_same lab hpos huv _ rfl h1, sub_self, abs_zero]; exact hη0
  by_cases h2 : lab v = lab u + 1
  · exact key huv rfl h2
  · have h3 : lab u = lab v + 1 := by
      revert h1 h2; generalize lab u = x; generalize lab v = y; revert x y; decide
    exact key (Ne.symm huv) Sym2.eq_swap h3

/-! ### Constants -/

theorem C3_le {n m : ℕ} (hn : 400 ≤ n) (hm : n + 5 ≤ 4 * m) : C3 n m ≤ 26000 := by
  have hm3 : 3 ≤ m := by omega
  set M : ℝ := (m : ℝ) with hMdef
  have hN : (400 : ℝ) ≤ n := by exact_mod_cast hn
  have hM : (n : ℝ) + 5 ≤ 4 * M := by
    have : ((n + 5 : ℕ) : ℝ) ≤ ((4 * m : ℕ) : ℝ) := by exact_mod_cast hm
    push_cast at this; simpa [hMdef] using this
  have c1 : ((m - 1 : ℕ) : ℝ) = M - 1 := by rw [Nat.cast_sub (by omega)]; simp [hMdef]
  have c2 : ((m - 2 : ℕ) : ℝ) = M - 2 := by rw [Nat.cast_sub (by omega)]; simp [hMdef]
  have hM2 : 0 < M - 2 := by linarith
  have hy : (n : ℝ) * 397 ≤ 1600 * (M - 2) := by linarith
  have hcube : ((n : ℝ) * 397) ^ 3 ≤ (1600 * (M - 2)) ^ 3 :=
    pow_le_pow_left₀ (by positivity) hy 3
  have h68 : (n : ℝ) ^ 3 ≤ 68 * (M * (M - 1) * (M - 2)) := by
    have e1 : (M - 2) ^ 3 ≤ M * (M - 1) * (M - 2) := by
      have : (M - 2) * (M - 2) ≤ M * (M - 1) := by nlinarith
      nlinarith
    nlinarith
  unfold C3 kapM
  rw [c1, c2]
  have hpos : 0 < M * (M - 1) * (M - 2) := by
    have : 0 < M - 1 := by linarith
    positivity
  have t1 : 27 * (n : ℝ) / (2 * M) ≤ 54 := by
    rw [div_le_iff₀ (by positivity)]; linarith
  have t2 : 750 * (n : ℝ) ^ 3 * (1 / (2 * M * ((M - 1) * (M - 2)))) ≤ 25500 := by
    rw [show 750 * (n : ℝ) ^ 3 * (1 / (2 * M * ((M - 1) * (M - 2)))) =
      750 * (n : ℝ) ^ 3 / (2 * (M * (M - 1) * (M - 2))) by field_simp]
    rw [div_le_iff₀ (by positivity)]
    linarith
  linarith

/-- The squared difference of two classes of an admissible profile is at most `2n`. -/
theorem sq_diff_le {a b c : ℕ} (h : AdmissibleProfile a b c) (X : Fin 3) :
    ((csz (col3 a b c) X : ℝ) - csz (col3 a b c) (X + 1)) ^ 2 ≤ 2 * ((a + b + c : ℕ) : ℝ) := by
  have e := CDRBicolour.Absorption.Count.Wilson.adm_diff h
  have s1 := sq_nonneg ((a : ℝ) - b)
  have s2 := sq_nonneg ((a : ℝ) - c)
  have s3 := sq_nonneg ((b : ℝ) - c)
  push_cast
  fin_cases X <;> simp [csz_col3] <;> nlinarith

/-- **The deficit of the uniform seed for a large admissible profile.** -/
theorem corner_eta {a b c : ℕ} (h : AdmissibleProfile a b c) (hn : 10 ^ 24 ≤ a + b + c) (X : Fin 3) :
    |(csz (col3 a b c) X : ℝ) - 1 - csz (col3 a b c) (X + 1)| ≤
      (1 / 10 ^ 11) * csz (col3 a b c) (X + 1) := by
  have h400 : 400 ≤ a + b + c := le_trans (by norm_num) hn
  obtain ⟨ha4, hb4, hc4⟩ := class_lower_all h h400
  have hcls : a + b + c ≤ 4 * csz (col3 a b c) (X + 1) := by
    fin_cases X <;> simp [csz_col3] <;> omega
  set n : ℝ := ((a + b + c : ℕ) : ℝ) with hn_def
  have hN : (10 : ℝ) ^ 24 ≤ n := by rw [hn_def]; exact_mod_cast hn
  have hs : n ≤ 4 * (csz (col3 a b c) (X + 1) : ℝ) := by rw [hn_def]; exact_mod_cast hcls
  set D : ℝ := (csz (col3 a b c) X : ℝ) - csz (col3 a b c) (X + 1)
  have hD := sq_diff_le h X
  have hD1 : (D - 1) ^ 2 ≤ 5 * n := by nlinarith [sq_nonneg (D + 1)]
  set B : ℝ := (1 / 10 ^ 11) * n / 4
  have hB : 5 * n ≤ B ^ 2 := by
    simp only [B]
    have : (0 : ℝ) < n := by linarith
    nlinarith
  have hB0 : 0 ≤ B := by simp only [B]; positivity
  have h1 : |D - 1| ≤ B := by
    rw [abs_le]; constructor <;> nlinarith [sq_nonneg (D - 1 - B), sq_nonneg (D - 1 + B)]
  have h2 : B ≤ (1 / 10 ^ 11) * csz (col3 a b c) (X + 1) := by
    simp only [B]; nlinarith
  have : (csz (col3 a b c) X : ℝ) - 1 - csz (col3 a b c) (X + 1) = D - 1 := by simp only [D]; ring
  rw [this]; exact h1.trans h2

/-- **H1 for balanced residual majority-type hosts.** -/
theorem corner_residual_seed {a b c : ℕ} (h : AdmissibleProfile a b c) (hn : 10 ^ 24 ≤ a + b + c)
    (L : Finset (Sym2 (Fin (a + b + c))))
    (hres : ∀ v, ellG' (wpi (col3 a b c) v) (fun e : E0 (Fin (a + b + c)) =>
      if e.1 ∈ L then 0 else 1) = 0)
    {Δ : ℕ} (hdeg : ∀ p, degL L p ≤ Δ) (hΔ : 10 ^ 13 * Δ ≤ a + b + c) :
    ∃ μ, IsDiffuseSeed (gHost (col3 a b c) L) majF 8 μ := by
  have h400 : 400 ≤ a + b + c := le_trans (by norm_num) hn
  obtain ⟨ha4, hb4, hc4⟩ := class_lower_all h h400
  set m := (a + b + c + 8) / 4 with hm_def
  have hm : ∀ k, m ≤ csz (col3 a b c) k := by
    intro k; fin_cases k <;> simp [csz_col3] <;> omega
  have h512 : 512 ≤ m := by omega
  have hbal : Fintype.card (Fin (a + b + c)) ≤ 4 * m := by rw [Fintype.card_fin]; omega
  obtain ⟨B⟩ := bri_of_balanced hm h512 hbal
  let B' : BRIG (col3 a b c) cdrF (wl (col3 a b c)) 52000 :=
    ⟨B.Φ, fun d hd => B.exact d hd, fun d hd => B.bound d hd⟩
  have h3 : 3 ≤ m := by omega
  let B3 := bri3 (col3 a b c) B' hm h3
  have hC3 : C3 (Fintype.card (Fin (a + b + c))) m ≤ 26000 := by
    rw [Fintype.card_fin]; exact C3_le h400 (by omega)
  have hC3' : 0 ≤ C3 (Fintype.card (Fin (a + b + c))) m := by
    unfold C3 kapM; positivity
  have hpos : ∀ k, 0 < csz (col3 a b c) k := fun k => lt_of_lt_of_le (by omega) (hm k)
  set n : ℝ := ((a + b + c : ℕ) : ℝ) with hn_def
  have hcard : (Fintype.card (Fin (a + b + c)) : ℝ) = n := by simp [hn_def]
  have hN : (10 : ℝ) ^ 24 ≤ n := by rw [hn_def]; exact_mod_cast hn
  have hμ₀ : ∀ T ∈ triG (col3 a b c) majF,
      1 / (4 * Fintype.card (Fin (a + b + c))) ≤ mu0 (col3 a b c) T ∧
        mu0 (col3 a b c) T ≤ 4 / Fintype.card (Fin (a + b + c)) := by
    intro T hT
    obtain ⟨p, q, r, rfl, hpq, hq, hr⟩ := maj_shape (col3 a b c) hT
    have hpr : p ≠ r := fun e => fin3_ne_add1 _ (by rw [← hr, e])
    have hqr : q ≠ r := fun e => fin3_ne_add1 _ (by rw [← hr, ← hq, e])
    unfold mu0
    rw [val_map_triple _ hpq hpr.symm hqr.symm, hq, hr, g3_maj, hcard]
    set s := csz (col3 a b c) (col3 a b c p + 1)
    have hs1 : a + b + c ≤ 4 * s := by
      have := hm (col3 a b c p + 1); omega
    have hs2 : s ≤ a + b + c := by
      have : s ≤ Fintype.card (Fin (a + b + c)) := card_le_univ _
      simpa using this
    have r1 : n ≤ 4 * (s : ℝ) := by rw [hn_def]; exact_mod_cast hs1
    have r2 : (s : ℝ) ≤ n := by rw [hn_def]; exact_mod_cast hs2
    have r0 : (0 : ℝ) < s := by exact_mod_cast hpos _
    have n0 : (0 : ℝ) < n := by linarith
    constructor
    · rw [div_le_div_iff₀ (by positivity) r0]; linarith
    · rw [div_le_div_iff₀ r0 n0]; linarith
  have hdef := abs_Minc_mu0 (col3 a b c) hpos (corner_eta h hn)
  have hw : ∀ v, ∀ T ∈ triG (col3 a b c) majF, ∑ f ∈ triEdges T, wpi (col3 a b c) v f = 0 :=
    fun v T hT => maj_piT (col3 a b c) hT v
  have hK : 0 ≤ C3 (Fintype.card (Fin (a + b + c))) m * 52000 := by positivity
  have hΔR : (10 : ℝ) ^ 13 * Δ ≤ n := by rw [hn_def]; exact_mod_cast hΔ
  have hΔ0 : (0 : ℝ) ≤ Δ := by positivity
  obtain ⟨μ, hμ⟩ := multi_residual_seed L hw hK (by norm_num : (1 : ℝ) ≤ 4)
    (by norm_num : (0 : ℝ) ≤ 1 / 10 ^ 11) B3 hres hμ₀ hdef hdeg (by simp; omega) (by
      rw [hcard]
      have e1 : C3 (Fintype.card (Fin (a + b + c))) m * 52000 ≤ 26000 * 52000 := by linarith
      nlinarith)
  exact ⟨μ, by norm_num at hμ; exact hμ⟩

end CDRBicolour.Absorption.Corners
