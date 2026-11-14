/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license.
Authors: Juan Pablo Traverso Gianini
-/
module

public import CDRBicolour.KBicolor.Wilson.SharpAsymptotic
public import CDRBicolour.KBicolor.Wilson.ExplicitAbsorptionCore

/-!
# Sharp counting for robust k-colour profiles

The residual decomposition is constructed using T. The reserve fraction is
1/(2g); the larger entropy slack is 2/g. No DSP input occurs in this theorem.
-/

@[expose] public section

noncomputable section

set_option autoImplicit false

namespace CDRBicolour.KBicolor.Wilson

open Finset TypedTriangle
open scoped Classical

/-- Includes the tower absorption bound and the explicit entropy cut-off. -/
def groupCountThreshold {k : ℕ} (hk : 4 ≤ k) (g : ℕ) (δ η : ℝ) : ℕ :=
  let o : Fin k := ⟨0,by omega⟩
  let ρ : ℝ := 1/(2*(g : ℝ))
  let ξ := seedAccuracy g o δ η
  let P := wilsonPatternBound k δ η ρ ξ
  let C : ℝ := 4*(g : ℝ)*P
  max (coreTowerThreshold hk g δ η ρ)
    (max 1 ⌈Real.exp ((Real.log C+2)/(2/(g : ℝ)))⌉₊)

theorem sharp_lower_at_explicit_group_order {k g : ℕ} (hk : 4 ≤ k) (hg : 15 ≤ g)
    (hga : _root_.STS.Admissible g) {δ η ε : ℝ}
    (hδ : 0 < δ) (hη : 0 < η) (hε : 2/(g : ℝ) ≤ ε) :
    ∀ (n : ℕ) (lab : Fin n → Fin k), groupCountThreshold hk g δ η ≤ n →
      Odd n → (∀ X Y, X ≠ Y → Even (ksz lab X*ksz lab Y)) →
      3*∑ X,ksz lab X*(ksz lab X-1)=n*(n-1) →
      (∀ X,δ*n ≤ ksz lab X) → (∃ a,SeedData (ksz lab) η a) →
      (1/6-ε)*(n : ℝ)^2*Real.log n ≤ Real.log (kCount lab) := by
  let o : Fin k := ⟨0,by omega⟩
  let ρ : ℝ := 1/(2*(g : ℝ))
  let θ : ℝ := 2/(g : ℝ)
  let ξ := seedAccuracy g o δ η
  let P := wilsonPatternBound k δ η ρ ξ
  let C : ℝ := 4*(g : ℝ)*P
  have hgR : (0 : ℝ) < g := by exact_mod_cast (show 0 < g by omega)
  have hg1 : (1 : ℝ) ≤ g := by exact_mod_cast (show 1 ≤ g by omega)
  have hg2 : (2 : ℝ) ≤ g := by exact_mod_cast (show 2 ≤ g by omega)
  have hρ : 0 < ρ := by dsimp [ρ]; positivity
  have hρhalf : ρ ≤ 1/2 := by
    dsimp [ρ]
    apply (div_le_div_iff₀ (by positivity : 0 < 2*(g : ℝ)) (by norm_num : (0 : ℝ)<2)).mpr
    nlinarith
  have hρgroup : ρ ≤ 1/((g : ℝ)+1) := by
    dsimp [ρ]
    apply (div_le_div_iff₀ (by positivity : 0 < 2*(g : ℝ)) (by positivity : 0 < (g : ℝ)+1)).mpr
    nlinarith
  have hθ : 0 < θ := by dsimp [θ]; positivity
  have hθ1 : θ ≤ 1 := (div_le_one hgR).mpr hg2
  have hρθε : ρ ≤ θ := by
    dsimp [ρ,θ]
    apply (div_le_div_iff₀ (by positivity : 0 < 2*(g : ℝ)) hgR).mpr
    nlinarith
  have hθg : 1 ≤ θ*(g : ℝ) := by dsimp [θ]; field_simp; norm_num
  have hP : 0 < P := Nat.zero_lt_one.trans_le (le_max_right _ _)
  have hPR : (0 : ℝ) < P := by exact_mod_cast hP
  have hC : 0 < C := by dsimp [C]; positivity
  let nA := coreTowerThreshold hk g δ η ρ
  have hA := absorption_core_at_tower_order hk hg hga hδ hη hρ hρhalf hρgroup
  intro n lab hn hodd heven hdiv hcls hseed
  have hnA : nA ≤ n := (le_max_left _ _).trans hn
  have hnrest := (le_max_right _ _).trans hn
  have hn1 : 1 ≤ n := (le_max_left _ _).trans hnrest
  have hnceil : ⌈Real.exp ((Real.log C+2)/θ)⌉₊ ≤ n := (le_max_right _ _).trans hnrest
  have hnR : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hlarge : Real.exp ((Real.log C+2)/θ) ≤ n :=
    (Nat.le_ceil _).trans (by exact_mod_cast hnceil)
  obtain ⟨m,t,hm,hB,hcone,hclose,hcover,htlin,h,S,hS,hDall⟩ :=
    hA n lab hnA hodd heven hdiv hcls hseed
  have hcard : Fintype.card (Σ X,Fin (m X)) = ∑ X,m X := by
    simp only [Fintype.card_sigma,Fintype.card_fin]
  have htlin' : (n : ℝ)/C ≤ t := htlin
  have htR : (0 : ℝ) < t := lt_of_lt_of_le (div_pos hnR hC) htlin'
  have ht : 1 ≤ t := by exact_mod_cast htR
  have hlog := log_order_control hθ hC hnR htlin' hlarge
  have hcover' : (1-θ)*(n : ℝ) ≤ (g : ℝ)*Fintype.card (Σ X,Fin (m X))*t := by
    calc
      _ ≤ (1-ρ)*(n : ℝ) := mul_le_mul_of_nonneg_right (by linarith) hnR.le
      _ ≤ ((g*(∑ X,m X)*t : ℕ) : ℝ) := hcover
      _ = _ := by rw [hcard]; push_cast; rfl
  let Λ : LFam (Σ X,Fin (m X)) S t := Classical.choice (nonempty_latin_family _ S t)
  obtain ⟨D,hD⟩ := hDall Λ
  exact sharp_lower_of_residual h hS Λ hθ.le hθ1 hε (by omega) hθg ht hn1 hcover' hlog hD

/-- An explicit threshold for both sharp bounds on the same labelled profile. -/
def sharpCountThreshold {k : ℕ} (hk : 4 ≤ k) (δ η ε : ℝ) : ℕ :=
  max (groupCountThreshold hk (countGroupOrder (min ε (1/12))) δ η) 360004

theorem sharp_counting_at_explicit_order {k : ℕ} (hk : 4 ≤ k) {δ η ε : ℝ}
    (hδ : 0 < δ) (hη : 0 < η) (hε : 0 < ε) :
    ∀ (n : ℕ) (lab : Fin n → Fin k), sharpCountThreshold hk δ η ε ≤ n →
      Odd n → (∀ X Y, X ≠ Y → Even (ksz lab X*ksz lab Y)) →
      3*∑ X,ksz lab X*(ksz lab X-1)=n*(n-1) →
      (∀ X,δ*n ≤ ksz lab X) → (∃ a,SeedData (ksz lab) η a) →
      0 < kCount lab ∧
      (1/6-ε)*(n : ℝ)^2*Real.log n ≤ Real.log (kCount lab) ∧
      Real.log (kCount lab) ≤ (1/6+ε)*(n : ℝ)^2*Real.log n := by
  let ε' := min ε (1/12)
  have hε' : 0 < ε' := lt_min hε (by norm_num)
  have hε'ε : ε' ≤ ε := min_le_left _ _
  have hε'12 : ε' ≤ 1/12 := min_le_right _ _
  obtain ⟨hg,hga,hge⟩ := countGroupOrder_spec hε'
  have hL := sharp_lower_at_explicit_group_order hk hg hga hδ hη hge
  intro n lab hn hodd heven hdiv hcls hseed
  have hnL : groupCountThreshold hk (countGroupOrder ε') δ η ≤ n := (le_max_left _ _).trans hn
  have hnlarge : 360004 ≤ n := (le_max_right _ _).trans hn
  have hnR : (1 : ℝ) < n := by exact_mod_cast (show 1 < n by omega)
  have hnpos : (0 : ℝ) < n := by linarith
  have hlog : 0 < Real.log n := Real.log_pos hnR
  have hcoef : 0 < 1/6-ε' := by linarith
  have hlo := hL n lab hnL hodd heven hdiv hcls hseed
  have hlogpos : 0 < Real.log (kCount lab) :=
    lt_of_lt_of_le (mul_pos (mul_pos hcoef (sq_pos_of_pos hnpos)) hlog) hlo
  have hcount : 0 < kCount lab := by
    by_contra hc
    have hz : kCount lab=0 := Nat.eq_zero_of_not_pos hc
    simp only [hz,Nat.cast_zero,Real.log_zero] at hlogpos
    exact (lt_irrefl (0 : ℝ)) hlogpos
  refine ⟨hcount,?_,?_⟩
  · refine le_trans ?_ hlo
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (by linarith : 1/6-ε ≤ 1/6-ε') (sq_nonneg _)) hlog.le
  · exact log_upper_of hε (by exact_mod_cast hnlarge) (Nat.cast_nonneg _)
      (kCount_upper lab (by omega))

end CDRBicolour.KBicolor.Wilson
