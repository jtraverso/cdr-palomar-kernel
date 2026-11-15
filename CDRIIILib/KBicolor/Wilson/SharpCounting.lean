/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license.
Authors: Juan Pablo Traverso Gianini
-/
module

public import CDRIIILib.KBicolor.Wilson.AbsorptionCore
public import CDRIIILib.KBicolor.Wilson.Quantitative

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

theorem nonempty_latin_family (A : Type*) [Fintype A] {g : ℕ}
    (S : Finset (Finset (Fin g))) (t : ℕ) : Nonempty (LFam A S t) := by
  have hL : 0 < Nat.card {l : Fin t → Fin t → Fin t // _root_.STS.IsLatin l} := by
    exact lt_of_lt_of_le Nat.zero_lt_one (_root_.STS.L_pos t)
  obtain ⟨l⟩ := (Nat.card_pos_iff.mp hL).1
  exact ⟨fun _ => l⟩

theorem sharp_lower_at_group_order {k g : ℕ} (hk : 4 ≤ k) (hg : 15 ≤ g)
    (hga : _root_.STS.Admissible g) {δ η ε : ℝ}
    (hδ : 0 < δ) (hη : 0 < η) (hε : 2/(g : ℝ) ≤ ε) :
    ∃ n₀ : ℕ, ∀ (n : ℕ) (lab : Fin n → Fin k), n₀ ≤ n →
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
  obtain ⟨nA,hA⟩ := exists_absorption_core hk hg hga hδ hη hρ hρhalf hρgroup
  refine ⟨max nA (max 1 ⌈Real.exp ((Real.log C+2)/θ)⌉₊),
    fun n lab hn hodd heven hdiv hcls hseed => ?_⟩
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

/-- A small admissible group order with entropy slack at most epsilon. -/
def countGroupOrder (ε : ℝ) : ℕ := 6*max 3 ⌈1/(3*ε)⌉₊+1

theorem countGroupOrder_spec {ε : ℝ} (hε : 0 < ε) :
    15 ≤ countGroupOrder ε ∧ _root_.STS.Admissible (countGroupOrder ε) ∧
      2/(countGroupOrder ε : ℝ) ≤ ε := by
  have hq3 : 3 ≤ max 3 ⌈1/(3*ε)⌉₊ := le_max_left _ _
  have hqceil : ⌈1/(3*ε)⌉₊ ≤ max 3 ⌈1/(3*ε)⌉₊ := le_max_right _ _
  have hq : 1/(3*ε) ≤ (max 3 ⌈1/(3*ε)⌉₊ : ℕ) :=
    (Nat.le_ceil _).trans (by exact_mod_cast hqceil)
  have hscaled := (div_le_iff₀ (by positivity : 0 < 3*ε)).mp hq
  have hg : 15 ≤ countGroupOrder ε := by unfold countGroupOrder; omega
  refine ⟨hg,Or.inl ?_,?_⟩
  · unfold countGroupOrder
    omega
  · have hgR : (0 : ℝ) < countGroupOrder ε := by exact_mod_cast (show 0 < countGroupOrder ε by omega)
    apply (div_le_iff₀ hgR).mpr
    unfold countGroupOrder
    push_cast at hscaled ⊢
    nlinarith [hscaled]

/-- Sharp lower bound for every robust profile, with no residual or arithmetic input. -/
theorem sharp_counting_lower {k : ℕ} (hk : 4 ≤ k) {δ η ε : ℝ}
    (hδ : 0 < δ) (hη : 0 < η) (hε : 0 < ε) :
    ∃ n₀ : ℕ, ∀ (n : ℕ) (lab : Fin n → Fin k), n₀ ≤ n →
      Odd n → (∀ X Y, X ≠ Y → Even (ksz lab X*ksz lab Y)) →
      3*∑ X,ksz lab X*(ksz lab X-1)=n*(n-1) →
      (∀ X,δ*n ≤ ksz lab X) → (∃ a,SeedData (ksz lab) η a) →
      (1/6-ε)*(n : ℝ)^2*Real.log n ≤ Real.log (kCount lab) := by
  obtain ⟨hg,hga,hge⟩ := countGroupOrder_spec hε
  exact sharp_lower_at_group_order hk hg hga hδ hη hge

end CDRBicolour.KBicolor.Wilson
