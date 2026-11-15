/-
Copyright (c) 2026 Juan Pablo Traverso Gianini.
Released under Apache 2.0 license.
Authors: Juan Pablo Traverso Gianini
-/
module
public import CDRIIILib.KBicolor.CompletionExact
public import CDRIIILib.KBicolor.ExactTypesPaschReplacement
public import CDRIIILib.KBicolor.DyadicLatinFamily
public import CDRIIILib.KBicolor.DyadicLatinSize
public import CDRIIILib.KBicolor.LatinMixedBudget

/-! # Prescribed exact interior types with arbitrarily many Pasch counts -/
@[expose] public section
noncomputable section
set_option autoImplicit false
namespace CDRBicolour.KBicolor
open Finset Classical TypedTriangle CDRBicolour.Absorption LatinPasch
open TypedTriangle.Applications.Latin

set_option maxHeartbeats 2000000 in
theorem kbicolour_types_exact_many_pasch_counts_of_absolute_margin (K k : ℕ) (hk : 3 ≤ k) {δ ε : ℝ}
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hε : 0 < ε) :
    ∃ n₀ : ℕ, ∀ (n : ℕ) (lab : Fin n → Fin k), n₀ ≤ n → Odd n →
      (∀ X, δ*n ≤ ksz lab X) →
      (∀ X Y, X ≠ Y → Even (ksz lab X * ksz lab Y)) →
      3 * ∑ X, ksz lab X * (ksz lab X-1) = n*(n-1) →
      ∀ t : Fin k → Fin k → ℕ,
      (∀ X Y, X ≠ Y → 2*(t X Y+t Y X) = ksz lab X * ksz lab Y) →
      (∀ X, 2*∑ Y ∈ univ.filter (fun Y => Y ≠ X), t X Y = ksz lab X * (ksz lab X-1)) →
      (∀ X Y, X ≠ Y → ε*(n:ℝ)^2 ≤ t X Y) →
      ∃ D : Fin K → Finset (Finset (Fin n)),
        (∀ i, IsDecomposition (kHost lab) (bicF k) (edges (kHost lab)) (D i)) ∧
        (∀ i X Y, X ≠ Y → kTypeCount lab (D i) X Y = t X Y) ∧
        Function.Injective (fun i => Pasch.count (D i)) := by
  obtain ⟨γ,hγ,N₀,hcomplete⟩ := kbicolour_completion_types_exact k hk hδ hδ1 hε
  let a : ℝ := min 1 (min (δ/4) (γ/18))
  have ha : 0 < a := lt_min (by norm_num) (lt_min (by positivity) (by positivity))
  have ha1 : a ≤ 1 := min_le_left _ _
  have haδ : a ≤ δ/4 := (min_le_right _ _).trans (min_le_left _ _)
  have haγ : a ≤ γ/18 := (min_le_right _ _).trans (min_le_right _ _)
  obtain ⟨N₁,hsize⟩ := exists_dyadic_size a ha (2*K+2)
  obtain ⟨N₂,hN₂⟩ := exists_nat_gt (4096*(2:ℝ)^K/a^5)
  refine ⟨max 1 (max N₀ (max N₁ (N₂+1))),fun n lab hn hodd hcls heven hdiv t hpair hrow hlow => ?_⟩
  have hn0 : 0<n := by omega
  have hnR : (0:ℝ)<n := by exact_mod_cast hn0
  have hncomp : N₀≤n := by omega
  have hnsize : N₁≤n := by omega
  obtain ⟨r,hr,hmlo,hmhi⟩ := hsize n hnsize
  let m := 2^r
  change (m:ℝ) ≤ a*n at hmhi
  change a*n/2 < (m:ℝ) at hmlo
  have hm : 2 ≤ m := by
    have hh : 2^1 ≤ 2^r := Nat.pow_le_pow_right (by norm_num) (by omega)
    exact hh
  have hlarge : 4096*(2:ℝ)^K < a^5*n := by
    have hh := (div_lt_iff₀ (show 0<a^5 by positivity)).mp hN₂
    have hnn : (N₂:ℝ)<n := by exact_mod_cast (show N₂<n by omega)
    have hmul := mul_lt_mul_of_pos_left hnn (show 0<a^5 by positivity)
    nlinarith only [hh,hmul]
  have hbudget : mixedBudget n m < (m:ℝ)^3/(4*(2:ℝ)^K) :=
    mixed_budget_small ha ha1 (by positivity) hn0 hm hmlo.le hlarge
  let X : Fin k := ⟨0,by omega⟩
  let Y : Fin k := ⟨1,by omega⟩
  have hXY : X≠Y := by intro he; have := congrArg Fin.val he; simp [X,Y] at this
  have hX : 2*m≤ksz lab X := by
    have hh := hcls X
    have hmul := mul_le_mul_of_nonneg_right haδ hnR.le
    exact_mod_cast (show (2:ℝ)*m≤ksz lab X by linarith)
  have hY : m≤ksz lab Y := by
    have hh := hcls Y
    have hmul := mul_le_mul_of_nonneg_right haδ hnR.le
    exact_mod_cast (show (m:ℝ)≤ksz lab Y by linarith)
  obtain ⟨rows,cols,syms,hplace⟩ := exists_latPlace lab hXY hX hY
  let L₀ := dyadicSquare r 0 (by omega)
  let L : Fin K → LatinSquare (Fin m) := fun i => dyadicSquare r i (by omega)
  have hl₀ : _root_.STS.IsLatin L₀ := ⟨L₀.row_bijective,L₀.column_bijective⟩
  have hdeg : ((9*m:ℕ):ℝ)≤γ*n := by
    have hmul := mul_le_mul_of_nonneg_right haγ hnR.le
    push_cast
    linarith
  obtain ⟨D₀,hD₀,hsub,ht₀⟩ := hcomplete n lab hncomp hodd hcls heven hdiv t hpair hrow hlow
    (latPackK rows cols syms L₀) (9*m) (latPackK_allowed hplace L₀)
    (latPackK_disj hplace hl₀) (latPackK_deg hplace hl₀) hdeg
  have hgap : ∀ i j : Fin K, i<j →
      ((intercalates (L j)).card:ℝ)+mixedBudget n m < (intercalates (L i)).card := by
    intro i j hij
    have hh := dyadicSquare_gap (show 2*K≤r by omega) i j hij
    have hbud : mixedBudget n m < ((2:ℝ)^r)^3/(4*(2:ℝ)^K) := by
      simpa only [m, Nat.cast_pow, Nat.cast_ofNat] using hbudget
    change ((2:ℝ)^r)^3/(4*(2:ℝ)^K) ≤
      (intercalates (L i)).card-((intercalates (L j)).card:ℝ) at hh
    linarith
  obtain ⟨D,hD,ht,hinj⟩ := exact_types_pasch_replacement hplace hm L₀ L D₀ hD₀ hsub hgap
  exact ⟨D,hD,fun i A B hAB => (ht i A B hAB).trans (ht₀ A B hAB),hinj⟩

/-- The same conclusion under the original relative interior-margin convention. -/
theorem kbicolour_types_exact_many_pasch_counts (K k : ℕ) (hk : 3 ≤ k) {δ η : ℝ}
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hη : 0 < η) :
    ∃ n₀ : ℕ, ∀ (n : ℕ) (lab : Fin n → Fin k), n₀ ≤ n → Odd n →
      (∀ X, δ*n ≤ ksz lab X) →
      (∀ X Y, X ≠ Y → Even (ksz lab X * ksz lab Y)) →
      3 * ∑ X, ksz lab X * (ksz lab X-1) = n*(n-1) →
      ∀ t : Fin k → Fin k → ℕ,
      (∀ X Y, X ≠ Y → 2*(t X Y+t Y X) = ksz lab X * ksz lab Y) →
      (∀ X, 2*∑ Y ∈ univ.filter (fun Y => Y ≠ X), t X Y = ksz lab X * (ksz lab X-1)) →
      (∀ X Y, X ≠ Y → η*ksz lab X*ksz lab Y ≤ 2*t X Y) →
      ∃ D : Fin K → Finset (Finset (Fin n)),
        (∀ i, IsDecomposition (kHost lab) (bicF k) (edges (kHost lab)) (D i)) ∧
        (∀ i X Y, X ≠ Y → kTypeCount lab (D i) X Y = t X Y) ∧
        Function.Injective (fun i => Pasch.count (D i)) := by
  obtain ⟨N,hN⟩ := kbicolour_types_exact_many_pasch_counts_of_absolute_margin K k hk hδ hδ1
    (show 0 < η*δ^2/2 by positivity)
  refine ⟨N,fun n lab hn hodd hcls heven hdiv t hpair hrow hlow =>
    hN n lab hn hodd hcls heven hdiv t hpair hrow (fun X Y hXY => ?_)⟩
  have hprod : (δ*(n:ℝ))*(δ*n) ≤ (ksz lab X:ℝ)*ksz lab Y :=
    mul_le_mul (hcls X) (hcls Y) (by positivity) (Nat.cast_nonneg _)
  have hh := mul_le_mul_of_nonneg_left hprod hη.le
  have hlo := hlow X Y hXY
  nlinarith

end CDRBicolour.KBicolor
