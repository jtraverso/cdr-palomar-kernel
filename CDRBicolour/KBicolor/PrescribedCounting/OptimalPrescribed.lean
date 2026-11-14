/-
Copyright (c) 2026 Juan Pablo Traverso Gianini.
Released under Apache 2.0 license.
Authors: Juan Pablo Traverso Gianini
-/
module
public import CDRBicolour.KBicolor.PrescribedCounting.SharpPrescribed
public import CDRBicolour.KBicolor.PrescribedCounting.TargetSeedData
public import CDRBicolour.KBicolor.Counting

/-! # Optimal counting for every prescribed interior type matrix

The target is fixed before the systems are chosen. The threshold is
uniform in the labelled partition and in that target. No residual
completion or extra fractional-seed assumption is left as an input.
-/
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace CDRBicolour.KBicolor
open Finset Classical TypedTriangle
open PrescribedCounting

theorem optimal_prescribed_type_count_of_three_le (k : ℕ) (hk : 3 ≤ k) {δ ζ ε : ℝ}
    (hδ : 0 < δ) (hζ : 0 < ζ) (hε : 0 < ε) :
    ∃ n₀ : ℕ, ∀ (n : ℕ) (lab : Fin n → Fin k), n₀ ≤ n → Odd n →
      (∀ i, δ*n ≤ ksz lab i) →
      (∀ i j, i ≠ j → Even (ksz lab i*ksz lab j)) →
      3*∑ i,ksz lab i*(ksz lab i-1)=n*(n-1) →
      ∀ target : Fin k → Fin k → ℕ,
      (∀ i j, i ≠ j → 2*(target i j+target j i)=ksz lab i*ksz lab j) →
      (∀ i, 2*∑ j ∈ univ.filter (fun j => j ≠ i), target i j=ksz lab i*(ksz lab i-1)) →
      (∀ i j, i ≠ j → ζ*(n : ℝ)^2 ≤ target i j) →
      let tv : TypeCoord k → ℕ := fun q => target q.1.1 q.1.2
      0 < exactTypeCount lab tv ∧
        (1/6-ε)*(n : ℝ)^2*Real.log n ≤ Real.log (exactTypeCount lab tv) ∧
        Real.log (exactTypeCount lab tv) ≤ (1/6+ε)*(n : ℝ)^2*Real.log n := by
  have hmin : 0 < min ε ζ := lt_min hε hζ
  obtain ⟨hg,hga,hgslack⟩ := Wilson.countGroupOrder_spec hmin
  obtain ⟨nC,hC⟩ := sharp_prescribed_at_group_order_of_three_le hk hg hga hδ hζ
    (hgslack.trans (min_le_left _ _)) (hgslack.trans (min_le_right _ _))
  refine ⟨max nC 360004,fun n lab hn hodd hcls heven hdiv target hpair hrow hlow => ?_⟩
  intro tv
  have hnC : nC ≤ n := (le_max_left _ _).trans hn
  have hnlarge : 360004 ≤ n := (le_max_right _ _).trans hn
  have hn0 : 0 < n := by omega
  have hseed := seedData_from_interior_target lab hδ hζ hn0 hcls target hpair hrow hlow
  obtain ⟨hpos,hbound⟩ := hC n lab hnC hodd heven hdiv hcls hseed target hpair hrow hlow
  refine ⟨hpos,hbound,?_⟩
  have hup : (exactTypeCount lab tv : ℝ) ≤ Real.exp ((n*(n-1)/6 : ℝ)*
      (Real.log n-2+1200/Real.sqrt ((n : ℝ)-3))) :=
    (Nat.cast_le.mpr (exactTypeCount_le lab tv)).trans (kCount_upper lab (by omega))
  exact log_upper_of hε (by exact_mod_cast hnlarge) (Nat.cast_nonneg _) hup

theorem optimal_prescribed_type_count_of_three_le_of_relative_margin (k : ℕ) (hk : 3 ≤ k) {δ η ε : ℝ}
    (hδ : 0 < δ) (hη : 0 < η) (hε : 0 < ε) :
    ∃ n₀ : ℕ, ∀ (n : ℕ) (lab : Fin n → Fin k), n₀ ≤ n → Odd n →
      (∀ i, δ*n ≤ ksz lab i) →
      (∀ i j, i ≠ j → Even (ksz lab i*ksz lab j)) →
      3*∑ i,ksz lab i*(ksz lab i-1)=n*(n-1) →
      ∀ target : Fin k → Fin k → ℕ,
      (∀ i j, i ≠ j → 2*(target i j+target j i)=ksz lab i*ksz lab j) →
      (∀ i, 2*∑ j ∈ univ.filter (fun j => j ≠ i), target i j=ksz lab i*(ksz lab i-1)) →
      (∀ i j, i ≠ j → η*ksz lab i*ksz lab j ≤ 2*(target i j : ℝ)) →
      let tv : TypeCoord k → ℕ := fun q => target q.1.1 q.1.2
      0 < exactTypeCount lab tv ∧
        (1/6-ε)*(n : ℝ)^2*Real.log n ≤ Real.log (exactTypeCount lab tv) ∧
        Real.log (exactTypeCount lab tv) ≤ (1/6+ε)*(n : ℝ)^2*Real.log n := by
  obtain ⟨n₀,h₀⟩ := optimal_prescribed_type_count_of_three_le k hk hδ (by positivity : 0 < η*δ^2/2) hε
  refine ⟨n₀,fun n lab hn hodd hcls heven hdiv target hpair hrow hrel => ?_⟩
  apply h₀ n lab hn hodd hcls heven hdiv target hpair hrow
  intro i j hij
  have hp : (δ*(n : ℝ))*(δ*n) ≤ (ksz lab i : ℝ)*ksz lab j :=
    mul_le_mul (hcls i) (hcls j) (by positivity) (Nat.cast_nonneg _)
  have hp' := mul_le_mul_of_nonneg_left hp hη.le
  nlinarith [hrel i j hij]

theorem optimal_prescribed_type_count (k : ℕ) (hk : 4 ≤ k) {δ ζ ε : ℝ}
    (hδ : 0 < δ) (hζ : 0 < ζ) (hε : 0 < ε) :
    ∃ n₀ : ℕ, ∀ (n : ℕ) (lab : Fin n → Fin k), n₀ ≤ n → Odd n →
      (∀ i, δ*n ≤ ksz lab i) →
      (∀ i j, i ≠ j → Even (ksz lab i*ksz lab j)) →
      3*∑ i,ksz lab i*(ksz lab i-1)=n*(n-1) →
      ∀ target : Fin k → Fin k → ℕ,
      (∀ i j, i ≠ j → 2*(target i j+target j i)=ksz lab i*ksz lab j) →
      (∀ i, 2*∑ j ∈ univ.filter (fun j => j ≠ i), target i j=ksz lab i*(ksz lab i-1)) →
      (∀ i j, i ≠ j → ζ*(n : ℝ)^2 ≤ target i j) →
      let tv : TypeCoord k → ℕ := fun q => target q.1.1 q.1.2
      0 < exactTypeCount lab tv ∧
        (1/6-ε)*(n : ℝ)^2*Real.log n ≤ Real.log (exactTypeCount lab tv) ∧
        Real.log (exactTypeCount lab tv) ≤ (1/6+ε)*(n : ℝ)^2*Real.log n :=
  optimal_prescribed_type_count_of_three_le k (by omega) hδ hζ hε

theorem optimal_prescribed_type_count_of_relative_margin (k : ℕ) (hk : 4 ≤ k) {δ η ε : ℝ}
    (hδ : 0 < δ) (hη : 0 < η) (hε : 0 < ε) :
    ∃ n₀ : ℕ, ∀ (n : ℕ) (lab : Fin n → Fin k), n₀ ≤ n → Odd n →
      (∀ i, δ*n ≤ ksz lab i) →
      (∀ i j, i ≠ j → Even (ksz lab i*ksz lab j)) →
      3*∑ i,ksz lab i*(ksz lab i-1)=n*(n-1) →
      ∀ target : Fin k → Fin k → ℕ,
      (∀ i j, i ≠ j → 2*(target i j+target j i)=ksz lab i*ksz lab j) →
      (∀ i, 2*∑ j ∈ univ.filter (fun j => j ≠ i), target i j=ksz lab i*(ksz lab i-1)) →
      (∀ i j, i ≠ j → η*ksz lab i*ksz lab j ≤ 2*(target i j : ℝ)) →
      let tv : TypeCoord k → ℕ := fun q => target q.1.1 q.1.2
      0 < exactTypeCount lab tv ∧
        (1/6-ε)*(n : ℝ)^2*Real.log n ≤ Real.log (exactTypeCount lab tv) ∧
        Real.log (exactTypeCount lab tv) ≤ (1/6+ε)*(n : ℝ)^2*Real.log n :=
  optimal_prescribed_type_count_of_three_le_of_relative_margin k (by omega) hδ hη hε

end CDRBicolour.KBicolor
