/-
Copyright (c) 2026 Juan Pablo Traverso Gianini.
Released under Apache 2.0 license.
Authors: Juan Pablo Traverso Gianini
-/
module
public import CDRIIILib.KBicolor.Wilson.NearFullReserve

@[expose] public section
noncomputable section
set_option autoImplicit false

namespace CDRBicolour.KBicolor.Wilson
open Finset

/-- Every balanced three-colour profile approaches the equal three-part pattern. -/
theorem normalized_three_profile (c : Fin 3 → ℝ) {n ε : ℝ} (hn : 0 < n) (hε : 0 < ε)
    (hsum : ∑ X, c X = n) (hbalance : 3*∑ X, (c X)^2 = n^2+2*n)
    (hsize : 1/ε^2 ≤ n) (X : Fin 3) :
    |1/3-c X/n| ≤ ε := by
  have hv : ∑ Y, (3*c Y-n)^2 = 6*n := by
    simp only [Fin.sum_univ_three] at hsum hbalance ⊢
    nlinarith only [hbalance,congrArg (fun x => x*n) hsum]
  have hcoord := single_le_sum (fun Y (_ : Y ∈ (univ : Finset (Fin 3))) =>
    sq_nonneg (3*c Y-n)) (mem_univ X)
  rw [hv] at hcoord
  have hsize' := (div_le_iff₀ (sq_pos_of_pos hε)).mp hsize
  have hbound : (n/3-c X)^2 ≤ (ε*n)^2 := by
    have h := mul_le_mul_of_nonneg_right hsize' hn.le
    nlinarith only [hcoord,h]
  have h := abs_le_of_sq_le_sq hbound (mul_pos hε hn).le
  rw [show 1/3-c X/n = (n/3-c X)/n by field_simp,abs_div,abs_of_pos hn]
  exact (div_le_iff₀ hn).mpr h

/-- A three-cycle is the tournament for the three singleton classes. -/
theorem three_singleton_tournament :
    Pattern.IsTour (fun _ : Fin 3 => 1) (fun X Y => if Y=X+1 then 1 else 0) := by
  refine ⟨fun X => ?_,fun X Y hXY => ?_,fun X => ?_⟩
  · fin_cases X <;> decide
  · fin_cases X <;> fin_cases Y <;> first | exact (hXY rfl).elim | decide
  · fin_cases X <;> decide

/-- Use the equal three-part pattern to cover almost all vertices, with a reserve in each class. -/
theorem exists_near_full_setup_reserve_three {g : ℕ} (hg : 1 ≤ g) {δ ρ ξ : ℝ}
    (hδ : 0 < δ) (hρ : 0 < ρ) (hρhalf : ρ ≤ 1/2) (hξ : 0 < ξ) :
    ∃ n₀ : ℕ, ∀ (n : ℕ) (lab : Fin n → Fin 3), n₀ ≤ n →
      3*∑ X, (ksz lab X : ℝ)^2 = (n : ℝ)^2+2*n →
      (∀ X, δ*n ≤ ksz lab X) →
      ∃ (m : Fin 3 → ℕ) (t : ℕ), (∀ X, 1 ≤ m X) ∧ ∑ X,m X ≤ 3 ∧
        3*∑ X,m X^2 = (∑ X,m X)^2 ∧
        (∀ X, |(m X : ℝ)/(∑ Y,m Y : ℕ)-ksz lab X/n| ≤ ξ) ∧
        (1-ρ)*n ≤ ((g*(∑ X,m X)*t : ℕ) : ℝ) ∧ (n : ℝ)/(4*g*3) ≤ t ∧
        ∃ h : Setup lab (fun x : (Σ X,Fin (m X)) => x.1) g t,
          ∀ X, ρ*δ/4*n ≤ #((reserve h).filter fun v => lab v=X) := by
  let ε := min (ρ*δ/4) ξ
  have hε : 0 < ε := lt_min (by positivity) hξ
  refine ⟨max 1 (max ⌈1/ε^2⌉₊ ⌈6*(g : ℝ)/ρ⌉₊),fun n lab hn hbalance hcls => ?_⟩
  have hnR : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hgR : (0 : ℝ) < g := by exact_mod_cast (show 0 < g by omega)
  have hsum : ∑ X, ksz lab X = n := by
    unfold ksz
    rw [← card_eq_sum_card_fiberwise (f := lab) (fun _ _ => mem_univ _),card_univ,Fintype.card_fin]
  have hsumR : ∑ X, (ksz lab X : ℝ) = n := by exact_mod_cast hsum
  have hδthird : δ ≤ 1/3 := by
    have h := add_le_add (add_le_add (hcls 0) (hcls 1)) (hcls 2)
    rw [Fin.sum_univ_three] at hsumR
    by_contra hnδ
    have := mul_pos (show 0 < δ-1/3 by linarith) hnR
    nlinarith only [h,hsumR,this]
  have hsize : 1/ε^2 ≤ (n : ℝ) := (Nat.le_ceil _).trans (by
    exact_mod_cast (show ⌈1/ε^2⌉₊ ≤ n by omega))
  have hlarge : 6*(g : ℝ)/ρ ≤ n := (Nat.le_ceil _).trans (by
    exact_mod_cast (show ⌈6*(g : ℝ)/ρ⌉₊ ≤ n by omega))
  have hclose := normalized_three_profile (fun X => (ksz lab X : ℝ))
    hnR hε hsumR hbalance hsize
  let m : Fin 3 → ℕ := fun _ => 1
  have hmSum : ∑ X, m X = 3 := by simp [m]
  let t := ⌊(1-ρ/2)*n/(3*(g : ℝ))⌋₊
  have hfloorU : (t : ℝ) ≤ (1-ρ/2)*n/(3*(g : ℝ)) :=
    Nat.floor_le (div_nonneg (mul_nonneg (by linarith) hnR.le) (by positivity))
  have hfloorL : (1-ρ/2)*n/(3*(g : ℝ))-1 < (t : ℝ) := Nat.sub_one_lt_floor _
  have hcoverU := (le_div_iff₀ (show 0 < 3*(g : ℝ) by positivity)).mp hfloorU
  have hcoverL := (div_lt_iff₀ (show 0 < 3*(g : ℝ) by positivity)).mp
    (show (1-ρ/2)*n/(3*(g : ℝ)) < (t : ℝ)+1 by linarith)
  have hcover : (1-ρ)*n ≤ 3*(g : ℝ)*t := by
    nlinarith only [hcoverL,(div_le_iff₀ hρ).mp hlarge]
  have htlin : (n : ℝ)/(4*g*3) ≤ t := by
    apply (div_le_iff₀ (by positivity : 0 < 4*(g : ℝ)*3)).mpr
    nlinarith only [hcover,mul_le_mul_of_nonneg_right hρhalf hnR.le]
  have hroom (X : Fin 3) : ρ*δ/4*n+(g : ℝ)*t ≤ ksz lab X := by
    have hlo := (abs_le.mp ((hclose X).trans (min_le_left (ρ*δ/4) ξ))).2
    have hlo' := (le_div_iff₀ hnR).mp (show 1/3-ρ*δ/4 ≤ (ksz lab X : ℝ)/n by linarith)
    have hδρ := mul_le_mul_of_nonneg_left hδthird (mul_nonneg hρ.le hnR.le)
    nlinarith only [hlo',hcoverU,hδρ]
  obtain ⟨τ,hrow,hcol,hbic⟩ := Pattern.kbls_of_tournament
    (fun x : (Σ X,Fin (m X)) => x.1) (Pattern.csize_sigma m) three_singleton_tournament
  obtain ⟨h⟩ := exists_setup lab (fun x : (Σ X,Fin (m X)) => x.1) τ hrow hcol hbic (fun X => by
    rw [Pattern.csize_sigma]
    have hgt : (g : ℝ)*t ≤ ksz lab X := (le_add_of_nonneg_left (by positivity :
      0 ≤ ρ*δ/4*n)).trans (hroom X)
    simpa [m] using (show g*t ≤ ksz lab X by exact_mod_cast hgt))
  refine ⟨m,t,fun _ => le_rfl,hmSum.le,by simp [m],fun X => ?_,?_,htlin,h,fun X => ?_⟩
  · simpa [m,hmSum] using (hclose X).trans (min_le_right (ρ*δ/4) ξ)
  · rw [hmSum]
    push_cast
    nlinarith only [hcover]
  · have hcard := reserve_class_card h X
    rw [Pattern.csize_sigma] at hcard
    have hcardR : (#((reserve h).filter fun v => lab v=X) : ℝ)+(g : ℝ)*t = ksz lab X := by
      simpa [m] using (show (#((reserve h).filter fun v => lab v=X) : ℝ)+
        (g : ℝ)*m X*t = ksz lab X by exact_mod_cast hcard)
    linarith only [hroom X,hcardR]

end CDRBicolour.KBicolor.Wilson
