/-
Copyright (c) 2026 Juan Pablo Traverso Gianini.
Released under Apache 2.0 license.
Authors: Juan Pablo Traverso Gianini
-/
module
public import CDRIIILib.KBicolor.PrescribedCounting.FixedCoreCounting
public import CDRIIILib.KBicolor.PrescribedCounting.ReservedCore

/-! # Uniform optimal entropy for each compatible prescribed interior matrix -/
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace CDRBicolour.KBicolor.PrescribedCounting
open Finset Classical TypedTriangle CDRBicolour.Absorption CDRBicolour.Absorption.Exact
open CDRBicolour.KBicolor.Wilson

theorem sharp_prescribed_at_group_order_of_three_le {k g : ℕ} (hk : 3 ≤ k) (hg : 15 ≤ g)
    (hga : _root_.STS.Admissible g) {δ η ζ ε : ℝ}
    (hδ : 0 < δ) (hη : 0 < η) (hε : 2/(g : ℝ) ≤ ε) (hζ : 2/(g : ℝ) ≤ ζ) :
    ∃ n₀ : ℕ, ∀ (n : ℕ) (lab : Fin n → Fin k), n₀ ≤ n →
      Odd n → (∀ X Y, X ≠ Y → Even (ksz lab X*ksz lab Y)) →
      3*∑ X,ksz lab X*(ksz lab X-1)=n*(n-1) →
      (∀ X,δ*n ≤ ksz lab X) → (∃ a,SeedData (ksz lab) η a) →
      ∀ target : Fin k → Fin k → ℕ,
      (∀ i j, i ≠ j → 2*(target i j+target j i)=ksz lab i*ksz lab j) →
      (∀ i, 2*∑ j ∈ univ.filter (fun j => j ≠ i), target i j=ksz lab i*(ksz lab i-1)) →
      (∀ i j, i ≠ j → ζ*(n : ℝ)^2 ≤ target i j) →
      let tv : TypeCoord k → ℕ := fun q => target q.1.1 q.1.2
      0 < exactTypeCount lab tv ∧ (1/6-ε)*(n : ℝ)^2*Real.log n ≤ Real.log (exactTypeCount lab tv) := by
  let o : Fin k := ⟨0,by omega⟩
  let ρ : ℝ := 1/(2*(g : ℝ))
  let θ : ℝ := 2/(g : ℝ)
  let ξ := seedAccuracy g o δ η
  let P := prescribedPatternBound k δ η ρ ξ
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
  have hP : 0 < P := prescribedPatternBound_pos k δ η ρ ξ
  have hPR : (0 : ℝ) < P := by exact_mod_cast hP
  have hC : 0 < C := by dsimp [C]; positivity
  obtain ⟨γ,hγ,nA,hA⟩ := exists_reserved_absorption_core_of_three_le hk hg hga hδ hη hρ hρhalf hρgroup
  let d := tradeDegreeBudget (Coord o) 17
  let nPlace := ⌈(9*(Fintype.card (Coord o) : ℝ)*17)/(ρ*δ/4)⌉₊
  let nPaid := ⌈(d : ℝ)/γ⌉₊
  let nLog := ⌈Real.exp ((Real.log C+2)/θ)⌉₊
  refine ⟨max nA (max 1 (max nPlace (max nPaid nLog))),
    fun n lab hn hodd heven hdiv hcls hseed target hpair hrow hlow => ?_⟩
  let tv : TypeCoord k → ℕ := fun q => target q.1.1 q.1.2
  have hnA : nA ≤ n := (le_max_left _ _).trans hn
  have hnrest := (le_max_right _ _).trans hn
  have hn1 : 1 ≤ n := (le_max_left _ _).trans hnrest
  have hnrest' := (le_max_right _ _).trans hnrest
  have hnPlace : nPlace ≤ n := (le_max_left _ _).trans hnrest'
  have hnPaid : nPaid ≤ n := (le_max_left _ _).trans ((le_max_right _ _).trans hnrest')
  have hnLog : nLog ≤ n := (le_max_right _ _).trans ((le_max_right _ _).trans hnrest')
  have hnR : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hlarge : Real.exp ((Real.log C+2)/θ) ≤ n :=
    (Nat.le_ceil _).trans (by exact_mod_cast hnLog)
  obtain ⟨m,t,hm,hB,hcone,hclose,hcover,htlin,h,S,hS,hreserve,hComp⟩ :=
    hA n lab hnA hodd heven hdiv hcls hseed
  have hcard : Fintype.card (Σ X,Fin (m X))=∑ X,m X := by simp only [Fintype.card_sigma,Fintype.card_fin]
  have htlin' : (n : ℝ)/C ≤ t := htlin
  have htR : (0 : ℝ) < t := lt_of_lt_of_le (div_pos hnR hC) htlin'
  have ht : 0 < t := by exact_mod_cast htR
  have hlog := log_order_control hθ hC hnR htlin' hlarge
  have hcover' : (1-θ)*(n : ℝ) ≤ (g : ℝ)*groupOrder (Σ X,Fin (m X)) t := by
    calc
      _ ≤ (1-ρ)*(n : ℝ) := mul_le_mul_of_nonneg_right (by linarith) hnR.le
      _ ≤ ((g*(∑ X,m X)*t : ℕ) : ℝ) := hcover
      _ = _ := by rw [groupOrder_eq,hcard]; push_cast; ring
  have hmin : ∀ X, 1 ≤ Hilton.csize (fun x : (Σ X,Fin (m X)) => x.1) X := by
    intro X
    rw [Pattern.csize_sigma]
    exact hm X
  have hApos : 0 < Fintype.card (Σ X,Fin (m X)) := by
    rw [hcard]
    have hh := hm o
    have hs : m o ≤ ∑ X,m X := single_le_sum (fun _ _ => Nat.zero_le _) (mem_univ _)
    omega
  have hGpos : 0 < groupOrder (Σ X,Fin (m X)) t := by rw [groupOrder_eq]; exact Nat.mul_pos hApos ht
  letI : Fact (Nat.Prime 17) := ⟨by decide⟩
  have hplace : ∀ X, 9*Fintype.card (Coord o)*17 ≤ #((reserve h).filter fun v => lab v=X) := by
    intro X
    have hh : (9*(Fintype.card (Coord o) : ℝ)*17)/(ρ*δ/4) ≤ n :=
      (Nat.le_ceil _).trans (Nat.cast_le.mpr hnPlace)
    have hh' := (div_le_iff₀ (by positivity : 0 < ρ*δ/4)).mp hh
    have he : ((9*Fintype.card (Coord o)*17 : ℕ) : ℝ) ≤ #((reserve h).filter fun v => lab v=X) := by
      push_cast
      nlinarith [hreserve X]
    exact_mod_cast he
  obtain ⟨trade,hτ,hPR⟩ := exists_place_in_reserve (m := 17) lab o (reserve h) hplace
  let Λold : LFam (Σ X,Fin (m X)) S t := Classical.choice (nonempty_latin_family _ S t)
  have hQ := reserve_trade_packing h hS Λold (by norm_num : 8 < 17) trade hPR (fun _ => false)
  have hLE : (packG trade (fun _ => false)).biUnion triEdges=leaveG trade := by
    have hh := packG_leave trade (fun _ => false)
    ext e
    simpa only [mem_biUnion] using Finset.ext_iff.mp hh e
  have hdeg : ∀ v, SparseEdge.degIn ((packG trade (fun _ => false)).biUnion triEdges) v ≤ d := by
    intro v
    rw [hLE]
    exact leave_degree_bounded trade v
  have hPaid : (d : ℝ) ≤ γ*n := by
    have hh : (d : ℝ)/γ ≤ n := (Nat.le_ceil _).trans (Nat.cast_le.mpr hnPaid)
    exact (div_le_iff₀ hγ).mp hh |>.trans_eq (mul_comm _ _)
  obtain ⟨E,hE⟩ := hComp Λold (packG trade (fun _ => false)) d hQ hdeg hPaid
  rw [hLE] at hE
  obtain ⟨hpos,hcount⟩ := fixed_core_prescribed_count h hS Λold o (by norm_num : 8 < 17)
    trade hτ hPR ⟨E,hE⟩ hn1 ht hGpos hmin hθ.le hθ1 hθg hζ hcover' target hpair hrow hlow
  refine ⟨hpos,?_⟩
  have hpairs : (g : ℝ)*(g-1) ≤ 6*(Fintype.card (VariableCross.Block S) : ℝ) := by
    have hh := group_pairs_le_OT hS
    have hhR : ((g*(g-1) : ℕ) : ℝ) ≤ ((6*#(CDRBicolour.Absorption.Count.Wilson.OT S) : ℕ) : ℝ) := by exact_mod_cast hh
    simpa only [VariableCross.Block,Fintype.card_coe,Nat.cast_mul,Nat.cast_sub (show 1 ≤ g by omega),
      Nat.cast_one,Nat.cast_ofNat] using hhR
  have hcover'' : (1-θ)*(n : ℝ) ≤ (g : ℝ)*Fintype.card (Σ X,Fin (m X))*t := by
    simpa only [groupOrder_eq,Nat.cast_mul,mul_assoc] using hcover'
  have hb := entropy_ineq hθ.le hθ1 hε (Nat.cast_nonneg (α := ℝ) g)
    (Nat.cast_nonneg (α := ℝ) (Fintype.card (Σ X,Fin (m X)))) hnR.le (Nat.cast_nonneg (α := ℝ) t)
    (Nat.cast_nonneg (α := ℝ) (Fintype.card (VariableCross.Block S))) (Real.log_nonneg (by exact_mod_cast hn1))
    hθg hpairs hcover'' hlog
  apply hb.trans
  convert hcount using 1
  rw [groupOrder_eq,Nat.cast_mul]
  ring

theorem sharp_prescribed_at_group_order {k g : ℕ} (hk : 4 ≤ k) (hg : 15 ≤ g)
    (hga : _root_.STS.Admissible g) {δ η ζ ε : ℝ}
    (hδ : 0 < δ) (hη : 0 < η) (hε : 2/(g : ℝ) ≤ ε) (hζ : 2/(g : ℝ) ≤ ζ) :
    ∃ n₀ : ℕ, ∀ (n : ℕ) (lab : Fin n → Fin k), n₀ ≤ n →
      Odd n → (∀ X Y, X ≠ Y → Even (ksz lab X*ksz lab Y)) →
      3*∑ X,ksz lab X*(ksz lab X-1)=n*(n-1) →
      (∀ X,δ*n ≤ ksz lab X) → (∃ a,SeedData (ksz lab) η a) →
      ∀ target : Fin k → Fin k → ℕ,
      (∀ i j, i ≠ j → 2*(target i j+target j i)=ksz lab i*ksz lab j) →
      (∀ i, 2*∑ j ∈ univ.filter (fun j => j ≠ i), target i j=ksz lab i*(ksz lab i-1)) →
      (∀ i j, i ≠ j → ζ*(n : ℝ)^2 ≤ target i j) →
      let tv : TypeCoord k → ℕ := fun q => target q.1.1 q.1.2
      0 < exactTypeCount lab tv ∧ (1/6-ε)*(n : ℝ)^2*Real.log n ≤ Real.log (exactTypeCount lab tv) :=
  sharp_prescribed_at_group_order_of_three_le (by omega) hg hga hδ hη hε hζ

end CDRBicolour.KBicolor.PrescribedCounting
