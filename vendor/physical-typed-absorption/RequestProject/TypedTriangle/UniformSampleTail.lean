/-
Copyright (c) 2026 Juan Pablo Traverso Gianini.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module
public import RequestProject.S07.RandomCore
set_option maxHeartbeats 4000000 -- build option (original: -DmaxHeartbeats=1600000; raised)
set_option maxRecDepth 16384 -- build option (original: -DmaxRecDepth=8192; raised)
@[expose] public section
set_option pp.fullNames true
open Finset Classical
noncomputable section
namespace TypedTriangle.RawReference

open S07V24

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- A relative lower-tail estimate from an exact mean lower bound and an
influence-square budget. The parameter `η` can be chosen separately at each
scale; this lemma does not construct nested samples. -/
theorem relative_lower_tail (q η L D : ℝ) (c : V → ℝ) (f : Finset V → ℝ)
    (hq0 : 0 ≤ q) (hq1 : q ≤ 1) (hη : 0 < η)
    (hL : 0 < L) (hD : 0 < D)
    (hf : ∀ W ⊆ (univ : Finset V), ∀ a ∈ (univ : Finset V), a ∉ W →
      |f (insert a W) - f W| ≤ c a)
    (hinfluence : ∀ a, (η*L/(2*D))*c a ≤ 1)
    (hmean : L ≤ bexp q univ f)
    (hsq : ∑ a ∈ (univ : Finset V), c a ^ 2 ≤ D) :
    bprob q univ (fun W => f W < (1-η)*L) ≤
      Real.exp (-(η^2*L^2/(4*D))) := by
  let l : ℝ := η*L/(2*D)
  have hl : 0 ≤ l := by dsimp [l]; positivity
  have ht := tail_lower hq0 hq1 c hl univ f hf (fun a _ => hinfluence a) (η*L)
  have hmono : bprob q univ (fun W => f W < (1-η)*L) ≤
      bprob q univ (fun W => f W ≤ bexp q univ f - η*L) := by
    apply bprob_mono hq0 hq1
    intro W hW
    nlinarith [hmean]
  have hsq' : l^2 * ∑ a ∈ (univ : Finset V), c a^2 ≤ l^2*D :=
    mul_le_mul_of_nonneg_left hsq (sq_nonneg l)
  have hexp : -(l*(η*L)) + l^2*D = -(η^2*L^2/(4*D)) := by
    dsimp [l]
    field_simp
    ring
  calc
    _ ≤ bprob q univ (fun W => f W ≤ bexp q univ f - η*L) := hmono
    _ ≤ Real.exp (-(l*(η*L)) + l^2 * ∑ a ∈ (univ : Finset V), c a^2) := ht
    _ ≤ Real.exp (-(l*(η*L)) + l^2*D) := Real.exp_le_exp.mpr (by linarith)
    _ = _ := by rw [hexp]

/-- The matching relative upper-tail estimate. Its influence and variance
budget is explicit, so later sampling tests can choose summable tolerances. -/
theorem relative_upper_tail (q η U D : ℝ) (c : V → ℝ) (f : Finset V → ℝ)
    (hq0 : 0 ≤ q) (hq1 : q ≤ 1) (hη : 0 < η)
    (hU : 0 < U) (hD : 0 < D)
    (hf : ∀ W ⊆ (univ : Finset V), ∀ a ∈ (univ : Finset V), a ∉ W →
      |f (insert a W) - f W| ≤ c a)
    (hinfluence : ∀ a, (η*U/(2*D))*c a ≤ 1)
    (hmean : bexp q univ f ≤ U)
    (hsq : ∑ a ∈ (univ : Finset V), c a ^ 2 ≤ D) :
    bprob q univ (fun W => (1+η)*U ≤ f W) ≤
      Real.exp (-(η^2*U^2/(4*D))) := by
  let l : ℝ := η*U/(2*D)
  have hl : 0 ≤ l := by dsimp [l]; positivity
  have ht := tail_upper hq0 hq1 c hl univ f hf (fun a _ => hinfluence a) (η*U)
  have hmono : bprob q univ (fun W => (1+η)*U ≤ f W) ≤
      bprob q univ (fun W => bexp q univ f + η*U ≤ f W) := by
    apply bprob_mono hq0 hq1
    intro W hW
    nlinarith [hmean]
  have hsq' : l^2 * ∑ a ∈ (univ : Finset V), c a^2 ≤ l^2*D :=
    mul_le_mul_of_nonneg_left hsq (sq_nonneg l)
  have hexp : -(l*(η*U)) + l^2*D = -(η^2*U^2/(4*D)) := by
    dsimp [l]
    field_simp
    ring
  calc
    _ ≤ bprob q univ (fun W => bexp q univ f + η*U ≤ f W) := hmono
    _ ≤ Real.exp (-(l*(η*U)) + l^2 * ∑ a ∈ (univ : Finset V), c a^2) := ht
    _ ≤ Real.exp (-(l*(η*U)) + l^2*D) := Real.exp_le_exp.mpr (by linarith)
    _ = _ := by rw [hexp]

/-- Relative containment-count tail with explicit maximum vertex influence.
Unlike the half-retention bound, `η` can be made arbitrarily small before the
host is chosen. The estimate uses the total number of candidate objects as
well as the guaranteed lower count `L`. -/
theorem count_tail_relative (q η : ℝ) {ι : Type*} [DecidableEq ι]
    (I : Finset ι) (e : ι → Finset V) {r : ℕ} (hr : 0 < r)
    (her : ∀ i ∈ I, (e i).card ≤ r) {Δ L : ℝ}
    (hΔ : 0 < Δ) (hdeg : ∀ a : V,
      ((I.filter fun i => a ∈ e i).card : ℝ) ≤ Δ)
    (hL : 0 < L) (hLI : L ≤ I.card)
    (hq : 0 < q) (hq1 : q ≤ 1) (hη : 0 < η) (hη1 : η ≤ 1) :
    bprob q univ (fun W => (ccount I e W : ℝ) < (1-η)*L*q^r) ≤
      Real.exp (-(η^2*L^2*q^(2*r)/(4*Δ*r*I.card))) := by
  let c : V → ℝ := fun a => (I.filter fun i => a ∈ e i).card
  let f : Finset V → ℝ := fun W => ccount I e W
  let L' : ℝ := L*q^r
  let D : ℝ := Δ*r*I.card
  have hrR : (0:ℝ) < r := by exact_mod_cast hr
  have hI : (0:ℝ) < I.card := lt_of_lt_of_le hL hLI
  have hqr : 0 < q^r := pow_pos hq _
  have hqr1 : q^r ≤ 1 := pow_le_one₀ hq.le hq1
  have hL' : 0 < L' := by dsimp [L']; positivity
  have hD : 0 < D := by dsimp [D]; positivity
  have hf : ∀ W ⊆ (univ : Finset V), ∀ a ∈ (univ : Finset V), a ∉ W →
      |f (insert a W) - f W| ≤ c a := by
    intro W _ a _ _
    exact ccount_diff I e W a
  have hmean : L' ≤ bexp q univ f := by
    have hbase : (I.card:ℝ)*q^r ≤ bexp q univ f := by
      have heq : f = fun W => ∑ i ∈ I, (if e i ⊆ W then (1:ℝ) else 0) := by
        ext W; simp only [f, ccount]; rw [Finset.sum_boole]
      rw [heq, bexp_sum, ← nsmul_eq_mul, ← Finset.sum_const]
      apply Finset.sum_le_sum
      intro i hi
      rw [bexp_subset_ind univ (e i) (Finset.subset_univ _)]
      exact pow_le_pow_of_le_one hq.le hq1 (her i hi)
    exact (mul_le_mul_of_nonneg_right hLI hqr.le).trans hbase
  have hsq : ∑ a ∈ (univ : Finset V), c a^2 ≤ D := by
    have h1 : ∑ a ∈ (univ : Finset V), c a^2 ≤
        ∑ a ∈ (univ : Finset V), Δ*c a := by
      apply Finset.sum_le_sum
      intro a _
      have hc : 0 ≤ c a := Nat.cast_nonneg _
      rw [sq]
      exact mul_le_mul_of_nonneg_right (hdeg a) hc
    have h2 : ∑ a ∈ (univ : Finset V), c a =
        ∑ i ∈ I, ((e i).card : ℝ) := by
      simp only [c]
      have hb := Finset.sum_card_bipartiteAbove_eq_sum_card_bipartiteBelow
        (s := (univ : Finset V)) (t := I) (r := fun a i => a ∈ e i)
      simp only [Finset.bipartiteAbove, Finset.bipartiteBelow] at hb
      exact_mod_cast (hb.trans (Finset.sum_congr rfl fun i _ => by
        congr 1; ext a; simp))
    have h3 : ∑ i ∈ I, ((e i).card : ℝ) ≤ (r:ℝ)*I.card := by
      calc
        _ ≤ ∑ _i ∈ I, (r:ℝ) :=
          Finset.sum_le_sum fun i hi => by exact_mod_cast her i hi
        _ = (r:ℝ)*I.card := by rw [Finset.sum_const, nsmul_eq_mul, mul_comm]
    rw [← Finset.mul_sum, h2] at h1
    calc
      _ ≤ Δ*∑ i ∈ I, ((e i).card : ℝ) := h1
      _ ≤ Δ*((r:ℝ)*I.card) := mul_le_mul_of_nonneg_left h3 hΔ.le
      _ = D := by dsimp [D]; ring
  have hinfluence : ∀ a : V, (η*L'/(2*D))*c a ≤ 1 := by
    intro a
    have hc := hdeg a
    have hl : 0 ≤ η*L'/(2*D) := by positivity
    calc
      _ ≤ (η*L'/(2*D))*Δ := mul_le_mul_of_nonneg_left hc hl
      _ = η*L*q^r/(2*(r:ℝ)*I.card) := by dsimp [L',D]; field_simp
      _ ≤ 1 := by
        apply (div_le_one (by positivity)).mpr
        have hηL : η*L ≤ L := by nlinarith [mul_le_mul_of_nonneg_right hη1 hL.le]
        have hprod : η*L*q^r ≤ (I.card:ℝ) := by
          calc
            _ ≤ L*q^r := mul_le_mul_of_nonneg_right hηL hqr.le
            _ ≤ L := by simpa only [mul_one] using mul_le_mul_of_nonneg_left hqr1 hL.le
            _ ≤ I.card := hLI
        have hr1 : (1:ℝ) ≤ r := by exact_mod_cast hr
        have hI0 : (0:ℝ) ≤ I.card := Nat.cast_nonneg _
        nlinarith [hprod, mul_nonneg (show 0 ≤ 2*(r:ℝ)-1 by linarith) hI0]
  have htail := relative_lower_tail q η L' D c f hq.le hq1 hη hL' hD
    hf hinfluence hmean hsq
  have hpow : q^(2*r) = (q^r)^2 := by
    rw [show 2*r = r*2 by omega, pow_mul]
  calc
    _ = bprob q univ (fun W => f W < (1-η)*L') := by
      congr 1; funext W; dsimp [f,L']; ring
    _ ≤ Real.exp (-(η^2*L'^2/(4*D))) := htail
    _ = _ := by
      congr 1
      dsimp [L',D]
      rw [hpow, mul_pow]
      ring

/-- Relative retention of a prescribed pool of candidate third vertices. -/
theorem pool_tail_relative (q η β : ℝ) (P : Finset V)
    (hq : 0 < q) (hq1 : q ≤ 1) (hη : 0 < η) (hη1 : η ≤ 1)
    (hβ : 0 < β) (hn : 0 < Fintype.card V)
    (hP : β*Fintype.card V ≤ P.card) :
    bprob q univ (fun W => ((P∩W).card:ℝ) < (1-η)*(β*Fintype.card V)*q) ≤
      Real.exp (-(η^2*(β*Fintype.card V)^2*q^2/(4*P.card))) := by
  have hL : 0 < β*(Fintype.card V:ℝ) := by positivity
  have hdeg : ∀ a : V, ((P.filter fun i => a ∈ ({i}:Finset V)).card:ℝ) ≤ 1 := by
    intro a
    have hs : (P.filter fun i => a ∈ ({i}:Finset V)) ⊆ {a} := by
      intro i hi
      simp only [mem_filter, mem_singleton] at hi ⊢
      exact hi.2.symm
    exact_mod_cast (card_le_card hs).trans (by simp)
  have ht := count_tail_relative q η P (fun i => ({i}:Finset V))
    (r := 1) (by norm_num) (by simp) (Δ := 1) (L := β*Fintype.card V)
    (by norm_num) hdeg hL hP hq hq1 hη hη1
  simpa only [ccount_singleton, pow_one, one_mul, mul_one, Nat.cast_one]
    using ht

/-- A sampled core exceeds `(1+η)q|V|` only with exponentially small
probability. Together with the pool bound for `P=univ`, this gives a child
size window with adjustable relative slack. -/
theorem size_upper_tail_relative (q η : ℝ)
    (hq : 0 < q) (hq1 : q ≤ 1) (hη : 0 < η) (hη1 : η ≤ 1)
    (hn : 0 < Fintype.card V) :
    bprob q (univ : Finset V) (fun W => (1+η)*q*Fintype.card V ≤ (W.card:ℝ)) ≤
      Real.exp (-(η^2*q^2*Fintype.card V/4)) := by
  let c : V → ℝ := fun _ => 1
  let f : Finset V → ℝ := fun W => W.card
  let U : ℝ := q*Fintype.card V
  let D : ℝ := Fintype.card V
  have hU : 0 < U := by dsimp [U]; positivity
  have hD : 0 < D := by dsimp [D]; exact_mod_cast hn
  have hf : ∀ W ⊆ (univ : Finset V), ∀ a ∈ (univ : Finset V), a ∉ W →
      |f (insert a W)-f W| ≤ c a := by
    intro W _ a _ ha
    simp [f,c,Finset.card_insert_of_notMem ha]
  have hinfluence : ∀ a : V, (η*U/(2*D))*c a ≤ 1 := by
    intro a
    simp only [c, mul_one]
    dsimp [U,D]
    have hnR : (0:ℝ) < Fintype.card V := by exact_mod_cast hn
    have hp : η*q ≤ 1 := by nlinarith [mul_le_mul_of_nonneg_right hη1 hq.le,
      mul_le_mul_of_nonneg_left hq1 hη.le]
    apply (div_le_one (by positivity)).mpr
    nlinarith [mul_le_mul_of_nonneg_right hp hnR.le]
  have hmean : bexp q univ f ≤ U := by
    dsimp [f,U]
    rw [bexp_card]
  have hsq : ∑ a ∈ (univ : Finset V), c a^2 ≤ D := by
    simp [c,D]
  have ht := relative_upper_tail q η U D c f hq.le hq1 hη hU hD
    hf hinfluence hmean hsq
  have hEvent : bprob q univ (fun W : Finset V =>
      (1+η)*q*Fintype.card V ≤ (W.card:ℝ)) =
      bprob q univ (fun W => (1+η)*U ≤ f W) := by
    unfold bprob
    apply bexp_congr
    intro W _
    congr 1
    dsimp [U,f]
    ring
  rw [hEvent]
  calc
    _ ≤ Real.exp (-(η^2*U^2/(4*D))) := ht
    _ = _ := by
      congr 1
      dsimp [U,D]
      field_simp

#print axioms relative_lower_tail
#print axioms relative_upper_tail
#print axioms count_tail_relative
#print axioms pool_tail_relative
#print axioms size_upper_tail_relative

end TypedTriangle.RawReference
