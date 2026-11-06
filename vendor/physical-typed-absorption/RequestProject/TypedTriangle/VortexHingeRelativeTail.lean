/-
Copyright (c) 2026 Juan Pablo Traverso Gianini.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module
public import RequestProject.TypedTriangle.UniformSampleTail
public import RequestProject.S07.HingeCore
public import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
set_option maxHeartbeats 4000000 -- build option (original: -DmaxHeartbeats=1600000; raised)
set_option maxRecDepth 16384 -- build option (original: -DmaxRecDepth=8192; raised)
@[expose] public section

/-! A relative, adjustable tail for one H4 hinge family. Its roots are fixed
before the Bernoulli sample and are not counted as free vertices. -/

open Finset Classical S07V24 TypedTriangle.SparseEdge
noncomputable section

namespace TypedTriangle.RawReference

private theorem hinge_card_upper {V I : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} {lab : V → I} {F : Set (Multiset I)}
    {u v a b : V} {i : ℕ}
    (hd : u ≠ v ∧ u ≠ a ∧ v ≠ a ∧ u ≠ b ∧ v ≠ b ∧ a ≠ b) :
    ((hinges G lab F u v a b i).card : ℝ) ≤
      (2:ℝ)^(i.choose 2)*(Fintype.card V : ℝ)^(i-4) := by
  obtain ⟨huv, hua, hva, hub, hvb, hab⟩ := hd
  have h := S10V23.card_hinges_forced huv hua hva hub hvb hab i
    (∅ : Finset V) (by simp) (hinges G lab F u v a b i)
    (Finset.Subset.rfl) (by simp)
  simpa only [Finset.card_empty, add_zero] using h

theorem hinge_tail_relative {V I : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} {lab : V → I} {F : Set (Multiset I)}
    {α q η : ℝ} {u v a b : V} {i : ℕ}
    (hd : u ≠ v ∧ u ≠ a ∧ v ≠ a ∧ u ≠ b ∧ v ≠ b ∧ a ≠ b)
    (hi6 : 6 ≤ i) (hα : 0 < α) (hq : 0 < q) (hq1 : q ≤ 1)
    (hη : 0 < η) (hη1 : η ≤ 1) (hn : 0 < Fintype.card V)
    (hcount : α * (Fintype.card V : ℝ)^(i-4) ≤
      (hinges G lab F u v a b i).card) :
    bprob q univ (fun W =>
      (ccount (hinges G lab F u v a b i) (freeV u v a b) W : ℝ) <
        (1-η)*(α*(Fintype.card V : ℝ)^(i-4))*q^(i-4)) ≤
      Real.exp (-(η^2*(α*(Fintype.card V : ℝ)^(i-4))^2*q^(2*(i-4)) /
        (4*((2:ℝ)^(i.choose 2)*(Fintype.card V : ℝ)^(i-5))*((i-4:ℕ):ℝ)*
          (hinges G lab F u v a b i).card))) := by
  have hr : 0 < i-4 := by omega
  have hΔ : 0 < (2:ℝ)^(i.choose 2)*(Fintype.card V : ℝ)^(i-5) := by
    have hnR : (0:ℝ) < Fintype.card V := by exact_mod_cast hn
    positivity
  have hL : 0 < α*(Fintype.card V : ℝ)^(i-4) := by
    have hnR : (0:ℝ) < Fintype.card V := by exact_mod_cast hn
    positivity
  have ht := count_tail_relative q η (hinges G lab F u v a b i)
    (freeV u v a b) hr (fun J hJ => (card_freeV hd hJ).le)
    hΔ (hinge_free_deg hd i)
    hL hcount hq hq1 hη hη1
  exact ht

private theorem hinge_exponent_identity (α η Q C T N R : ℝ)
    (hC : C ≠ 0) (hT : T ≠ 0) (hN : N ≠ 0) (hR : R ≠ 0) :
    η^2*(α*(T*N))^2*Q/(4*(C*T)*R*(C*T*N)) =
      η^2*α^2*Q*N/(4*C^2*R) := by
  field_simp

theorem hinge_tail_linear {V I : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} {lab : V → I} {F : Set (Multiset I)}
    {α q η : ℝ} {u v a b : V} {i : ℕ}
    (hd : u ≠ v ∧ u ≠ a ∧ v ≠ a ∧ u ≠ b ∧ v ≠ b ∧ a ≠ b)
    (hi6 : 6 ≤ i) (hα : 0 < α) (hq : 0 < q) (hq1 : q ≤ 1)
    (hη : 0 < η) (hη1 : η ≤ 1) (hn : 0 < Fintype.card V)
    (hcount : α * (Fintype.card V : ℝ)^(i-4) ≤
      (hinges G lab F u v a b i).card) :
    bprob q univ (fun W =>
      (ccount (hinges G lab F u v a b i) (freeV u v a b) W : ℝ) <
        (1-η)*(α*(Fintype.card V : ℝ)^(i-4))*q^(i-4)) ≤
      Real.exp (-(η^2*α^2*q^(2*(i-4))*(Fintype.card V : ℝ) /
        (4*((2:ℝ)^(i.choose 2))^2*((i-4:ℕ):ℝ)))) := by
  let N : ℝ := Fintype.card V
  let C : ℝ := (2:ℝ)^(i.choose 2)
  let T : ℝ := N^(i-5)
  let R : ℝ := (i-4:ℕ)
  let Q : ℝ := q^(2*(i-4))
  have hN : 0 < N := by dsimp [N]; exact_mod_cast hn
  have hC : 0 < C := by dsimp [C]; positivity
  have hT : 0 < T := pow_pos hN _
  have hR : 0 < R := by dsimp [R]; exact_mod_cast (show 0 < i-4 by omega)
  have hI : ((hinges G lab F u v a b i).card : ℝ) ≤ C*T*N := by
    have hu := hinge_card_upper (G := G) (lab := lab) (F := F) (i := i) hd
    have hp : N^(i-4) = T*N := by
      dsimp [T]
      rw [← pow_succ]
      congr 1
      omega
    simpa only [C, N, hp, mul_assoc] using hu
  have hIpos : (0:ℝ) < (hinges G lab F u v a b i).card := by
    have hL : 0 < α*N^(i-4) := by positivity
    exact lt_of_lt_of_le hL (by simpa only [N] using hcount)
  have hfrac :
      η^2*(α*(T*N))^2*Q/(4*(C*T)*R*(C*T*N)) ≤
        η^2*(α*(T*N))^2*Q/(4*(C*T)*R*(hinges G lab F u v a b i).card) := by
    gcongr
  have heq := hinge_exponent_identity α η Q C T N R hC.ne' hT.ne' hN.ne' hR.ne'
  have hp : N^(i-4) = T*N := by
    dsimp [T]
    rw [← pow_succ]
    congr 1
    omega
  calc
    _ ≤ Real.exp (-(η^2*(α*N^(i-4))^2*Q /
        (4*(C*T)*R*(hinges G lab F u v a b i).card))) := by
          simpa only [N, C, T, R, Q] using
            (hinge_tail_relative hd hi6 hα hq hq1 hη hη1 hn hcount)
    _ ≤ Real.exp (-(η^2*(α*(T*N))^2*Q/(4*(C*T)*R*(C*T*N)))) := by
      rw [hp]
      exact Real.exp_le_exp.mpr (neg_le_neg hfrac)
    _ = _ := by
      rw [heq]

/-- A fixed polynomial family of tests fits in a stretched-exponential
sampling budget. This is the asymptotic input for all H4 root quadruples. -/
theorem polynomial_sqrt_budget (d : ℕ) (c : ℝ) (hc : 0 < c) :
    ∃ N : ℝ, ∀ x : ℝ, N ≤ x →
      (x^d + 2)*Real.exp (-c*Real.sqrt x) < 1 := by
  have h1 : Filter.Tendsto
      (fun t : ℝ => t^(2*d)*Real.exp (-c*t)) Filter.atTop (nhds 0) := by
    simpa only [Real.rpow_natCast] using
      (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (2*d : ℕ) c hc)
  have h0 : Filter.Tendsto
      (fun t : ℝ => Real.exp (-c*t)) Filter.atTop (nhds 0) := by
    simpa using (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (0:ℝ) c hc)
  have hsum : Filter.Tendsto
      (fun t : ℝ => (t^(2*d)+2)*Real.exp (-c*t)) Filter.atTop (nhds 0) := by
    simpa only [zero_add, mul_zero, add_zero, ← add_mul] using
      h1.add (h0.const_mul 2)
  have hcomp := hsum.comp Real.tendsto_sqrt_atTop
  have hcongr :
      (fun x : ℝ => (x^d+2)*Real.exp (-c*Real.sqrt x)) =ᶠ[Filter.atTop]
      (fun x : ℝ => ((Real.sqrt x)^(2*d)+2)*Real.exp (-c*Real.sqrt x)) := by
    filter_upwards [Filter.eventually_ge_atTop (0:ℝ)] with x hx
    have hpow : (Real.sqrt x)^(2*d) = x^d := by
      rw [pow_mul, Real.sq_sqrt hx]
    rw [hpow]
  have hfinal : Filter.Tendsto
      (fun x : ℝ => (x^d+2)*Real.exp (-c*Real.sqrt x))
      Filter.atTop (nhds 0) := hcomp.congr' hcongr.symm
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.1
    (hfinal.eventually (gt_mem_nhds zero_lt_one))
  exact ⟨N, fun x hx => hN x hx⟩

#print axioms hinge_tail_relative
#print axioms hinge_tail_linear
#print axioms polynomial_sqrt_budget

end TypedTriangle.RawReference
