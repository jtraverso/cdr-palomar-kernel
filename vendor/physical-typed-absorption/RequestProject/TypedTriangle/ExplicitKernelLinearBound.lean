/-
Copyright (c) 2026 Juan Pablo Traverso Gianini.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module
public import RequestProject.TypedTriangle.GroupingKernelExplicitBound
set_option maxHeartbeats 4000000 -- build option (original: -DmaxHeartbeats=1600000; raised)
set_option maxRecDepth 16384 -- build option (original: -DmaxRecDepth=8192; raised)
@[expose] public section

open Finset Classical
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 400000

namespace TypedTriangle.GroupingExplicit

/-- Extract a bounded nonzero subkernel without an irreducibility premise. -/
theorem kernel_small_subvector {ι : Type} [Fintype ι] (d D : ℕ)
    (A : ι → Fin d → ℤ) (u : ι → ℕ)
    (hA : ∀ i k, |A i k| ≤ (D : ℤ)) (hu : u ≠ 0)
    (hzero : (∑ i, (u i : ℤ) • A i) = 0)
    : ∃ v : ι → ℕ, v ≤ u ∧ v ≠ 0 ∧
      (∑ i, (v i : ℤ) • A i) = 0 ∧ (∑ i, v i) ≤ kernelBound d D := by
  let Ω := Σ i : ι, Fin (u i)
  have hΩ : (univ : Finset Ω).Nonempty := by
    obtain ⟨i,hi⟩ := Function.ne_iff.mp hu
    have hipos : 0 < u i := Nat.pos_of_ne_zero (by
      simpa only [Pi.zero_apply] using hi)
    exact ⟨⟨i,⟨0,hipos⟩⟩,mem_univ _⟩
  have hAll : (∑ x : Ω, A x.1) = 0 := by
    simpa only [Ω, Fintype.sum_sigma, sum_const, card_univ, Fintype.card_fin,
      Nat.cast_smul_eq_nsmul] using hzero
  obtain ⟨J,_,hJne,hJcard,hJsum⟩ :=
    vector_zero_sum_small_block d D (fun x : Ω => A x.1) univ
      (fun x _ k => hA x.1 k) hΩ hAll
  let fibre : (i : ι) → Finset (Fin (u i)) :=
    fun i => univ.filter (fun j => (⟨i,j⟩ : Ω) ∈ J)
  let v : ι → ℕ := fun i => (fibre i).card
  have hle : v ≤ u := by
    intro i
    calc
      v i ≤ (univ : Finset (Fin (u i))).card := card_filter_le _ _
      _ = u i := by simp
  have hv : v ≠ 0 := by
    obtain ⟨⟨i,j⟩,hij⟩ := hJne
    have hvi : 0 < v i := card_pos.mpr ⟨j,by simp only [fibre,mem_filter,mem_univ,true_and]; exact hij⟩
    intro h
    have hi := congrFun h i
    simp only [Pi.zero_apply] at hi
    omega
  have hSigma : univ.sigma fibre = J := by
    ext x
    rcases x with ⟨i,j⟩
    simp only [mem_sigma,mem_univ,true_and,fibre,mem_filter]
  have hCard : (∑ i, v i) = J.card := by
    rw [← hSigma,card_sigma]
  have hCharge : (∑ i, (v i : ℤ) • A i) = ∑ x ∈ J, A x.1 := by
    rw [← hSigma,Finset.sum_sigma]
    simp only [sum_const,Nat.cast_smul_eq_nsmul,v]
  exact ⟨v,hle,hv,hCharge.trans hJsum,hCard.trans_le hJcard⟩

/-- If every nonzero subkernel uses a demanded token, bounded zero-sum
blocks give a uniform linear bound in the total demanded multiplicity. -/
theorem kernel_flag_bound {ι : Type} [Fintype ι] (d D : ℕ)
    (A : ι → Fin d → ℤ) (u : ι → ℕ) (demand : Finset ι)
    (hA : ∀ i k, |A i k| ≤ (D : ℤ))
    (hzero : (∑ i, (u i : ℤ) • A i) = 0)
    (hDemand : ∀ v : ι → ℕ, v ≤ u → v ≠ 0 →
      (∑ i, (v i : ℤ) • A i) = 0 → 0 < ∑ i ∈ demand, v i) :
    (∑ i, u i) ≤ kernelBound d D * ∑ i ∈ demand, u i := by
  suffices h : ∀ n : ℕ, ∀ u : ι → ℕ, (∑ i,u i) = n →
      (∑ i, (u i : ℤ) • A i) = 0 →
      (∀ v : ι → ℕ, v ≤ u → v ≠ 0 →
        (∑ i, (v i : ℤ) • A i) = 0 → 0 < ∑ i ∈ demand,v i) →
      (∑ i,u i) ≤ kernelBound d D * ∑ i ∈ demand,u i by
    exact h _ u rfl hzero hDemand
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro u hnorm hzero hDemand
    by_cases hu : u = 0
    · simp [hu]
    obtain ⟨v,hvu,hv,hvzero,hvsize⟩ := kernel_small_subvector d D A u hA hu hzero
    let w : ι → ℕ := fun i => u i - v i
    have hwu : w ≤ u := fun i => Nat.sub_le _ _
    have hsplit : ∀ i, w i + v i = u i := fun i => Nat.sub_add_cancel (hvu i)
    have htotal : (∑ i,w i) + (∑ i,v i) = ∑ i,u i := by
      rw [← sum_add_distrib]
      exact sum_congr rfl (fun i _ => hsplit i)
    have hvpos : 0 < ∑ i,v i := by
      obtain ⟨i,hi⟩ := Function.ne_iff.mp hv
      have hipos : 0 < v i := Nat.pos_of_ne_zero (by simpa only [Pi.zero_apply] using hi)
      exact hipos.trans_le (single_le_sum (fun j _ => Nat.zero_le (v j)) (mem_univ i))
    have hwsmall : (∑ i,w i) < n := by omega
    have hwzero : (∑ i,(w i : ℤ) • A i) = 0 := by
      have heq : (∑ i,(w i : ℤ) • A i) + (∑ i,(v i : ℤ) • A i) =
          ∑ i,(u i : ℤ) • A i := by
        rw [← sum_add_distrib]
        apply sum_congr rfl
        intro i _
        rw [← add_smul,← Nat.cast_add,hsplit i]
      simpa only [hvzero,hzero,add_zero] using heq
    have hWbound := ih _ hwsmall w rfl hwzero
      (fun v' hv'w hv' hz => hDemand v' (le_trans hv'w hwu) hv' hz)
    have hDemandPos := hDemand v hvu hv hvzero
    have hdemand : (∑ i ∈ demand,w i) + (∑ i ∈ demand,v i) = ∑ i ∈ demand,u i := by
      rw [← sum_add_distrib]
      exact sum_congr rfl (fun i _ => hsplit i)
    calc
      (∑ i,u i) = (∑ i,w i) + (∑ i,v i) := htotal.symm
      _ ≤ kernelBound d D * (∑ i ∈ demand,w i) + kernelBound d D :=
        Nat.add_le_add hWbound hvsize
      _ ≤ kernelBound d D * (∑ i ∈ demand,w i) +
          kernelBound d D * (∑ i ∈ demand,v i) := by
        exact Nat.add_le_add_left (by simpa using Nat.mul_le_mul_left (kernelBound d D) hDemandPos) _
      _ = kernelBound d D * (∑ i ∈ demand,u i) := by rw [← Nat.mul_add,hdemand]

#print axioms kernel_small_subvector
#print axioms kernel_flag_bound

theorem kernel_demand_bound {ι : Type} [Fintype ι] (d D : ℕ)
    (A : ι → Fin d → ℤ) (u : ι → ℕ) (demand : ι → Prop) [DecidablePred demand]
    (hA : ∀ i k, |A i k| ≤ (D : ℤ))
    (hzero : (∑ i, (u i : ℤ) • A i) = 0)
    (hDemand : ∀ v : ι → ℕ, v ≤ u → v ≠ 0 →
      (∑ i, (v i : ℤ) • A i) = 0 → 1 ≤ ∑ i ∈ univ.filter demand, v i) :
    (∑ i, u i) ≤ kernelBound d D * ∑ i ∈ univ.filter demand, u i :=
  kernel_flag_bound d D A u (univ.filter demand) hA hzero hDemand

#print axioms kernel_demand_bound
end TypedTriangle.GroupingExplicit
