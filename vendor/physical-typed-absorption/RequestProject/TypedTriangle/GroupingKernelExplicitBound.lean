/-
Copyright (c) 2026 Juan Pablo Traverso Gianini.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module
public import RequestProject.TypedTriangle.GroupingVectorZeroSum
set_option maxHeartbeats 4000000 -- build option (original: -DmaxHeartbeats=1600000; raised)
set_option maxRecDepth 16384 -- build option (original: -DmaxRecDepth=8192; raised)
@[expose] public section

open Finset Classical
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 400000

namespace TypedTriangle.GroupingExplicit

/-- Expand multiplicities into distinct indexed tokens, extract a small
zero-sum family, and use irreducibility to recover the whole vector. -/
theorem kernel_atom_bound {ι : Type} [Fintype ι] (d D : ℕ)
    (A : ι → Fin d → ℤ) (u : ι → ℕ)
    (hA : ∀ i k, |A i k| ≤ (D : ℤ)) (hu : u ≠ 0)
    (hzero : (∑ i, (u i : ℤ) • A i) = 0)
    (hmin : ∀ v : ι → ℕ, v ≤ u → v ≠ 0 →
      (∑ i, (v i : ℤ) • A i) = 0 → v = u) :
    (∑ i, u i) ≤ kernelBound d D := by
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
  have hEqual : v = u := hmin v hle hv (hCharge.trans hJsum)
  calc
    (∑ i,u i) = ∑ i,v i := by rw [hEqual]
    _ = J.card := hCard
    _ ≤ kernelBound d D := hJcard

#print axioms kernel_atom_bound
end TypedTriangle.GroupingExplicit
