/-
Copyright (c) 2026 Juan Pablo Traverso Gianini.
Released under Apache 2.0 license.
Authors: Juan Pablo Traverso Gianini
-/
module
public import CDRIIILib.KBicolor.PrescribedCounting.ReferenceCross
public import CDRIIILib.KBicolor.PrescribedCounting.ModularResidual
public import CDRIIILib.KBicolor.PrescribedCounting.ReserveTrades
public import CDRIIILib.KBicolor.PrescribedCounting.ResidualQuotas
public import CDRIIILib.KBicolor.PrescribedCounting.GroupEntropyAssembly
public import CDRIIILib.KBicolor.PrescribedCounting.CoreBounds

/-! # Exact prescribed counting on a concretely completable Wilson core -/
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace CDRBicolour.KBicolor.PrescribedCounting
open Finset Classical TypedTriangle CDRBicolour.Absorption CDRBicolour.Absorption.Exact
open CDRBicolour.KBicolor.Wilson
variable {A : Type} [Fintype A] [DecidableEq A] {k n g t p : ℕ}
variable {lab : Fin n → Fin k} {κ : A → Fin k}

theorem fixed_core_prescribed_count (h : Setup lab κ g t) {S : Finset (Finset (Fin g))}
    (hS : _root_.STS.IsSTS S) (Λold : LFam A S t) (o : Fin k)
    [Fact p.Prime] (hp : 8 < p) (P : Place lab (Coord o) p) (hτ : P.τ=tau3 o)
    (hPR : ∀ a, P.ψ a ∈ reserve h)
    (hcomplete : ∃ E, IsDecomposition
      (residual (rHostK lab ((crossP h Λold).biUnion triEdges)) (leaveG P)) (bicF k)
      (edges (residual (rHostK lab ((crossP h Λold).biUnion triEdges)) (leaveG P))) E)
    (hn : 1 ≤ n) (ht : 0 < t) (hB : 0 < groupOrder A t)
    (hcls : ∀ i, 1 ≤ Hilton.csize κ i)
    {θ ζ : ℝ} (hθ : 0 ≤ θ) (hθ1 : θ ≤ 1) (hgθ : 1 ≤ θ*g) (hθζ : θ ≤ ζ)
    (hcover : (1-θ)*n ≤ (g : ℝ)*groupOrder A t)
    (target : Fin k → Fin k → ℕ)
    (hpair : ∀ i j, i ≠ j → 2*(target i j+target j i)=ksz lab i*ksz lab j)
    (hrow : ∀ i, 2*∑ j ∈ univ.filter (fun j => j ≠ i), target i j=ksz lab i*(ksz lab i-1))
    (hlow : ∀ i j, i ≠ j → ζ*(n : ℝ)^2 ≤ target i j) :
    let tv : TypeCoord k → ℕ := fun q => target q.1.1 q.1.2
    0 < exactTypeCount lab tv ∧
      (Fintype.card (VariableCross.Block S) : ℝ)*(groupOrder A t : ℝ)^2*(Real.log t-2) ≤
        Real.log (exactTypeCount lab tv) := by
  intro tv
  let e := groupEmbedding h
  let cls := groupLabels κ t
  let O := Fintype.card (VariableCross.Block S)
  obtain ⟨Λref,x,hx,hC,hCx⟩ := exists_reference_cross h hS
  let C := VariableCross.packing e Λref
  have hCE : C.biUnion triEdges=(crossP h Λold).biUnion triEdges := flattened_cross_edges h hS Λref Λold
  have hQ : ∀ σ, IsPacking (rHostK lab (C.biUnion triEdges)) (bicF k) (packG P σ) := by
    intro σ
    rw [hCE]
    exact reserve_trade_packing h hS Λold hp P hPR σ
  obtain ⟨E,hE⟩ := hcomplete
  rw [← hCE] at hE
  have hCdiv : ∀ i j, i ≠ j → 3 ∣ kTypeCount lab C i j := by
    intro i j hij
    rw [hCx i j hij]
    exact dvd_mul_right _ _
  obtain ⟨R,hR,hRmod⟩ := modular_residual lab o hp P hτ C hC hCdiv hQ E hE target hpair hrow
  have hfull := union_decomp lab hC.1 hC.2 hR
  have hRC : Disjoint R C := (VariableCross.packing_disjoint_residual e lab Λref hR.1).symm
  have hsmall := residual_small_of_coverage e hS lab Λref R hfull hRC hn hθ hθ1 hgθ hcover
  have hRlow : ∀ i j, i ≠ j → kTypeCount lab R i j ≤ target i j := by
    intro i j hij
    have hc : (kTypeCount lab R i j : ℝ) ≤ #R := by exact_mod_cast card_filter_le R _
    have hz : θ*(n : ℝ)^2 ≤ ζ*(n : ℝ)^2 := mul_le_mul_of_nonneg_right hθζ (sq_nonneg _)
    have hh : (kTypeCount lab R i j : ℝ) ≤ target i j := by nlinarith [hlow i j hij]
    exact_mod_cast hh
  have hadd : ∀ i j, kTypeCount lab (R ∪ C) i j=kTypeCount lab R i j+kTypeCount lab C i j := by
    intro i j
    unfold kTypeCount
    rw [filter_union,card_union_of_disjoint (disjoint_filter_filter hRC)]
  have hPair : ∀ i j, i ≠ j → target i j+target j i=
      (kTypeCount lab R i j+kTypeCount lab C i j)+(kTypeCount lab R j i+kTypeCount lab C j i) := by
    intro i j hij
    have h1 := typeCount_pair lab hfull hij
    change 2*(kTypeCount lab (R ∪ C) i j+kTypeCount lab (R ∪ C) j i)=_ at h1
    simp_rw [hadd] at h1
    have h2 := hpair i j hij
    omega
  have hRow : ∀ i, (∑ j ∈ univ.filter (fun j => j ≠ i), target i j)=
      ∑ j ∈ univ.filter (fun j => j ≠ i), (kTypeCount lab R i j+kTypeCount lab C i j) := by
    intro i
    have h1 := typeCount_row lab hfull i
    change 2*∑ j ∈ univ.filter (fun j => j ≠ i), kTypeCount lab (R ∪ C) i j=_ at h1
    simp_rw [hadd] at h1
    have h2 := hrow i
    omega
  have hcPair : ∀ i j, i ≠ j → kTypeCount lab C i j+kTypeCount lab C j i=
      3*(O*(Hilton.csize cls i*Hilton.csize cls j)) := by
    intro i j hij
    rw [hCx i j hij,hCx j i hij.symm]
    have hh := hx.pair i j hij
    dsimp only [O,cls]
    nlinarith
  have hcRow : ∀ i, (∑ j ∈ univ.filter (fun j => j ≠ i), kTypeCount lab C i j)=
      3*(O*(Hilton.csize cls i*Hilton.csize cls i)) := by
    intro i
    have he : ∀ j ∈ univ.filter (fun j => j ≠ i), kTypeCount lab C i j=3*(O*x i j) :=
      fun j hj => hCx i j (mem_filter.mp hj).2.symm
    rw [sum_congr rfl he,← mul_sum,← mul_sum]
    have hs : (∑ j ∈ univ.filter (fun j => j ≠ i), x i j)=∑ j, x i j := by
      apply sum_subset (filter_subset _ _)
      intro j _ hj
      have hji : j=i := by simpa only [mem_filter,mem_univ,true_and,not_not] using hj
      subst j
      exact hx.diag i
    rw [hs,hx.row]
  obtain ⟨y,hy,hquota⟩ := extract_residual_quotas O (Hilton.csize cls)
    (kTypeCount lab R) (kTypeCount lab C) target hRlow hRmod hPair hRow hcPair hcRow
  let y' : VariableCross.Block S → Fin k → Fin k → ℕ := fun a => y (Fintype.equivFin _ a)
  have hquota' : ∀ i j, i ≠ j → kTypeCount lab R i j+∑ a, 3*y' a i j=target i j := by
    intro i j hij
    dsimp only [y']
    rw [show (∑ a : VariableCross.Block S, 3*y (Fintype.equivFin _ a) i j)=
      ∑ a : Fin O, 3*y a i j from Equiv.sum_comp (Fintype.equivFin _) (fun a : Fin O => 3*y a i j)]
    exact hquota i j hij
  have hmin : ∀ i, t ≤ Hilton.csize cls i := by
    intro i
    rw [groupLabels_size]
    have hh := Nat.mul_le_mul_right t (hcls i)
    simpa only [one_mul] using hh
  exact prescribed_group_entropy e hS lab cls (groupEmbedding_label h) Λref R hR target y'
    (fun a => hy _) hquota' hB ht hmin

end CDRBicolour.KBicolor.PrescribedCounting
