/-
Copyright (c) 2026 Juan Pablo Traverso Gianini.
Released under Apache 2.0 license.
Authors: Juan Pablo Traverso Gianini
-/
module
public import CDRIIILib.KBicolor.ReservedSpectrum
public import CDRIIILib.KBicolor.Wilson.Reserve

/-! # A bounded trade supply inside the actual universal reserve -/
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace CDRBicolour.KBicolor.PrescribedCounting
open Finset Classical TypedTriangle CDRBicolour.Absorption CDRBicolour.Absorption.Exact
variable {V : Type} [Fintype V] [DecidableEq V] {k m : ℕ}

theorem exists_place_in_reserve [NeZero m] (lab : V → Fin k) (o : Fin k) (R : Finset V)
    (hsize : ∀ X, 9*Fintype.card (Coord o)*m ≤ #(R.filter fun v => lab v=X)) :
    ∃ P : Place lab (Coord o) m, P.τ=tau3 o ∧ ∀ p, P.ψ p ∈ R := by
  let labR : R → Fin k := fun v => lab v.1
  have hc : ∀ X, ksz labR X=#(R.filter fun v => lab v=X) := by
    intro X
    let e : {v : R // labR v=X} ≃ {v : V // v ∈ R.filter fun v => lab v=X} :=
      { toFun := fun v => ⟨v.1.1,mem_filter.mpr ⟨v.1.2,v.2⟩⟩
        invFun := fun v => ⟨⟨v.1,(mem_filter.mp v.2).1⟩,(mem_filter.mp v.2).2⟩
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl }
    rw [ksz,← Fintype.card_subtype]
    exact (Fintype.card_congr e).trans (Fintype.card_coe _)
  obtain ⟨P,hP⟩ := exists_place labR (tau3 o) (tau3_inj o) (fun X => by rw [hc]; exact hsize X)
  let P' : Place lab (Coord o) m :=
    { τ := P.τ
      τinj := P.τinj
      ψ := fun p => (P.ψ p).1
      ψinj := fun p q he => P.ψinj (Subtype.ext he)
      ψlab := fun j i x => P.ψlab j i x }
  exact ⟨P',hP,fun p => (P.ψ p).2⟩

theorem packG_inside_reserve {lab : V → Fin k} {J : Type} [Fintype J] [DecidableEq J]
    [NeZero m] (P : Place lab J m) (R : Finset V) (hR : ∀ p, P.ψ p ∈ R)
    (σ : J × ZMod m × ZMod m → Bool) : ∀ T ∈ packG P σ, T ⊆ R := by
  intro T hT v hv
  obtain ⟨c,-,hc⟩ := mem_biUnion.mp hT
  obtain ⟨T₀,-,rfl⟩ := mem_halfOfG P hc
  obtain ⟨i,-,rfl⟩ := mem_map.mp hv
  exact hR _

def tradeDegreeBudget (J : Type) [Fintype J] (m : ℕ) : ℕ :=
  3 * #T0m * (Fintype.card J*m*m)

theorem leave_degree_bounded {lab : V → Fin k} {J : Type} [Fintype J] [DecidableEq J]
    [NeZero m] (P : Place lab J m) (v : V) :
    SparseEdge.degIn (leaveG P) v ≤ tradeDegreeBudget J m := by
  let Q := packG P (fun _ => false)
  have hQ : #Q ≤ #T0m*(Fintype.card J*m*m) := by
    calc
      #Q ≤ ∑ c : J × ZMod m × ZMod m, #(halfOfG P (fun _ => false) c) := card_biUnion_le
      _ ≤ ∑ _c : J × ZMod m × ZMod m, #T0m := by
        apply sum_le_sum
        intro c _
        simp only [halfOfG,Bool.false_eq_true,ite_false,half0]
        exact card_image_le
      _ = _ := by simp only [sum_const,card_univ,Fintype.card_prod,ZMod.card,nsmul_eq_mul,Nat.cast_id]; ring
  have hcard : #(leaveG P) ≤ 3*#Q := by
    rw [← packG_leave P (fun _ => false)]
    calc
      _ ≤ ∑ T ∈ Q, #(triEdges T) := card_biUnion_le
      _ = 3*#Q := by
        rw [sum_congr rfl (fun T hT => card_triEdges_three (packG_allowed P (fun _ => false) T hT).1)]
        simp only [sum_const,nsmul_eq_mul,Nat.cast_id]
        dsimp only [Q]
        ring
  have hd : SparseEdge.degIn (leaveG P) v ≤ #(leaveG P) := by
    unfold SparseEdge.degIn
    exact @Finset.card_filter_le (Sym2 V) (leaveG P) (fun e => v ∈ e)
      (fun e => @Sym2.Mem.decidable V (Classical.decEq V) v e)
  have hb : 3*#Q ≤ tradeDegreeBudget J m := by
    dsimp only [tradeDegreeBudget]
    simpa only [mul_assoc] using Nat.mul_le_mul_left 3 hQ
  exact hd.trans (hcard.trans hb)

theorem reserve_trade_packing {A : Type} [Fintype A] [DecidableEq A] {n g t : ℕ}
    {lab : Fin n → Fin k} {κ : A → Fin k} (h : Wilson.Setup lab κ g t)
    {S : Finset (Finset (Fin g))} (hS : _root_.STS.IsSTS S) (Λ : Wilson.LFam A S t)
    [Fact m.Prime] (hm : 8 < m) {J : Type} [Fintype J] [DecidableEq J]
    (P : Place lab J m) (hR : ∀ p, P.ψ p ∈ Wilson.reserve h)
    (σ : J × ZMod m × ZMod m → Bool) :
    IsPacking (rHostK lab ((Wilson.crossP h Λ).biUnion triEdges)) (bicF k) (packG P σ) := by
  refine ⟨fun T hT => ?_,packG_disj P hm σ⟩
  have ha := packG_allowed P σ T hT
  have hsub := packG_inside_reserve P (Wilson.reserve h) hR σ T hT
  exact ⟨ha.1,fun u hu v _ huv => Wilson.reserve_adj h hS Λ (hsub hu) huv,ha.2.2⟩

end CDRBicolour.KBicolor.PrescribedCounting
