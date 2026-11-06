/-
Copyright (c) 2026 Juan Pablo Traverso Gianini.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module
public import RequestProject.TypedTriangle.IntegerChargeWord
public import RequestProject.TypedTriangle.PhysicalChargeCell
set_option maxHeartbeats 4000000 -- build option (original: -DmaxHeartbeats=1600000; raised)
set_option maxRecDepth 16384 -- build option (original: -DmaxRecDepth=8192; raised)
@[expose] public section
open Finset Classical
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace TypedTriangle.ChargePolar

/-- Positive realization with resource budget measured by the profile's own
l1 norm; no signed word or initial certificate is supplied. -/
theorem integer_polarization {V I : Type*} [Fintype V]
    {H : Host V I} {F : Set (Multiset I)} {α : ℝ}
    (h3 : CommonNbrCond H F α) (x : Sym2 V → ℤ) (U : Finset V) (k : ℕ)
    (hnorm : (∑ e, |x e|) ≤ (k:ℤ))
    (hTri : ∀ e, x e≠0 → HasTri H F e)
    (hRoots : ∀ e, x e≠0 → ∀ v ∈ e, v∈U)
    (B : Finset (Sym2 V)) {b : ℕ} (hB : ∀ v, SelSimul.edeg B v ≤ b)
    (hwin : ((U.card+3*k+2*b+2:ℕ):ℝ) < α*Fintype.card V) :
    ∃ (Aux : Finset V) (Y : Finset (Sym2 V)), Aux.card≤3*k ∧ Disjoint Aux U ∧
      Y.card≤4*k ∧ Disjoint Y B ∧ Fresh U Y ∧ Inside (U ∪ Aux) Y ∧
      Y⊆edges H ∧ ind Y-x ∈ lattice H F := by
  obtain ⟨l,hl,hlen,hmem⟩ := integer_word x
  have hk : l.length≤k := by exact_mod_cast (hlen.trans_le hnorm)
  have hw : ((U.card+3*l.length+2*b+2:ℕ):ℝ) < α*Fintype.card V := by
    have hc : U.card+3*l.length+2*b+2 ≤ U.card+3*k+2*b+2 := by omega
    exact (show ((U.card+3*l.length+2*b+2:ℕ):ℝ) ≤ (U.card+3*k+2*b+2:ℕ) by exact_mod_cast hc).trans_lt hwin
  obtain ⟨Aux,Y,hAux,hAuxU,hY,hYB,hFresh,hInside,hEdges,hRel⟩ :=
    word_polarization h3 l U B hB (fun z hz => hTri z.2 (hmem z hz))
      (fun z hz => hRoots z.2 (hmem z hz)) hw
  refine ⟨Aux,Y,hAux.trans (Nat.mul_le_mul_left 3 hk),hAuxU,
    hY.trans (Nat.mul_le_mul_left 4 hk),hYB,hFresh,hInside,hEdges,?_⟩
  simpa only [hl] using hRel

/-- Native physical two-mode cell for an arbitrary bounded integer profile.
Both decomposition modes are constructed from H3/H4 and the profile's physical
membership in the ambient host. -/
theorem integer_charge_cell (α : ℝ) (h : ℕ) (hα : 0<α) :
    ∃ K n₀ : ℕ, ∀ {V I : Type} [Fintype V] (H : Host V I)
      (J : SimpleGraph V) (F : Set (Multiset I)) (β : ℝ),
      n₀≤Fintype.card V → CommonNbrCond H F α → HingeCond H F α h →
      J≤H.G → CommonNbrCond (⟨J,H.lab⟩ : Host V I) F β →
      ∀ (x : Sym2 V → ℤ) (U : Finset V) (k : ℕ),
      (∑ e, |x e|)≤(k:ℤ) →
      (∀ e, x e≠0 → HasTri (⟨J,H.lab⟩ : Host V I) F e) →
      (∀ e, x e≠0 → ∀ v ∈ e, v∈U) → x∈lattice H F →
      ∀ (B : Finset (Sym2 V)) (b Ub : ℕ), (∀ v, SelSimul.edeg B v≤b) →
      ((U.card+3*k+2*b+2:ℕ):ℝ)<β*Fintype.card V →
      U.card+3*k+3*(K*(4*k))+K*(4*k)*(2*h-2)+3*(K*(4*k))*(2*h-3)≤Ub →
      (Ub:ℝ)+3+4*b<α*Fintype.card V →
      ((Ub:ℝ)+1+h+5*b)*2^(Nat.choose h 2)≤α/2*Fintype.card V →
      ∃ A Y : Finset (Sym2 V), Y.card≤4*k ∧ Y⊆edges (⟨J,H.lab⟩ : Host V I) ∧
        Disjoint Y B ∧ Disjoint A B ∧ Disjoint A Y ∧ Basal H F (A∪Y) ∧ Basal H F A ∧
        (A∪Y).card≤K*(4*k)*(4*(2*h-2).choose 2+6)+4*k ∧
        ind Y-x ∈ lattice (⟨J,H.lab⟩ : Host V I) F := by
  obtain ⟨K,n₀,hCell⟩ := physical_charge_cell α h hα
  refine ⟨K,n₀,?_⟩
  intro V I _ H J F β hn h3 h4 hJG hJ3 x U k hnorm hTri hRoots hx B b Ub hB hw hUb hw1 hw2
  obtain ⟨l,hl,hlen,hmem⟩ := integer_word x
  have hk : l.length≤k := by exact_mod_cast (hlen.trans_le hnorm)
  have hwin : ((U.card+3*l.length+2*b+2:ℕ):ℝ)<β*Fintype.card V := by
    have hc : U.card+3*l.length+2*b+2 ≤ U.card+3*k+2*b+2 := by omega
    exact (show ((U.card+3*l.length+2*b+2:ℕ):ℝ) ≤ (U.card+3*k+2*b+2:ℕ) by exact_mod_cast hc).trans_lt hw
  have hbudget : U.card+3*l.length+3*(K*(4*l.length))+K*(4*l.length)*(2*h-2)+
      3*(K*(4*l.length))*(2*h-3)≤Ub := by
    apply le_trans _ hUb
    gcongr
  obtain ⟨A,Y,hY,hE,hYB,hAB,hAY,hBase,hOff,hSize,hRel⟩ :=
    hCell H J F β hn h3 h4 hJG hJ3 l U (fun z hz => hTri z.2 (hmem z hz))
      (fun z hz => hRoots z.2 (hmem z hz)) (by simpa only [hl] using hx)
      B b Ub hB hwin hbudget hw1 hw2
  refine ⟨A,Y,hY.trans (Nat.mul_le_mul_left 4 hk),hE,hYB,hAB,hAY,hBase,hOff,?_,?_⟩
  · apply hSize.trans
    gcongr
  · simpa only [hl] using hRel

end TypedTriangle.ChargePolar
