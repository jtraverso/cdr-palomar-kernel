/-
Copyright (c) 2026 Juan Pablo Traverso Gianini.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module
public import RequestProject.TypedTriangle.ChargeWordPolarization
public import RequestProject.TypedTriangle.SampleConstruct
set_option maxHeartbeats 4000000 -- build option (original: -DmaxHeartbeats=1600000; raised)
set_option maxRecDepth 16384 -- build option (original: -DmaxRecDepth=8192; raised)
@[expose] public section
open Finset Classical
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace TypedTriangle.ChargePolar

/-- Actual two-mode charge cell: the positive payload realizes the prescribed
intrinsic class; both the whole cell and its complement are basal in the ambient
host. The absorber is constructed by G2, not assumed as a provider. -/
theorem physical_charge_cell (α : ℝ) (h : ℕ) (hα : 0 < α) :
    ∃ K n₀ : ℕ, ∀ {V I : Type} [Fintype V] (H : Host V I)
      (J : SimpleGraph V) (F : Set (Multiset I)) (β : ℝ),
      n₀ ≤ Fintype.card V → CommonNbrCond H F α → HingeCond H F α h →
      J ≤ H.G → CommonNbrCond (⟨J,H.lab⟩ : Host V I) F β →
      ∀ (l : List (Bool × Sym2 V)) (U : Finset V),
      (∀ z ∈ l, HasTri (⟨J,H.lab⟩ : Host V I) F z.2) →
      (∀ z ∈ l, ∀ v ∈ z.2, v ∈ U) →
      signedWord l ∈ lattice H F →
      ∀ (B : Finset (Sym2 V)) (b Ub : ℕ), (∀ v, SelSimul.edeg B v ≤ b) →
      ((U.card+3*l.length+2*b+2:ℕ):ℝ) < β*Fintype.card V →
      U.card+3*l.length+3*(K*(4*l.length))+K*(4*l.length)*(2*h-2)+
        3*(K*(4*l.length))*(2*h-3) ≤ Ub →
      (Ub:ℝ)+3+4*b < α*Fintype.card V →
      ((Ub:ℝ)+1+h+5*b)*2^(Nat.choose h 2) ≤ α/2*Fintype.card V →
      ∃ A Y : Finset (Sym2 V),
        Y.card ≤ 4*l.length ∧ Y ⊆ edges (⟨J,H.lab⟩ : Host V I) ∧
        Disjoint Y B ∧ Disjoint A B ∧ Disjoint A Y ∧
        Basal H F (A ∪ Y) ∧ Basal H F A ∧
        (A ∪ Y).card ≤ K*(4*l.length)*(4*(2*h-2).choose 2+6)+4*l.length ∧
        ind Y-signedWord l ∈ lattice (⟨J,H.lab⟩ : Host V I) F := by
  obtain ⟨K,n₀,hG2⟩ := slot_absorber_of_H3H4 α h hα
  refine ⟨K,n₀,?_⟩
  intro V I _ H J F β hn h3 h4 hJG hJ3 l U hTri hRoots hWord B b Ub hB hw hUb hw1 hw2
  obtain ⟨Aux,Y,hAux,hAuxU,hY,hYB,hFresh,hInside,hEdges,hRel⟩ :=
    word_polarization hJ3 l U B hB hTri hRoots hw
  have hRelG : ind Y-signedWord l ∈ lattice H F :=
    lattice_mono (H := (⟨J,H.lab⟩ : Host V I)) (H' := H) hJG rfl hRel
  have hPhys : IsPhysical H F Y := by
    have hh := Submodule.add_mem (lattice H F) hRelG hWord
    change ind Y ∈ lattice H F
    simpa only [sub_add_cancel] using hh
  have hUb' : (U ∪ Aux).card+3*(K*Y.card)+K*Y.card*(2*h-2)+
      3*(K*Y.card)*(2*h-3) ≤ Ub := by
    apply le_trans _ hUb
    have hc : (U ∪ Aux).card ≤ U.card+3*l.length :=
      (card_union_le U Aux).trans (Nat.add_le_add_left hAux _)
    gcongr
  obtain ⟨A,hAbs,hAB,hAc⟩ := hG2 H F hn h3 h4 B b hB Y hPhys (U ∪ Aux) hInside Ub hUb' hw1 hw2
  refine ⟨A,Y,hY,hEdges,hYB,hAB,hAbs.1,hAbs.2.2,hAbs.2.1,?_,hRel⟩
  calc (A ∪ Y).card ≤ A.card+Y.card := card_union_le _ _
    _ ≤ K*(4*l.length)*(4*(2*h-2).choose 2+6)+4*l.length := by
      apply Nat.add_le_add _ hY
      exact hAc.trans (Nat.mul_le_mul_right _ (Nat.mul_le_mul_left K hY))

end TypedTriangle.ChargePolar
