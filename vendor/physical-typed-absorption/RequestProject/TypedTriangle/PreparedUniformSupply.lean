/-
Copyright (c) 2026 Juan Pablo Traverso Gianini.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module
public import RequestProject.TypedTriangle.PreparedAbsorberSupply
public import RequestProject.S07V28.PlacementWindow
public import RequestProject.S07V30.DeletionWindow
set_option maxHeartbeats 4000000 -- build option (original: -DmaxHeartbeats=1600000; raised)
set_option maxRecDepth 16384 -- build option (original: -DmaxRecDepth=8192; raised)
@[expose] public section

/-! Uniform robust absorber supply is derived from the prepared core and
G2. Constants precede the host and the payload. -/
open Finset Classical
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace TypedTriangle.PreparedSupply
open CorePayment Dispersal

/-- Uniform construction of the supply used by simultaneous placement. The
prepared core itself is constructed from H3/H4 in PreparedCoreConstruction. -/
theorem prepared_uniform_supply (α : ℝ) (h k : ℕ) (hα : 0 < α) :
    ∃ N s : ℕ, ∀ β : ℝ, 0 < β → ∃ δ : ℝ, 0 < δ ∧ ∃ n₀ : ℕ,
      ∀ {V I : Type} [Fintype V] (H : Host V I) (F : Set (Multiset I)),
        n₀ ≤ Fintype.card V → PreparedCore H.G H.lab F α h N β →
        ∀ P : Finset (Sym2 V), P.card ≤ k → IsPhysical H F P →
        S07V28.RobustAbsorberSupply H.G H.lab F P s
          ⌊δ*Fintype.card V⌋₊ ⌊δ*Fintype.card V⌋₊ := by
  obtain ⟨K,N,hG2⟩ := prepared_absorber_window α h hα
  let s := K*k*(4*(2*h-2).choose 2+6)
  let U := 2*k + 3*(K*k) + K*k*(2*h-2) + 3*(K*k)*(2*h-3)
  refine ⟨N,s,?_⟩
  intro β hβ
  obtain ⟨δ,hδ,n₀,hwin⟩ := S07V30.exists_deletion_window hα hβ U h
  refine ⟨δ,hδ,n₀,?_⟩
  intro V I _ H F hn Pc P hk hP B hBd S hS
  let Z := S \ support P
  have hz : Z.card ≤ ⌊δ*Fintype.card V⌋₊ := (card_le_card sdiff_subset).trans hS
  have hw := hwin (Fintype.card V) (Fintype.card (Survivors Z)) Z.card
    ⌊δ*Fintype.card V⌋₊ hn (card_survivors_add_card Z) hz le_rfl
  have hav : ∀ e ∈ P, ∀ v ∈ e, v ∉ Z := by
    intro e he v hv hvZ
    exact (mem_sdiff.mp hvZ).2 (mem_filter.mpr ⟨mem_univ _,e,he,hv⟩)
  have hsup : (support P).card ≤ 2*k :=
    (S07V28.card_support_le P).trans (Nat.mul_le_mul_left 2 hk)
  have hU : (support P).card + 3*(K*P.card) + K*P.card*(2*h-2) +
      3*(K*P.card)*(2*h-3) ≤ U := by
    dsimp [U]
    gcongr
  obtain ⟨A,hA,hAB,hcard,havoid⟩ := hG2 H F β Pc P hP Z hw.1 hav B
    ⌊δ*Fintype.card V⌋₊ U hBd hU hw.2.2.1 hw.2.2.2
  refine ⟨A,hA,hAB,hcard.trans (Nat.mul_le_mul_right _ (Nat.mul_le_mul_left K hk)),?_⟩
  intro v hv hvS
  by_contra hvP
  obtain ⟨_,e,he,hve⟩ := mem_filter.mp hv
  exact havoid e he v hve (mem_sdiff.mpr ⟨hvS,hvP⟩)

end TypedTriangle.PreparedSupply
