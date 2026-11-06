/-
Copyright (c) 2026 Juan Pablo Traverso Gianini.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module
public import RequestProject.TypedTriangle.VortexIntrinsicFirstEntry
public import RequestProject.TypedTriangle.PreparedCoreConstruction
set_option maxHeartbeats 4000000 -- build option (original: -DmaxHeartbeats=1600000; raised)
set_option maxRecDepth 16384 -- build option (original: -DmaxRecDepth=8192; raised)
@[expose] public section

/-! Convert the intrinsic quotient stability to PreparedCore on the actual
surviving host, without a second preparation or a further vertex deletion. -/

open Finset Classical
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace TypedTriangle.Vortex

private theorem quotMap_injective_congr_source {V I : Type*} [Fintype V]
    {H K L : Host V I} {F : Set (Multiset I)}
    (heq : H = K) (hG : H.G ≤ L.G) (hl : H.lab = L.lab)
    (hG' : K.G ≤ L.G) (hl' : K.lab = L.lab) :
    Function.Injective (quotMap (F := F) hG hl) ↔
      Function.Injective (quotMap (F := F) hG' hl') := by
  subst K
  rfl

theorem intrinsic_stability_on_actual_host {V I : Type*} [Fintype V]
    (H : Host V I) (F : Set (Multiset I)) (A : Finset V) (β : ℝ)
    (hStable : ∀ B : Finset V, (B.card : ℝ) ≤ β * Fintype.card (Survivors A) →
      Function.Injective (nestedVertexQuotMap H F A B)) :
    ∀ Z : Finset (Survivors A), (Z.card : ℝ) ≤ β * Fintype.card (Survivors A) →
      Function.Injective
        (quotMap (F := F) (vertexDeleted_le (restrictedHost H A) Z) rfl) := by
  intro Z hZ
  let B := liftVertexSet A Z
  have hB : (B.card : ℝ) ≤ β * Fintype.card (Survivors A) := by
    simpa only [B, card_liftVertexSet] using hZ
  have hInj := hStable B hB
  have hInjD : Function.Injective
      (quotMap (F := F) (vertexDeleted_mono (vertexDeleted_le H B) A) rfl) :=
    (quotMap_injective_congr_source (vertexDeleted_vertexDeleted H A B) _ _ _ _).2 hInj
  have hInjR : Function.Injective
      (quotMap (F := F) (restrictedHost_mono (vertexDeleted_le H B) A)
        (restrictedHost_labels rfl A)) := by
    intro x y hxy
    apply (survivingPhysQuotEquiv (vertexDeleted H B) F A).injective
    apply hInjD
    have hx := quotMap_surviving_naturality F (vertexDeleted_le H B) rfl A x
    have hy := quotMap_surviving_naturality F (vertexDeleted_le H B) rfl A y
    exact hx.trans ((congrArg (survivingPhysQuotEquiv H F A) hxy).trans hy.symm)
  have heq : restrictedHost (vertexDeleted H B) A = vertexDeleted (restrictedHost H A) Z := by
    rw [restrictedHost_vertexDeleted]
    dsimp only [B]
    rw [subtype_liftVertexSet]
  exact (quotMap_injective_congr_source heq _ _ _ _).1 hInjR

/-- A fixed tolerance and threshold turn direct quotient stability into all
four PreparedCore fields. The host is unchanged. -/
theorem preparedCore_on_stable_host (α : ℝ) (h : ℕ) (hα : 0 < α) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ N : ℕ, ∃ n₀ : ℕ,
      ∀ β : ℝ, β ≤ ε →
      ∀ {V I : Type} [Fintype V] (H : Host V I) (F : Set (Multiset I)),
        n₀ ≤ Fintype.card V → CommonNbrCond H F α → HingeCond H F α h →
        (∀ Z : Finset V, (Z.card : ℝ) ≤ β * Fintype.card V →
          Function.Injective (quotMap (F := F) (vertexDeleted_le H Z) rfl)) →
        Dispersal.PreparedCore H.G H.lab F (α / 2) h N β := by
  obtain ⟨δ, hδ, hδhalf, hGeom⟩ := original_geometry_vertex_budget hα h
  obtain ⟨εWin, hεWin, nWin, hWin⟩ := uniform_nested_vertex_windows α h hα
  let ε := min (min δ εWin) (1 / 2)
  have hε : 0 < ε := lt_min (lt_min hδ hεWin) (by norm_num)
  refine ⟨ε, hε, ?_⟩
  intro N
  refine ⟨max nWin (2 * N), ?_⟩
  intro β hβ V I _ H F hn h3 h4 hStable
  have hβδ : β ≤ δ := hβ.trans ((min_le_left _ _).trans (min_le_left _ _))
  have hβWin : β ≤ εWin := hβ.trans ((min_le_left _ _).trans (min_le_right _ _))
  have hβhalf : β ≤ 1 / 2 := hβ.trans (min_le_right _ _)
  have hSmall (Z : Finset V) (hZ : (Z.card : ℝ) ≤ β * Fintype.card V) :
      (Z.card : ℝ) ≤ δ * Fintype.card V :=
    hZ.trans (mul_le_mul_of_nonneg_right hβδ (by positivity))
  have hGeo (Z : Finset V) (hZ : (Z.card : ℝ) ≤ β * Fintype.card V) :=
    original_geometry_restrictedHost hα.le h3 h4 Z
      (hGeom (by positivity) (hSmall Z hZ)).1 (hGeom (by positivity) (hSmall Z hZ)).2
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro Z hZ
    exact (prepared_commonNbrCond_iff _ _ _).mp (hGeo Z hZ).1
  · intro Z hZ
    exact (prepared_hingeCond_iff _ _ _ _).mp (hGeo Z hZ).2
  · intro Z hZ
    have hHalf : (Z.card : ℝ) ≤ (Fintype.card V : ℝ) / 2 := by
      have hs := mul_le_mul_of_nonneg_right hβhalf (by positivity : (0 : ℝ) ≤ Fintype.card V)
      linarith
    have hc := card_survivors_add_card Z
    have hN : 2 * N ≤ Fintype.card V := (le_max_right _ _).trans hn
    have hHalfN : 2 * Z.card ≤ Fintype.card V := by exact_mod_cast (by linarith : (2 : ℝ) * Z.card ≤ Fintype.card V)
    have hOrder : N ≤ Fintype.card (Survivors Z) := by omega
    exact hOrder
  · intro Z hZ y hy hzero
    have hZWin : (Z.card : ℝ) ≤ εWin * Fintype.card V :=
      hZ.trans (mul_le_mul_of_nonneg_right hβWin (by positivity))
    obtain ⟨_, _, hw1, hw2⟩ := hWin (∅ : Finset V) Z
      ((le_max_left _ _).trans hn) (by simp only [card_empty, Nat.cast_zero]; positivity) hZWin
    have hSurvEmpty : Fintype.card (Survivors (∅ : Finset V)) = Fintype.card V := by
      simpa only [card_empty, Nat.add_zero] using card_survivors_add_card (∅ : Finset V)
    rw [hSurvEmpty] at hw1 hw2
    have hw1' : (Z.card : ℝ) + 2 < α * Fintype.card V := by
      have hNonneg : (0 : ℝ) ≤ α * Fintype.card V := mul_nonneg hα.le (by positivity)
      linarith
    have hw2' : ((Z.card : ℝ) + h) * 2 ^ Nat.choose h 2 ≤ α / 2 * Fintype.card V := by
      have hNonneg : (0 : ℝ) ≤ α * Fintype.card V := mul_nonneg hα.le (by positivity)
      nlinarith
    have hp := (quotMap_vertexDeleted_injective_iff hα h3 h4 Z hw1' hw2').mp (hStable Z hZ)
    exact edgeRestrict_mem_lattice H F Z (hp y hy hzero)

#print axioms intrinsic_stability_on_actual_host
#print axioms preparedCore_on_stable_host
end TypedTriangle.Vortex
