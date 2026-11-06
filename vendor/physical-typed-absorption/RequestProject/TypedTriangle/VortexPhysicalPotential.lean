/-
Copyright (c) 2026 Juan Pablo Traverso Gianini.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module
public import RequestProject.TypedTriangle.VortexCleanSampleQuotient
set_option maxHeartbeats 4000000 -- build option (original: -DmaxHeartbeats=1600000; raised)
set_option maxRecDepth 16384 -- build option (original: -DmaxRecDepth=8192; raised)
@[expose] public section

/-! An intrinsic global preparation index. The index depends only on the
current physical quotient, increases on every failed persistence test, and
never resets when a sampled level is entered. -/

open Finset Classical
noncomputable section
namespace TypedTriangle.Vortex
universe u

def modulePotential (Q : Type*) [AddCommGroup Q] (T : ℕ) : ℕ :=
  Robust.potential T (Module.finrank ℤ Q) (Nat.card (Submodule.torsion ℤ Q))

private theorem modulePotential_equiv {A B : Type u} [AddCommGroup A] [AddCommGroup B]
    (e : A ≃ₗ[ℤ] B) (T : ℕ) : modulePotential A T = modulePotential B T := by
  have hker : LinearMap.ker e.toLinearMap = ⊥ := LinearMap.ker_eq_bot.mpr e.injective
  have hTor : Nat.card (Submodule.torsion ℤ A) = Nat.card (Submodule.torsion ℤ B) := by
    rw [Robust.torsion_card_of_surjective e.toLinearMap e.surjective
      (by rw [hker]; exact bot_le), hker]
    simp
  unfold modulePotential
  rw [e.finrank_eq, hTor]

private theorem modulePotential_strict {A B : Type u} [AddCommGroup A] [AddCommGroup B]
    [Module.Finite ℤ B] [Finite (Submodule.torsion ℤ B)]
    (f : B →ₗ[ℤ] A) (T : ℕ) (hf : Function.Surjective f)
    (hTor : Nat.card (Submodule.torsion ℤ A) ≤ T)
    [Finite (Submodule.torsion ℤ A)] (hStrict : ¬ Function.Injective f) :
    modulePotential A T < modulePotential B T :=
  Robust.potential_strict hTor Nat.card_pos (Robust.strict_step f hf hStrict)

private theorem modulePotential_mono {A B : Type u} [AddCommGroup A] [AddCommGroup B]
    [Module.Finite ℤ B] [Finite (Submodule.torsion ℤ B)]
    (f : B →ₗ[ℤ] A) (T : ℕ) (hf : Function.Surjective f)
    (hTor : Nat.card (Submodule.torsion ℤ A) ≤ T)
    [Finite (Submodule.torsion ℤ A)] :
    modulePotential A T ≤ modulePotential B T := by
  by_cases hi : Function.Injective f
  · exact (modulePotential_equiv (LinearEquiv.ofBijective f ⟨hi, hf⟩) T).ge
  · exact (modulePotential_strict f T hf hTor hi).le

def physicalPotential {V I : Type*} [Fintype V]
    (H : Host V I) (F : Set (Multiset I)) (T : ℕ) : ℕ :=
  modulePotential (physQuot H F) T

theorem physicalPotential_le {V I : Type*} [Fintype V]
    (H : Host V I) (F : Set (Multiset I)) (d T : ℕ)
    (hRank : Module.finrank ℤ (physQuot H F) ≤ d)
    (hTor : Nat.card (Submodule.torsion ℤ (physQuot H F)) ≤ T) :
    physicalPotential H F T ≤ d + (d + 1) * Nat.log 2 T :=
  Robust.potential_le hRank hTor

theorem physicalPotential_map_strict {V I : Type*} [Fintype V]
    {H K : Host V I} (F : Set (Multiset I)) (T : ℕ)
    (hG : K.G ≤ H.G) (hl : K.lab = H.lab)
    (hSurj : Function.Surjective (quotMap (F := F) hG hl))
    (hTor : Nat.card (Submodule.torsion ℤ (physQuot H F)) ≤ T)
    (hStrict : ¬ Function.Injective (quotMap (F := F) hG hl)) :
    physicalPotential H F T < physicalPotential K F T :=
  modulePotential_strict _ T hSurj hTor hStrict

theorem physicalPotential_vertexDeleted_eq {V I : Type*} [Fintype V]
    (H : Host V I) (F : Set (Multiset I)) (Z : Finset V) (T : ℕ) :
    physicalPotential (vertexDeleted H Z) F T =
      physicalPotential (restrictedHost H Z) F T :=
  (modulePotential_equiv (survivingPhysQuotEquiv H F Z) T).symm

theorem physicalPotential_sample_mono {V I : Type*} [Fintype V]
    (H : Host V I) (F : Set (Multiset I)) (W : Finset V)
    (α : ℝ) (h T : ℕ) (hα : 0 < α)
    (hGeom : ∀ U : Finset V, W ⊆ U →
      CommonNbrCond (restrictedHost H (univ \ U)) F α ∧
      HingeCond (restrictedHost H (univ \ U)) F α h)
    (hw1 : 3 < α * W.card)
    (hw2 : (1 + (h : ℝ)) * 2 ^ Nat.choose h 2 ≤ α / 2 * W.card)
    (hTor : Nat.card (Submodule.torsion ℤ (physQuot H F)) ≤ T) :
    physicalPotential H F T ≤ physicalPotential (restrictedHost H (univ \ W)) F T := by
  have hSurj := quotient_sample_surjective_of_intermediate_geometry H F W α h hα
    hGeom hw1 hw2
  have hm := modulePotential_mono (quotMap (F := F) (vertexDeleted_le H (univ \ W)) rfl)
    T hSurj hTor
  exact hm.trans_eq (physicalPotential_vertexDeleted_eq H F (univ \ W) T)

theorem physicalPotential_small_deletion_strict {V I : Type*} [Fintype V]
    (H : Host V I) (F : Set (Multiset I)) (Z : Finset V)
    (α : ℝ) (h T : ℕ) (hα : 0 < α)
    (h3 : CommonNbrCond H F α) (h4 : HingeCond H F α h)
    (hw1 : (Z.card : ℝ) + 2 < α * Fintype.card V)
    (hw2 : ((Z.card : ℝ) + h) * 2 ^ Nat.choose h 2 ≤ α / 2 * Fintype.card V)
    (hTor : Nat.card (Submodule.torsion ℤ (physQuot H F)) ≤ T)
    (hStrict : ¬ Function.Injective
      (quotMap (F := F) (vertexDeleted_le H Z) rfl)) :
    physicalPotential H F T < physicalPotential (restrictedHost H Z) F T := by
  have hSurj := quotMap_vertexDeleted_surjective hα h3 h4 Z hw1 hw2
  have hs := modulePotential_strict (quotMap (F := F) (vertexDeleted_le H Z) rfl)
    T hSurj hTor hStrict
  exact hs.trans_eq (physicalPotential_vertexDeleted_eq H F Z T)

#print axioms physicalPotential_le
#print axioms physicalPotential_vertexDeleted_eq
#print axioms physicalPotential_sample_mono
#print axioms physicalPotential_small_deletion_strict
end TypedTriangle.Vortex
