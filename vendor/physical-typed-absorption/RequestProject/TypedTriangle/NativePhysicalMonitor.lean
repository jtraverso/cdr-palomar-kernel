/-
Copyright (c) 2026 Juan Pablo Traverso Gianini.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module
public import RequestProject.TypedTriangle.CoreFunctionalBridge
set_option maxHeartbeats 4000000 -- build option (original: -DmaxHeartbeats=1600000; raised)
set_option maxRecDepth 16384 -- build option (original: -DmaxRecDepth=8192; raised)
@[expose] public section
open Finset Classical Submodule
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace TypedTriangle.CoreMonitor

lemma real_l1E_eq {V : Type*} [Fintype V] (x : Sym2 V → ℤ) :
    (∑ e, |(x e:ℝ)|) = (Dispersal.l1E x:ℝ) := by
  simp [Dispersal.l1E]

/-- Native physical monitor localization. Only the bounded core functional and
its annihilation of currently available physical charges remain as algebraic
inputs; the compatible ambient functional and all physical weights are built.
The geometry is on actual surviving hosts, never on isolated deleted vertices. -/
theorem native_core_physical_gluing (α β : ℝ) (h : ℕ) (hα : 0 < α) (hβ : 0 < β) :
    ∃ B : ℝ, 1 ≤ B ∧ ∃ n₀ : ℕ,
      ∀ {V I : Type} [Fintype V] (H : Host V I) (F : Set (Multiset I)) (outer bad : Finset V),
        n₀ ≤ Fintype.card (Survivors bad) → n₀ ≤ Fintype.card (Survivors (outer∪bad)) →
        CommonNbrCond (restrictedHost H bad) F α → HingeCond (restrictedHost H bad) F α h →
        CommonNbrCond (restrictedHost H (outer∪bad)) F β → HingeCond (restrictedHost H (outer∪bad)) F β h →
        CommonNbrCond (restrictedHost H outer) F β → HingeCond (restrictedHost H outer) F β h →
        ((bad.subtype (· ∉ outer)).card:ℝ) ≤ S07V37.delOf β h*Fintype.card (Survivors outer) →
        ∀ (A : ℝ), 0 ≤ A →
        ∀ f : localGroup (restrictedHost H outer) F →ₗ[ℤ] ℝ,
          (∀ x : localGroup (restrictedHost H outer) F,
            |f x| ≤ A*Dispersal.l1E (x:Sym2 (Survivors outer) → ℤ)) →
          (∀ x : localGroup (vertexDeleted H (outer∪bad)) F,
            (x:Sym2 V → ℤ) ∈ lattice (vertexDeleted H bad) F →
              f (coreRestriction H F outer bad x) = 0) →
          ∃ lam : Sym2 V → ℝ, (∀ e, |lam e| ≤ S07V39.glueConst β (B*A)) ∧
            (∀ x : localGroup (restrictedHost H outer) F,
              ∑ e, lam e*(edgeZeroExtend outer x.1 e:ℝ) = f x) ∧
            (∀ T, IsAllowed (vertexDeleted H bad) F T → ∑ e ∈ triEdges T, lam e = 0) ∧
            ∀ T, IsAllowed H F T →
              |∑ e ∈ triEdges T, lam e| ≤ 3*S07V39.glueConst β (B*A)*(T∩bad).card := by
  obtain ⟨B0,hB0,nE,hExt⟩ := native_core_deleted_functional α β h hα hβ
  refine ⟨B0+1,by linarith,max nE (S07V25.n1Of β),?_⟩
  intro V I _ H F outer bad hnG hnJ hG3 hG4 hJ3 hJ4 hK3 hK4 hbad A hA f hf hkill
  obtain ⟨f0,hf0,hagree,hann⟩ := hExt H F outer bad ((le_max_left _ _).trans hnG)
    ((le_max_left _ _).trans hnJ) hG3 hG4 hJ3 hJ4 A hA f hf hkill
  have hcoreCard : Fintype.card (Survivors (outer∪bad)) ≤ Fintype.card (Survivors outer) := by
    have h₁ := card_survivors_add_card outer
    have h₂ := card_survivors_add_card (outer∪bad)
    have h₃ := card_le_card (subset_union_left : outer ⊆ outer∪bad)
    omega
  have hnK : S07V25.n1Of β ≤ Fintype.card (Survivors outer) :=
    ((le_max_right _ _).trans hnJ).trans hcoreCard
  have hA0 : A ≤ (B0+1)*A := by nlinarith
  have hB0A : B0*A ≤ (B0+1)*A := by nlinarith
  have hfR : ∀ x : localGroup (restrictedHost H outer) F,
      |f x| ≤ ((B0+1)*A)*(∑ e, |(((x:Sym2 (Survivors outer) → ℤ) e):ℝ)|) := by
    intro x
    rw [real_l1E_eq]
    exact (hf x).trans (mul_le_mul_of_nonneg_right hA0 (by rw [←real_l1E_eq]; positivity))
  have hf0R : ∀ x : Composition.localProfile (S07V39.delG H.G bad) H.lab F,
      |f0 x| ≤ ((B0+1)*A)*(∑ e, |(((x:Sym2 V → ℤ) e):ℝ)|) := by
    intro x
    rw [real_l1E_eq]
    exact (hf0 x).trans (mul_le_mul_of_nonneg_right hB0A (by rw [←real_l1E_eq]; positivity))
  exact core_physical_gluing H F outer bad hβ (by positivity) hK3 hK4 hnK hbad f f0 hfR hf0R hagree hann
end TypedTriangle.CoreMonitor
