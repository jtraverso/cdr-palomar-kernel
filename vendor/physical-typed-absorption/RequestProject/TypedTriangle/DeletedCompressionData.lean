/-
Copyright (c) 2026 Juan Pablo Traverso Gianini.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module
public import RequestProject.TypedTriangle.NativeCoreKernel
set_option maxHeartbeats 4000000 -- build option (original: -DmaxHeartbeats=1600000; raised)
set_option maxRecDepth 16384 -- build option (original: -DmaxRecDepth=8192; raised)
@[expose] public section
open Finset Classical Submodule
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace TypedTriangle
open Incidence
variable {V I : Type*} [Fintype V]

/-- Full coordinate data transported from the TRUE surviving host: the physical
lattice image, not just the coordinate kernel and norm, is preserved. H3 is never
asserted on deleted isolated vertices. -/
theorem surviving_compression_coordinate_data (H : Host V I) (F : Set (Multiset I))
    (Z : Finset V) {s H₀ D₀ : ℕ}
    (cmp : Compression (restrictedHost H Z) F s H₀ D₀) :
    ∃ q : localGroup (vertexDeleted H Z) F →ₗ[ℤ] (Fin ((s+1)^2) → ℤ),
      (∀ x, q x = 0 → (x:Sym2 V → ℤ) ∈ lattice (vertexDeleted H Z) F) ∧
      (∀ x i, |q x i| ≤ D₀*Dispersal.l1E (x:Sym2 V → ℤ)) ∧
      ∃ S : Finset (Fin ((s+1)^2) → ℤ),
        (∀ z ∈ S, ∀ i, |z i| ≤ (3*D₀:ℕ)) ∧
        ((lattice (vertexDeleted H Z) F).comap (localGroup (vertexDeleted H Z) F).subtype).map q =
          span ℤ (S:Set _) := by
  obtain ⟨qc,hker,hq,S,hS,himg⟩ := compression_local_coordinate_data (restrictedHost H Z) F cmp
  let e := survivingLocalEquiv H F Z
  let q := qc.comp e.symm.toLinearMap
  refine ⟨q,?_,?_,S,hS,?_⟩
  · intro x hx
    have hc := hker (e.symm x) hx
    have he := edgeZeroExtend_mem_lattice H F Z hc
    have hback : edgeZeroExtend Z (e.symm x:Sym2 (Survivors Z) → ℤ) = x :=
      congrArg Subtype.val (e.apply_symm_apply x)
    rwa [hback] at he
  · intro x i
    exact (hq (e.symm x) i).trans (mul_le_mul_of_nonneg_left
      (Dispersal.l1E_restr_le (Z:=Z) (x:Sym2 V → ℤ)) (by positivity))
  · rw [←survivingLocalEquiv_map_lattice H F Z,←Submodule.map_comp]
    have hcomp : q.comp e.toLinearMap = qc := by
      apply LinearMap.ext
      intro x
      exact congrArg qc (e.symm_apply_apply x)
    rw [hcomp]
    exact himg

end TypedTriangle
