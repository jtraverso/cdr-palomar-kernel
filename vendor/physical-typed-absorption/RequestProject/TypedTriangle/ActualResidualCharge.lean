/-
Copyright (c) 2026 Juan Pablo Traverso Gianini.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module
public import RequestProject.TypedTriangle.NativeCoreMonitorRepresentation
set_option maxHeartbeats 4000000 -- build option (original: -DmaxHeartbeats=1600000; raised)
set_option maxRecDepth 16384 -- build option (original: -DmaxRecDepth=8192; raised)
@[expose] public section
open Finset Classical
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace TypedTriangle.CatalogNative
open S07V42
variable {V I : Type*} [Fintype V]

/-- The actual physical core-supported leftover enters the allocator's initial
subgroup K_empty. Neither MCore membership nor charge membership is assumed.
The path contract is supplied by the SAME V45 sampled core. -/
theorem actual_physical_residue_charge (H : Host V I) (F : Set (Multiset I))
    {W : Finset V} {t : ℕ} (hCt : S07V45.CorePathContract H.G H.lab F W t)
    (ht : Odd t) (ht3 : 3 ≤ t) (J : Finset (Sym2 V))
    (hphys : IsPhysical H F J) (hsub : J ⊆ SparseEdge.edges (indG H.G W)) :
    ∃ x : MCore H.G H.lab F W, (x : Sym2 V → ℤ) = ind J ∧
      clsQ H.G H.lab F W (x : Sym2 V → ℤ) ∈ KZ H.G H.lab F W ∅ := by
  have hprof := physical_indicator_mem_core H F hCt ht ht3 J hphys hsub
  refine ⟨⟨ind J,hprof⟩,rfl,(mem_KZ H.G H.lab F W).mpr ⟨ind J,?_,?_,rfl⟩⟩
  · simpa only [MZ,MCore,sdiff_empty] using hprof
  · have hG : S07V39.delG H.G (∅ : Finset V) = H.G := by
      ext u v
      simp [S07V39.delG]
    rw [LamDel,hG]
    exact hphys

end TypedTriangle.CatalogNative
