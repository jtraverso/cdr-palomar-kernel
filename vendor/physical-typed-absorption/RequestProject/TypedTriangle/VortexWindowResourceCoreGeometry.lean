/-
Copyright (c) 2026 Juan Pablo Traverso Gianini.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module
public import RequestProject.TypedTriangle.VortexCleanVertexDeletion
public import RequestProject.TypedTriangle.VortexCleanHingeEquiv
public import RequestProject.TypedTriangle.VortexCleanHingeGeometry
public import RequestProject.TypedTriangle.VortexNestedH3Transfer
public import RequestProject.TypedTriangle.VortexReferenceTrim
set_option maxHeartbeats 4000000 -- build option (original: -DmaxHeartbeats=1600000; raised)
set_option maxRecDepth 16384 -- build option (original: -DmaxRecDepth=8192; raised)
@[expose] public section
open Finset Classical
noncomputable section
set_option autoImplicit false
namespace TypedTriangle.Vortex

private theorem lower_resource_geometry {Y I : Type} [Fintype Y]
    (J : Host Y I) (F : Set (Multiset I)) (α : ℝ) (h : ℕ) (hα : 0 < α)
    (h3 : CommonNbrCond J F (α/4-α/8))
    (hClean : CleanHingeCond J F (α/4-α/8) h) :
    CommonNbrCond J F (α/32) ∧ HingeCond J F (α/32) h := by
  constructor
  · intro u v huv k hk
    exact (mul_le_mul_of_nonneg_right (by linarith : α/32 ≤ α/4-α/8)
      (by positivity)).trans (h3 u v huv k hk)
  · exact (hClean.mono (by linarith : α/32 ≤ α/4-α/8)).hingeCond

private theorem geometry_change_fintype {Y I : Type} (f₁ f₂ : Fintype Y)
    (J : Host Y I) (F : Set (Multiset I)) (α : ℝ) (h : ℕ)
    (hGeometry : @CommonNbrCond Y I f₁ J F α ∧ @HingeCond Y I f₁ J F α h) :
    @CommonNbrCond Y I f₂ J F α ∧ @HingeCond Y I f₂ J F α h := by
  cases Subsingleton.elim f₁ f₂
  exact hGeometry

/-- Geometry of the actual resource core after protecting the future
vertices. The prepared window is the same induced host as the bank uses. -/
theorem window_resource_core_geometry {X I : Type} [Fintype X]
    (H : Host X I) (F : Set (Multiset I)) (α₀ : ℝ) (h : ℕ)
    (W : Finset X) (A : Finset (Survivors (univ \ W))) (hα : 0 < α₀)
    (h3 : CommonNbrCond (⟨H.G.comap Subtype.val,H.lab ∘ Subtype.val⟩ :
      Host {x // x ∈ W} I) F (α₀/4))
    (hClean : CleanHingeCond (⟨H.G.comap Subtype.val,H.lab ∘ Subtype.val⟩ :
      Host {x // x ∈ W} I) F (α₀/4) h)
    (hCut : (A.card:ℝ) ≤ (α₀/8)*W.card)
    (hHingeCut : (A.card:ℝ)*(2:ℝ)^h.choose 2 ≤ (α₀/8)*W.card) :
    CommonNbrCond (restrictedHost (restrictedHost H (univ \ W)) A) F (α₀/32) ∧
      HingeCond (restrictedHost (restrictedHost H (univ \ W)) A) F (α₀/32) h := by
  let JW : Host {x // x ∈ W} I := ⟨H.G.comap Subtype.val,H.lab ∘ Subtype.val⟩
  let J0 := restrictedHost H (univ \ W)
  let e := (ReferenceTrim.scheduledToWindow W).symm
  have hAdj : ∀u v, JW.G.Adj u v ↔ J0.G.Adj (e u) (e v) := fun _ _ => Iff.rfl
  have hLab : ∀u, JW.lab u = J0.lab (e u) := fun _ => rfl
  have hCard : Fintype.card (Survivors (univ \ W)) = W.card := by
    simpa only [Fintype.card_coe] using (Fintype.card_congr e).symm
  have h3Scheduled := commonNbrCond_equiv e JW J0 F (α₀/4) hAdj hLab h3
  have hCleanScheduled := cleanHingeCond_equiv e JW J0 F (α₀/4) h hAdj hLab hClean
  have h3Core := commonNbr_after_vertex_deletion_additive J0 F (α₀/4) (α₀/8) A
    h3Scheduled (by linarith) (by simpa only [hCard] using hCut)
  have hCleanCore := clean_hinge_after_vertex_deletion J0 F (α₀/4) (α₀/8) h A
    hCleanScheduled (by linarith) (by simpa only [hCard] using hHingeCut)
  let fSource : Fintype (Survivors A) := by
    letI : DecidableEq (Survivors (univ \ W)) := Classical.decEq _
    exact inferInstance
  have hDone := @lower_resource_geometry _ _ fSource (restrictedHost J0 A) F α₀ h
    hα h3Core hCleanCore
  exact geometry_change_fintype _ _ (restrictedHost J0 A) F (α₀/32) h hDone

#print axioms window_resource_core_geometry
end TypedTriangle.Vortex
