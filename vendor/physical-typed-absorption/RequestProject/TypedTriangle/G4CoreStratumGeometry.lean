/-
Copyright (c) 2026 Juan Pablo Traverso Gianini.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module
public import RequestProject.S07V42.Atoms
public import RequestProject.TypedTriangle.RestrictedHingeGeometry
set_option maxHeartbeats 4000000 -- build option (original: -DmaxHeartbeats=1600000; raised)
set_option maxRecDepth 16384 -- build option (original: -DmaxRecDepth=8192; raised)
@[expose] public section

/-! Geometry on the actual complement of a sampled core and a small stratum. -/

open Finset Classical
noncomputable section

namespace TypedTriangle

theorem core_geometry_on_joint_restriction {V I : Type*} [Fintype V]
    (H : Host V I) (F : Set (Multiset I))
    (W outer bad : Finset V) (hW : W = univ \ outer)
    {β : ℝ} {h : ℕ} (hβ : 0 < β)
    (hCore3 : SparseEdge.CommonNbrCond
      (H.G.comap (Subtype.val : {x // x ∈ W} → V))
      (H.lab ∘ Subtype.val) F β)
    (hCore4 : SparseEdge.HingeCond
      (H.G.comap (Subtype.val : {x // x ∈ W} → V))
      (H.lab ∘ Subtype.val) F β h)
    (hbad : (bad.card : ℝ) ≤ S07V42.coreDelta β h * W.card) :
    CommonNbrCond (restrictedHost H (outer ∪ bad)) F (β / 2) ∧
      HingeCond (restrictedHost H (outer ∪ bad)) F (β / 2) h := by
  let Zx : Finset {x : V // x ∈ W} := univ.filter (fun x => x.1 ∈ bad)
  let incl : {x : V // x ∉ outer ∪ bad} → {x : V // x ∈ W} :=
    fun y => ⟨y.1, by
      rw [hW]
      simp only [mem_sdiff, mem_univ, true_and]
      exact fun ho => y.2 (mem_union_left bad ho)⟩
  have hinj : Function.Injective incl := by
    intro x y he
    apply Subtype.ext
    exact congrArg (fun z : {x : V // x ∈ W} => z.1) he
  have hrange : ∀ x : {x : V // x ∈ W},
      (∃ y, incl y = x) ↔ x ∉ Zx := by
    intro x
    simp only [Zx, mem_filter, mem_univ, true_and]
    constructor
    · rintro ⟨y, he⟩
      have hv : y.1 = x.1 := congrArg
        (fun z : {x : V // x ∈ W} => z.1) he
      intro hb
      exact y.2 (mem_union_right outer (hv ▸ hb))
    · intro hb
      have ho : x.1 ∉ outer := by
        have hx : x.1 ∈ (univ : Finset V) \ outer :=
          (congrArg (fun S : Finset V => x.1 ∈ S) hW).mp x.2
        simpa only [mem_sdiff, mem_univ, true_and] using hx
      refine ⟨⟨x.1, by simpa only [mem_union, not_or] using And.intro ho hb⟩, ?_⟩
      apply Subtype.ext
      rfl
  have hZ : (Zx.card : ℝ) ≤
      S07V42.coreDelta β h * Fintype.card {x : V // x ∈ W} := by
    rw [Fintype.card_coe]
    exact (Nat.cast_le.mpr (S07V42.card_Zx_le W bad)).trans hbad
  have h3 := S07V42.commonNbr_deletion hinj hrange hβ hCore3 hZ
    (S07V42.coreDelta_le hβ h)
  have h4 := S07V42.hinge_deletion hinj hrange hβ hCore4 hZ
    (S07V42.coreDelta_nonneg hβ h) (S07V42.coreDelta_mul_le hβ h)
  exact ⟨h3, h4⟩

end TypedTriangle

#print axioms TypedTriangle.core_geometry_on_joint_restriction
