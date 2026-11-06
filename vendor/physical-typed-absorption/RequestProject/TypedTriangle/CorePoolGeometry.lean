/-
Copyright (c) 2026 Juan Pablo Traverso Gianini.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module
public import RequestProject.TypedTriangle.RestrictedHostGeometry
public import RequestProject.TypedTriangle.RestrictedVertexBounds
set_option maxHeartbeats 1600000 -- build option (original: -DmaxHeartbeats=1600000)
set_option maxRecDepth 8192 -- build option (original: -DmaxRecDepth=8192)
@[expose] public section

/-! H3 on the actual vertex type of a random core. No small-complement
assumption is used: its robust common-neighbour pool is the input. -/
open Finset Classical
noncomputable section
namespace TypedTriangle.CorePaid
variable {V I : Type*} [Fintype V]

lemma card_survivors_compl (W : Finset V) :
    Fintype.card (Survivors (univ \ W)) = W.card := by
  have h1 := card_survivors_add_card (univ \ W)
  have h2 := card_sdiff_add_card_eq_card (subset_univ W)
  rw [card_univ] at h2
  omega

theorem commonNbrCond_of_core_pool (H : Host V I) (F : Set (Multiset I))
    (W : Finset V) {κ : ℝ} (hκ : 0 ≤ κ)
    (hpool : ∀ u v : V, u ≠ v → ∀ k : I,
      ({H.lab u,H.lab v,k}:Multiset I) ∈ F →
        κ*Fintype.card V ≤ ((commonNbrs H k u v) ∩ W).card) :
    CommonNbrCond (restrictedHost H (univ \ W)) F κ := by
  intro u v hne k hlab
  have hcard : (Fintype.card (Survivors (univ \ W)):ℝ) ≤ Fintype.card V := by
    rw [card_survivors_compl]
    exact_mod_cast card_le_univ W
  have heq : ((commonNbrs H k u.1 v.1).filter (fun w => w ∉ univ \ W)) =
      commonNbrs H k u.1 v.1 ∩ W := by
    ext w
    simp
  have hh := hpool u.1 v.1 (fun he => hne (Subtype.ext he)) k hlab
  rw [card_commonNbrs_restrictedHost,heq]
  exact (mul_le_mul_of_nonneg_left hcard hκ).trans hh

end TypedTriangle.CorePaid
