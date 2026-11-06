/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module
public import RequestProject.TypedTriangle.PreparedDeletion
public import RequestProject.TypedTriangle.LinkDiameter
set_option maxHeartbeats 4000000 -- build option (original: -DmaxHeartbeats=1600000; raised)
set_option maxRecDepth 16384 -- build option (original: -DmaxRecDepth=8192; raised)
@[expose] public section

/-! Native robust component interfaces, with sparse used-edge deletion.
These are the actual hypotheses needed by V20, stated without its remote imports.
Pending local rc3 verification. No extra density inside links is assumed. -/

open Finset Classical
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace TypedTriangle.ActiveCover
open ComponentRows Incidence
variable {V I : Type*} [Fintype V] {G : SimpleGraph V} {lab : V → I}
  {F : Set (Multiset I)}

lemma delG_walk_avoids (J : SimpleGraph V) (Y : Finset V) (B : Finset (Sym2 V))
    {x y : V} (p : (delG J Y B).Walk x y) :
    x ∉ Y → ∀ z ∈ p.support, z ∉ Y := by
  induction p with
  | nil => intro hx; simpa using hx
  | @cons u w y huw p ih =>
    intro _ z hz
    rcases List.mem_cons.mp hz with rfl | hz
    · exact huw.2.1
    · exact ih huw.2.2.1 z hz

lemma walk_support_in_active_component {a x y : V} {K : Finset V}
    (hK : IsActiveRow G lab F (a, K)) (hx : x ∈ K)
    (p : (link G lab F a).Walk x y) : ∀ z ∈ p.support, z ∈ K := by
  induction p with
  | nil => simpa using hx
  | @cons u w y huw p ih =>
    have hw : w ∈ K := (active_component_closed hK u w huw).mp hx
    intro z hz
    rcases List.mem_cons.mp hz with rfl | hz
    · exact hx
    · exact ih hw z hz

/-- Robust diameter in the actual typed link minus a sparse used-edge set.
All walks stay in the original component and avoid the vertex deletion. -/
theorem native_component_robust_diameter {α : ℝ} {h : ℕ} (hα : 0 < α)
    (hH3 : CommonNbrCond (⟨G, lab⟩ : Host V I) F α)
    (hH4 : HingeCond (⟨G, lab⟩ : Host V I) F α h)
    (a : V) (K : Finset V) (hK : IsActiveRow G lab F (a, K))
    (B : Finset (Sym2 V)) (d M : ℕ) (hdeg : ∀ x, degIn B x ≤ d)
    (hw1 : (M : ℝ) + 2 + 4 * d < α * Fintype.card V)
    (hw2 : ((M : ℝ) + h + 5 * d) * 2 ^ Nat.choose h 2 ≤ α / 2 * Fintype.card V)
    (hw3 : (M : ℝ) + d ≤ α * Fintype.card V / 2) :
    ∀ Y : Finset V, Y.card ≤ M → ∀ x ∈ K, ∀ y ∈ K, x ∉ Y → y ∉ Y →
      ∃ p : (delG (linkGraph (⟨G, lab⟩ : Host V I) F a) ∅ B).Walk x y,
        p.length ≤ 3 * ⌊2 / α⌋₊ ∧ ∀ z ∈ p.support, z ∈ K ∧ z ∉ Y := by
  intro Y hY x hx y hy hxY hyY
  have hYR : (Y.card : ℝ) ≤ M := by exact_mod_cast hY
  have hr := link_reach_robust_any_root hα hH3 hH4 a Y B d hdeg
    (by linarith) ((mul_le_mul_of_nonneg_right (by linarith :
      (Y.card : ℝ) + h + 5 * d ≤ M + h + 5 * d) (by positivity)).trans hw2)
    hxY hyY (active_component_reachable hK hx hy)
  have hd := linkOn_good_diamLe hα hH3 a Y B hdeg (by linarith)
  rw [linkOn_goodEdges_eq] at hd
  obtain ⟨p, hp⟩ := hd x y hr
  have hle : delG (linkGraph (⟨G, lab⟩ : Host V I) F a) Y B ≤
      delG (linkGraph (⟨G, lab⟩ : Host V I) F a) ∅ B := by
    intro u v huv
    exact ⟨huv.1, by simp, by simp, huv.2.2.2⟩
  have hle0 : delG (linkGraph (⟨G, lab⟩ : Host V I) F a) Y B ≤ link G lab F a :=
    delG_le _ _ _
  have hsK := walk_support_in_active_component hK hx (p.map (SimpleGraph.Hom.ofLE hle0))
  have hsY := delG_walk_avoids _ Y B p hxY
  refine ⟨p.map (SimpleGraph.Hom.ofLE hle), by simpa using hp, ?_⟩
  intro z hz
  have hz' : z ∈ p.support := by simpa using hz
  exact ⟨hsK z (by simpa using hz'), hsY z hz'⟩

/-- Non-bipartiteness survives every deletion in the same numerical window. -/
theorem native_component_robust_nonbip {α : ℝ} {h : ℕ} (hα : 0 < α)
    (hH3 : CommonNbrCond (⟨G, lab⟩ : Host V I) F α)
    (hH4 : HingeCond (⟨G, lab⟩ : Host V I) F α h)
    (a : V) (K : Finset V) (hK : IsActiveRow G lab F (a, K))
    (hNB : ¬ IsBip G lab F (a, K))
    (B : Finset (Sym2 V)) (d M : ℕ) (hdeg : ∀ x, degIn B x ≤ d)
    (hw1 : (M : ℝ) + 2 + 4 * d < α * Fintype.card V)
    (hw2 : ((M : ℝ) + h + 5 * d) * 2 ^ Nat.choose h 2 ≤ α / 2 * Fintype.card V) :
    ∀ Y : Finset V, Y.card ≤ M →
      ¬ ∃ col : V → Bool, ∀ x ∈ K, ∀ y ∈ K, x ∉ Y → y ∉ Y →
        (delG (linkGraph (⟨G, lab⟩ : Host V I) F a) ∅ B).Adj x y → col x ≠ col y := by
  intro Y hY
  have hYR : (Y.card : ℝ) ≤ M := by exact_mod_cast hY
  have hcard := active_component_card_ge hH3 hK
  have hlt : Y.card < K.card := by exact_mod_cast (show (Y.card : ℝ) < K.card by linarith)
  obtain ⟨u, hu, huY⟩ := Finset.exists_mem_notMem_of_card_lt_card hlt
  have hcomp : comp G lab F a u = K := by
    obtain ⟨u₀, _, hK0⟩ := hK
    exact (ActiveCover.comp_eq_of_mem (hK0 ▸ hu)).trans hK0
  have hNB' : ¬ IsBip G lab F (a, comp G lab F a u) := by simpa [hcomp] using hNB
  have hm := componentRows_starIm_le_incidence (G := G) (lab := lab) (F := F) a
    (two_dl_of_not_bip G lab F hNB')
  have hz : ∀ y ∈ Y, ((2 : ℤ) • Incidence.dlt u) y = 0 := by
    intro y hy
    have hyu : y ≠ u := fun he => huY (he ▸ hy)
    simp [Incidence.dlt, hyu]
  have hm' := (link_image_robust_any_root hα hH3 hH4 a Y B d hdeg
    (by linarith) ((mul_le_mul_of_nonneg_right (by linarith :
      (Y.card : ℝ) + h + 5 * d ≤ M + h + 5 * d) (by positivity)).trans hw2) hz).mp hm
  have hno := Incidence.double_delta_forbids_coloring
    (delG (linkGraph (⟨G, lab⟩ : Host V I) F a) Y B) K u hu
    (fun x y hxy => active_component_closed hK x y hxy.1) hm'
  rintro ⟨col, hcol⟩
  apply hno
  refine ⟨col, ?_⟩
  intro x hx y hy hxy
  exact hcol x hx y hy hxy.2.1 hxy.2.2.1
    ⟨hxy.1, by simp, by simp, hxy.2.2.2⟩

end TypedTriangle.ActiveCover
