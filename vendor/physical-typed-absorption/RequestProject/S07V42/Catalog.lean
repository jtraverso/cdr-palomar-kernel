/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module
public import RequestProject.S07V42.Generation
public import RequestProject.S07V42.Reroute
set_option maxHeartbeats 4000000 -- build option (original: -DmaxHeartbeats=1600000; raised)
set_option maxRecDepth 16384 -- build option (original: -DmaxRecDepth=8192; raised)
@[expose] public section

/-!
# V42 §6 — the FIXED finite physical catalog and its native rerouting

* `catR β d c d' c' E'` (fixed before the host) and the catalog index
  `Cat d R = {v // v ∈ box d R}` (`card_Cat : |Cat d R| = (2R+1)^d`, uniform).
* `gCat C0 R : Cat d R → Q` — the class of any core local profile with `q0`-coordinate `v`
  (zero for unattained coordinates). It depends only on the FIXED core compression, never on
  `Z`; `gCat_spec`: `gCat v = [x]` whenever `q0 x = v`.
* `catalog_generates` (step 3): for every admissible `Z`, the active catalog entries
  (`gCat c ∈ K_Z`) generate `K_Z`.
* `native_reroute` (step 4): `∃ U` fixed before the host such that, for every admissible `Z`
  and EVERY active entry `c`, there is an actual `x ∈ M(H[W \ Z]) ∩ Λ(H − Z)` with
  `l1E x ≤ U` and `[x] = gCat c` (the SAME fixed catalog class, rerouted through the CURRENT
  bounded generators; torsion included).
-/

open Finset Classical Submodule

noncomputable section

namespace S07V42

open TypedTriangle.SparseEdge TypedTriangle.ComponentRows TypedTriangle.Composition
open TypedTriangle.Dispersal S07V34

/-- the catalog coordinate radius, fixed before the host -/
def catR (β : ℝ) (d c E d' c' E' : ℕ) : ℕ := max E (c * genK β d c d' c' E')

/-- the catalog index: the integer coordinate box -/
abbrev Cat (d R : ℕ) := {v // v ∈ S07V34.box d R}

lemma card_box' (d R : ℕ) : (S07V34.box d R).card = (2 * R + 1) ^ d := by
  unfold S07V34.box
  rw [Fintype.card_piFinset]
  simp only [Int.card_Icc, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  congr 1
  omega

/-- **the catalog size is uniform** -/
lemma card_Cat (d R : ℕ) : Fintype.card (Cat d R) = (2 * R + 1) ^ d := by
  rw [Fintype.card_coe, card_box']

variable {V I : Type*} [Fintype V] {H : SimpleGraph V} {lab : V → I} {F : Set (Multiset I)}
  {W : Finset V}

/-- the fixed catalog charges -/
def gCat {d c E : ℕ} (C0 : CoreCompression H lab F W d c E) (R : ℕ) (v : Cat d R) :
    ClassQ H lab F W :=
  if h : ∃ x : MCore H lab F W, C0.q x = v.1 then clsQ H lab F W (h.choose : Sym2 V → ℤ)
  else 0

lemma gCat_spec {d c E : ℕ} (C0 : CoreCompression H lab F W d c E) {R : ℕ} (v : Cat d R)
    (x : MCore H lab F W) (hx : C0.q x = v.1) : gCat C0 R v = clsQ H lab F W x := by
  have h : ∃ x : MCore H lab F W, C0.q x = v.1 := ⟨x, hx⟩
  unfold gCat
  rw [dif_pos h, C0.class_eq_iff, h.choose_spec, hx, sub_self]
  exact zero_mem _

lemma gCat_of_not {d c E : ℕ} (C0 : CoreCompression H lab F W d c E) {R : ℕ} (v : Cat d R)
    (h : ¬ ∃ x : MCore H lab F W, C0.q x = v.1) : gCat C0 R v = 0 := by
  unfold gCat; rw [dif_neg h]

/-- the coordinate of a bounded core vector lies in the catalog box -/
lemma q_mem_box {d c E : ℕ} (C0 : CoreCompression H lab F W d c E) {R k : ℕ}
    (hR : c * k ≤ R) (x : MCore H lab F W) (hx : l1E (x : Sym2 V → ℤ) ≤ k) :
    C0.q x ∈ S07V34.box d R := by
  rw [S07V34.mem_box]
  intro i
  refine (C0.bound x i).trans ?_
  calc (c : ℤ) * l1E (x : Sym2 V → ℤ) ≤ c * k :=
        mul_le_mul_of_nonneg_left hx (Nat.cast_nonneg c)
    _ ≤ R := by exact_mod_cast hR

/-- **The fixed catalog generates every admissible `K_Z` (step 3).** -/
theorem catalog_generates {β : ℝ} {h : ℕ} (hβ : 0 < β) {d c E d' c' E' : ℕ}
    (hH3 : CommonNbrCond (H.comap (Subtype.val : {x // x ∈ W} → V)) (lab ∘ Subtype.val) F β)
    (hH4 : HingeCond (H.comap (Subtype.val : {x // x ∈ W} → V)) (lab ∘ Subtype.val) F β h)
    (hW : coreN0 β h ≤ W.card) (C0 : CoreCompression H lab F W d c E)
    {Z : Finset V} (hZ : (Z.card : ℝ) ≤ coreDelta β h * W.card)
    (CZ : DelCompression H lab F Z d' c' E') :
    AddSubgroup.closure {k | ∃ v, gCat C0 (catR β d c E d' c' E') v = k ∧
        gCat C0 (catR β d c E d' c' E') v ∈ KZ H lab F W Z} =
      (KZ H lab F W Z).toAddSubgroup := by
  obtain ⟨Y, hY, hspan⟩ := KZ_eq_span hβ hH3 hH4 hW C0 hZ CZ
  apply le_antisymm
  · rw [AddSubgroup.closure_le]
    rintro _ ⟨v, rfl, hv⟩
    exact hv
  · intro k hk
    have hk' : k ∈ KZ H lab F W Z := hk
    rw [hspan, ← Submodule.mem_toAddSubgroup, Submodule.span_int_eq_addSubgroupClosure] at hk'
    have hsub : clsQ H lab F W '' (Y : Set (Sym2 V → ℤ)) ⊆
        {k | ∃ v, gCat C0 (catR β d c E d' c' E') v = k ∧
          gCat C0 (catR β d c E d' c' E') v ∈ KZ H lab F W Z} := by
      rintro _ ⟨y, hy, rfl⟩
      obtain ⟨hy1, hy2, hy3⟩ := hY y hy
      have hyC : y ∈ MCore H lab F W := MZ_le_MCore H lab F W Z hy1
      have hb := q_mem_box (R := catR β d c E d' c' E') C0 (le_max_right E _) ⟨y, hyC⟩ hy3
      have hg := gCat_spec C0 ⟨_, hb⟩ ⟨y, hyC⟩ rfl
      refine ⟨⟨_, hb⟩, hg, ?_⟩
      rw [hg]
      exact (mem_KZ H lab F W).2 ⟨y, hy1, hy2, rfl⟩
    exact AddSubgroup.closure_mono hsub hk'

universe u v

/-- **Native rerouting of every active catalog entry (step 4).** The bound `U` is fixed from
`(β, h, d, c, E, d', c', E')` before the host. -/
theorem native_reroute {β : ℝ} (h : ℕ) (hβ : 0 < β) (d c E d' c' E' : ℕ) :
    ∃ U : ℕ, ∀ {V : Type u} [Fintype V] {I : Type v} {H : SimpleGraph V} {lab : V → I}
      {F : Set (Multiset I)} {W : Finset V},
      CommonNbrCond (H.comap (Subtype.val : {x // x ∈ W} → V)) (lab ∘ Subtype.val) F β →
      HingeCond (H.comap (Subtype.val : {x // x ∈ W} → V)) (lab ∘ Subtype.val) F β h →
      coreN0 β h ≤ W.card → ∀ C0 : CoreCompression H lab F W d c E,
      ∀ {Z : Finset V}, (Z.card : ℝ) ≤ coreDelta β h * W.card →
      DelCompression H lab F Z d' c' E' →
      ∀ v : Cat d (catR β d c E d' c' E'),
        gCat C0 (catR β d c E d' c' E') v ∈ KZ H lab F W Z →
        ∃ x, x ∈ MZ H lab F W Z ∧ x ∈ LamDel H lab F Z ∧ l1E x ≤ U ∧
          clsQ H lab F W x = gCat C0 (catR β d c E d' c' E') v := by
  set R := catR β d c E d' c' E' with hR
  set k := genK β d c d' c' E' with hk
  obtain ⟨U, hU⟩ := bounded_representative.{u} d R k
  refine ⟨U, ?_⟩
  intro V _ I H lab F W hH3 hH4 hW C0 Z hZ CZ v hv
  by_cases hc : ∃ x : MCore H lab F W, C0.q x = v.1
  swap
  · refine ⟨0, zero_mem _, zero_mem _, ?_, ?_⟩
    · simp [l1E]
    · rw [gCat_of_not C0 v hc]; simp [clsQ]
  obtain ⟨x0, hx0⟩ := hc
  rw [gCat_spec C0 v x0 hx0] at hv ⊢
  obtain ⟨Y, hY, hgen⟩ := bounded_generators hβ hH3 hH4 hW C0 hZ CZ
  obtain ⟨x1, hx1M, hx1L, hx1⟩ := (mem_KZ H lab F W).1 hv
  obtain ⟨f, hf⟩ := hgen x1 hx1M hx1L
  -- move to the core module
  have hYC : ∀ y ∈ Y, y ∈ MCore H lab F W := fun y hy => MZ_le_MCore H lab F W Z (hY y hy).1
  let Y' : Finset (MCore H lab F W) := Y.subtype (· ∈ MCore H lab F W)
  have hsumY : ∀ g : (Sym2 V → ℤ) → (Sym2 V → ℤ),
      ∑ y ∈ Y', g (y : Sym2 V → ℤ) = ∑ y ∈ Y, g y := by
    intro g
    rw [Finset.sum_subtype_eq_sum_filter, Finset.filter_true_of_mem hYC]
  let P : AddSubgroup (MCore H lab F W) :=
    ((MZ H lab F W Z ⊓ LamDel H lab F Z).comap (MCore H lab F W).subtype).toAddSubgroup
  have hℓ : S07V37.L1Like (fun x : MCore H lab F W => l1E (x : Sym2 V → ℤ)) :=
    ⟨fun x => S07V37.l1E_L1Like.nonneg _, fun x y => S07V37.l1E_L1Like.add_le _ _,
      fun z x => S07V37.l1E_L1Like.smul_le z _⟩
  have hS : ∀ s ∈ C0.S, ∀ i, |s i| ≤ R := fun s hs i =>
    (C0.S_bound s hs i).trans (by exact_mod_cast le_max_left _ _)
  have hY' : ∀ y ∈ Y', y ∈ P ∧ l1E (y : Sym2 V → ℤ) ≤ k ∧
      ∀ i, |C0.q.toAddMonoidHom y i| ≤ R := by
    intro y hy
    rw [Finset.mem_subtype] at hy
    obtain ⟨h1, h2, h3⟩ := hY _ hy
    exact ⟨⟨h1, h2⟩, h3, fun i => S07V34.mem_box.1 (q_mem_box C0 (le_max_right _ _) y h3) i⟩
  have hb : ∀ i, |v.1 i| ≤ R := S07V34.mem_box.1 v.2
  -- the physical word
  set w : MCore H lab F W := x0 - ∑ y ∈ Y', f (y : Sym2 V → ℤ) • y with hw
  have hwL : (w : Sym2 V → ℤ) ∈ LamCore H lab F W := by
    have h01 : (x0 : Sym2 V → ℤ) - x1 ∈ LamCore H lab F W := by
      have := hx1.symm
      unfold clsQ at this
      exact (Submodule.Quotient.eq _).1 this
    have hcoe : (w : Sym2 V → ℤ) = ((x0 : Sym2 V → ℤ) - x1) + (x1 - ∑ y ∈ Y, f y • y) := by
      rw [hw, Submodule.coe_sub, Submodule.coe_sum]
      simp only [Submodule.coe_smul]
      rw [hsumY (fun y => f y • y)]
      abel
    rw [hcoe]
    exact add_mem h01 hf.1
  have hqw : C0.q w ∈ span ℤ (C0.S : Set (Fin d → ℤ)) := (C0.mem_span_iff _).2 ⟨w, hwL, rfl⟩
  have hbK : qmk C0.S v.1 ∈ Kgrp C0.S (Y'.image C0.q.toAddMonoidHom) := by
    have hdec : v.1 = C0.q w + ∑ y ∈ Y', f (y : Sym2 V → ℤ) • C0.q y := by
      rw [hw, map_sub, map_sum]
      simp only [map_zsmul, hx0]
      abel
    have hcl : C0.q w ∈ AddSubgroup.closure (C0.S : Set (Fin d → ℤ)) := by
      rw [← Submodule.span_int_eq_addSubgroupClosure]; exact hqw
    rw [hdec, qmk_hom, map_add]
    have hz0 : (QuotientAddGroup.mk' (AddSubgroup.closure (C0.S : Set (Fin d → ℤ)))) (C0.q w) = 0 :=
      (QuotientAddGroup.eq_zero_iff _).2 hcl
    rw [hz0, zero_add, map_sum]
    refine AddSubgroup.sum_mem _ fun y hy => ?_
    rw [map_zsmul]
    exact AddSubgroup.zsmul_mem _ (AddSubgroup.subset_closure (Set.mem_image_of_mem (qmk C0.S)
      (Finset.mem_coe.2 (Finset.mem_image.2 ⟨y, hy, rfl⟩)))) _
  obtain ⟨x, hxP, hxU, hxq⟩ := hU (fun x : MCore H lab F W => l1E (x : Sym2 V → ℤ)) hℓ P
    C0.q.toAddMonoidHom C0.S hS Y' hY' v.1 hb hbK
  refine ⟨x, hxP.1, hxP.2, hxU, ?_⟩
  rw [C0.class_eq_iff]
  have : qmk C0.S (C0.q x) = qmk C0.S (C0.q x0) := by rw [hx0]; exact hxq
  rw [qmk_hom, qmk_hom, QuotientAddGroup.mk'_apply, QuotientAddGroup.mk'_apply,
    QuotientAddGroup.eq] at this
  have h2 : C0.q x - C0.q x0 = -(-C0.q x + C0.q x0) := by abel
  rw [h2]
  refine neg_mem ?_
  rw [← Submodule.mem_toAddSubgroup, Submodule.span_int_eq_addSubgroupClosure]
  exact this

end S07V42
