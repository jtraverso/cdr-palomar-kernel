/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license.
Authors: Juan Pablo Traverso Gianini
-/
module

public import CDRBicolour.Absorption.BRIGadget

/-!
# Averaged K₄ gadgets

For an edge `uv` let `P(u,v)` be its gadget pairs: ordered pairs of distinct points of class
`lab u + 1` if `uv` is monochromatic, and `(w, z)` with `w ∈ class(u) \ {u}`,
`z ∈ class(v) \ {v}` if it is bichromatic.  For every pair all four triangles of the K₄ are
bicoloured (`gad_allowed`), so the averaged gadget `gav u v = (2|P|)⁻¹ ∑_P gad u v w z`
covers `1_{uv} - |P|⁻¹ ∑_{(w,z) ∈ P} 1_{wz}` (`Minc_gav`).
-/

@[expose] public section

noncomputable section

namespace CDRBicolour.Absorption

open Finset TypedTriangle CDRBicolour.Prefix

section Average

variable {V : Type*} [Fintype V] [DecidableEq V] {lab : V → Fin 3}

variable (lab) in
/-- The gadget pairs of an (ordered) edge. -/
def pairsF (u v : V) : Finset (V × V) :=
  if lab u = lab v then (univ.filter fun w => lab w = lab u + 1).offDiag
  else (univ.filter fun w => lab w = lab u ∧ w ≠ u) ×ˢ (univ.filter fun z => lab z = lab v ∧ z ≠ v)

theorem tri_of {x y z : V} (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z)
    (h : (lab x = lab y ∧ lab y ≠ lab z) ∨ (lab x = lab z ∧ lab x ≠ lab y) ∨
      (lab y = lab z ∧ lab x ≠ lab y)) : ({x, y, z} : Finset V) ∈ tri lab :=
  mem_tri.mpr (isAllowed_triple lab hxy hxz hyz (cdrF_of h))

/-- The four triangles of a gadget are allowed, and its points are distinct. -/
theorem gad_allowed {u v w z : V} (huv : u ≠ v) (hp : (w, z) ∈ pairsF lab u v) :
    u ≠ w ∧ u ≠ z ∧ v ≠ w ∧ v ≠ z ∧ w ≠ z ∧
    ({u, v, w} : Finset V) ∈ tri lab ∧ ({u, v, z} : Finset V) ∈ tri lab ∧
    ({u, w, z} : Finset V) ∈ tri lab ∧ ({v, w, z} : Finset V) ∈ tri lab := by
  unfold pairsF at hp
  split_ifs at hp with hl
  · simp only [mem_offDiag, mem_filter, mem_univ, true_and] at hp
    obtain ⟨hw, hz, hwz⟩ := hp
    have hne : lab u + 1 ≠ lab u := fin3_succ_ne _
    have huw : u ≠ w := fun h => hne (by rw [← hw, h])
    have huz : u ≠ z := fun h => hne (by rw [← hz, h])
    have hvw : v ≠ w := fun h => hne (by rw [← hw, ← h, hl])
    have hvz : v ≠ z := fun h => hne (by rw [← hz, ← h, hl])
    refine ⟨huw, huz, hvw, hvz, hwz, tri_of huv huw hvw ?_, tri_of huv huz hvz ?_,
      tri_of huw huz hwz ?_, tri_of hvw hvz hwz ?_⟩
    · left; exact ⟨hl, by rw [hw, hl]; exact (fin3_succ_ne _).symm⟩
    · left; exact ⟨hl, by rw [hz, hl]; exact (fin3_succ_ne _).symm⟩
    · right; right; exact ⟨hw.trans hz.symm, by rw [hw]; exact hne.symm⟩
    · right; right; exact ⟨hw.trans hz.symm, by rw [hw, hl]; exact (fin3_succ_ne _).symm⟩
  · simp only [mem_product, mem_filter, mem_univ, true_and] at hp
    obtain ⟨⟨hw, hwu⟩, hz, hzv⟩ := hp
    have huz : u ≠ z := fun h => hl (by rw [h, hz])
    have hvw : v ≠ w := fun h => hl (by rw [← hw, h])
    have hwz : w ≠ z := fun h => hl (by rw [← hw, h, hz])
    refine ⟨Ne.symm hwu, huz, hvw, Ne.symm hzv, hwz, tri_of huv (Ne.symm hwu) hvw ?_,
      tri_of huv huz (Ne.symm hzv) ?_, tri_of (Ne.symm hwu) huz hwz ?_,
      tri_of hvw (Ne.symm hzv) hwz ?_⟩
    · right; left; exact ⟨hw.symm, hl⟩
    · right; right; exact ⟨hz.symm, hl⟩
    · left; exact ⟨hw.symm, by rw [hw, hz]; exact hl⟩
    · right; left; exact ⟨hz.symm, by rw [hw]; exact Ne.symm hl⟩

variable (lab) in
/-- The averaged gadget of an ordered edge. -/
def gav (u v : V) : Finset V → ℝ :=
  (1 / (2 * (#(pairsF lab u v) : ℝ))) • ∑ p ∈ pairsF lab u v, gad u v p.1 p.2

/-- **Coverage of the averaged gadget.** -/
theorem Minc_gav {u v : V} (huv : u ≠ v) (hP : (pairsF lab u v).Nonempty) (e : E0 V) :
    Minc lab (gav lab u v) e = (if e.1 = s(u, v) then 1 else 0) -
      (1 / (#(pairsF lab u v) : ℝ)) * ∑ p ∈ pairsF lab u v, (if e.1 = s(p.1, p.2) then 1 else 0) := by
  have hc : (0 : ℝ) < #(pairsF lab u v) := by exact_mod_cast hP.card_pos
  simp only [gav, map_smul, map_sum, Pi.smul_apply, Finset.sum_apply, smul_eq_mul]
  have : ∀ p ∈ pairsF lab u v, Minc lab (gad u v p.1 p.2) e =
      2 * (if e.1 = s(u, v) then 1 else 0) - 2 * (if e.1 = s(p.1, p.2) then 1 else 0) := by
    intro p hp
    obtain ⟨a1, a2, a3, a4, a5, t1, t2, t3, t4⟩ := gad_allowed huv hp
    exact Minc_gad huv a1 a2 a3 a4 a5 t1 t2 t3 t4 e
  rw [sum_congr rfl this, sum_sub_distrib, sum_const, ← mul_sum, nsmul_eq_mul]
  field_simp

/-- A representative ordered pair of an edge. -/
def rep (e : E0 V) : V × V := Quot.out e.1

theorem rep_spec (e : E0 V) : s((rep e).1, (rep e).2) = e.1 := by
  unfold rep
  exact Quot.out_eq e.1

theorem rep_ne (e : E0 V) : (rep e).1 ≠ (rep e).2 := by
  intro h
  apply e.2
  rw [← rep_spec e, h, Sym2.mk_isDiag_iff]

/-- Gadget pairs exist when every class has at least three points. -/
theorem pairsF_nonempty (hcls : ∀ k, 3 ≤ csz lab k) {u v : V} :
    (pairsF lab u v).Nonempty := by
  unfold pairsF
  split_ifs with hl
  · have h := hcls (lab u + 1)
    unfold csz at h
    obtain ⟨w, hw⟩ := card_pos.mp (by omega : 0 < #(univ.filter fun w => lab w = lab u + 1))
    have h2 : 1 < #((univ.filter fun w => lab w = lab u + 1).erase w) := by
      rw [card_erase_of_mem hw]; omega
    obtain ⟨z, hz⟩ := card_pos.mp (by omega : 0 < #((univ.filter fun w => lab w = lab u + 1).erase w))
    refine ⟨(w, z), mem_offDiag.mpr ⟨hw, (mem_erase.mp hz).2, (Ne.symm (mem_erase.mp hz).1)⟩⟩
  · have hu := hcls (lab u)
    have hv := hcls (lab v)
    unfold csz at hu hv
    have hU : 0 < #((univ.filter fun w => lab w = lab u).erase u) := by
      rw [card_erase_of_mem (by simp)]; omega
    have hV : 0 < #((univ.filter fun w => lab w = lab v).erase v) := by
      rw [card_erase_of_mem (by simp)]; omega
    obtain ⟨w, hw⟩ := card_pos.mp hU
    obtain ⟨z, hz⟩ := card_pos.mp hV
    refine ⟨(w, z), mem_product.mpr ⟨?_, ?_⟩⟩
    · simp only [mem_erase, mem_filter, mem_univ, true_and] at hw ⊢; exact ⟨hw.2, hw.1⟩
    · simp only [mem_erase, mem_filter, mem_univ, true_and] at hz ⊢; exact ⟨hz.2, hz.1⟩

variable (lab) in
/-- The averaged-gadget operator. -/
def Phi1 : (E0 V → ℝ) →ₗ[ℝ] (Finset V → ℝ) where
  toFun d := ∑ e, d e • gav lab (rep e).1 (rep e).2
  map_add' d d' := by simp [add_smul, sum_add_distrib]
  map_smul' r d := by simp [smul_sum, smul_smul]

variable (lab) in
/-- The averaging weight: how much of `d e` the gadgets of `e` push onto the edge `f`. -/
def avgW (e f : E0 V) : ℝ :=
  (1 / (#(pairsF lab (rep e).1 (rep e).2) : ℝ)) *
    ∑ p ∈ pairsF lab (rep e).1 (rep e).2, (if f.1 = s(p.1, p.2) then 1 else 0)

/-- **Coverage of the averaged-gadget operator**: `M Φ₁ d = d - Avg d`. -/
theorem Minc_Phi1 (hcls : ∀ k, 3 ≤ csz lab k) (d : E0 V → ℝ) (f : E0 V) :
    Minc lab (Phi1 lab d) f = d f - ∑ e, d e * avgW lab e f := by
  simp only [Phi1, LinearMap.coe_mk, AddHom.coe_mk, map_sum, map_smul, Finset.sum_apply,
    Pi.smul_apply, smul_eq_mul]
  have h : ∀ e : E0 V, Minc lab (gav lab (rep e).1 (rep e).2) f =
      (if f = e then 1 else 0) - avgW lab e f := by
    intro e
    rw [Minc_gav (rep_ne e) (pairsF_nonempty hcls) f, rep_spec e, avgW]
    congr 1
    by_cases hfe : f = e
    · rw [if_pos (congrArg Subtype.val hfe), if_pos hfe]
    · rw [if_neg (fun h => hfe (Subtype.ext h)), if_neg hfe]
  simp_rw [h, mul_sub, sum_sub_distrib, mul_ite, mul_one, mul_zero]
  rw [sum_ite_eq]
  simp

/-- Counting the orientations of an edge inside a set of ordered pairs. -/
theorem count_orient (S : Finset (V × V)) {x y : V} (hxy : x ≠ y) :
    ∑ p ∈ S, (if s(x, y) = s(p.1, p.2) then (1 : ℝ) else 0) =
      (if (x, y) ∈ S then 1 else 0) + (if (y, x) ∈ S then 1 else 0) := by
  have h : ∀ p : V × V, (if s(x, y) = s(p.1, p.2) then (1 : ℝ) else 0) =
      (if p = (x, y) then 1 else 0) + (if p = (y, x) then 1 else 0) := by
    rintro ⟨a, b⟩
    rcases eq_or_ne (a, b) (x, y) with h | h
    · obtain ⟨rfl, rfl⟩ := Prod.mk.inj h
      simp [hxy]
    · rcases eq_or_ne (a, b) (y, x) with h' | h'
      · obtain ⟨rfl, rfl⟩ := Prod.mk.inj h'
        simp [Sym2.eq_swap, hxy]
      · have : s(x, y) ≠ s(a, b) := by
          rw [Ne, Sym2.eq_iff]
          rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
          · exact h rfl
          · exact h' rfl
        simp [this, h, h']
  simp_rw [h, sum_add_distrib]
  rw [sum_ite_eq', sum_ite_eq']

variable (lab) in
/-- The type pattern of the gadget pairs of `(u, v)`, ignoring the exclusion of `u` and `v`. -/
def matchQ (u v : V) (X Y : Fin 3) : Prop :=
  (lab u = lab v ∧ X = lab u + 1 ∧ Y = lab u + 1) ∨ (lab u ≠ lab v ∧ X = lab u ∧ Y = lab v)

instance (u v : V) (X Y : Fin 3) : Decidable (matchQ lab u v X Y) := by
  unfold matchQ; infer_instance

/-- Membership in the gadget pairs, for a pair of distinct points not touching `u, v`. -/
theorem mem_pairsF {u v x y : V} (hxy : x ≠ y) :
    (x, y) ∈ pairsF lab u v ↔ matchQ lab u v (lab x) (lab y) ∧
      (lab u ≠ lab v → x ≠ u ∧ y ≠ v) := by
  unfold pairsF matchQ
  split_ifs with hl
  · simp only [mem_offDiag, mem_filter, mem_univ, true_and]
    constructor
    · rintro ⟨h1, h2, -⟩; exact ⟨Or.inl ⟨hl, h1, h2⟩, fun h => absurd hl h⟩
    · rintro ⟨h | h, -⟩
      · exact ⟨h.2.1, h.2.2, hxy⟩
      · exact absurd hl h.1
  · simp only [mem_product, mem_filter, mem_univ, true_and]
    constructor
    · rintro ⟨⟨h1, h2⟩, h3, h4⟩; exact ⟨Or.inr ⟨hl, h1, h3⟩, fun _ => ⟨h2, h4⟩⟩
    · rintro ⟨h | h, h'⟩
      · exact absurd h.1 hl
      · exact ⟨⟨h.2.1, (h' hl).1⟩, h.2.2, (h' hl).2⟩

variable (lab) in
/-- The uniform part of the averaging weight: depends only on the types. -/
def ut (e : E0 V) (X Y : Fin 3) : ℝ :=
  (1 / (#(pairsF lab (rep e).1 (rep e).2) : ℝ)) *
    ((if matchQ lab (rep e).1 (rep e).2 X Y then 1 else 0) +
      (if matchQ lab (rep e).1 (rep e).2 Y X then 1 else 0))

theorem avgW_eq (e f : E0 V) :
    avgW lab e f = (1 / (#(pairsF lab (rep e).1 (rep e).2) : ℝ)) *
      ((if ((rep f).1, (rep f).2) ∈ pairsF lab (rep e).1 (rep e).2 then 1 else 0) +
        (if ((rep f).2, (rep f).1) ∈ pairsF lab (rep e).1 (rep e).2 then 1 else 0)) := by
  unfold avgW
  rw [← rep_spec f, count_orient _ (rep_ne f)]

/-- **Local error of the averaging weight**: it differs from its uniform part only when `e`
touches `f`, and then by at most `2 / |P_e|`. -/
theorem avgW_sub_ut (hcls : ∀ k, 3 ≤ csz lab k) (e f : E0 V) :
    |avgW lab e f - ut lab e (lab (rep f).1) (lab (rep f).2)| ≤
      (2 / (#(pairsF lab (rep e).1 (rep e).2) : ℝ)) *
        (if (rep f).1 ∈ e.1 ∨ (rep f).2 ∈ e.1 then 1 else 0) := by
  have hP : (0 : ℝ) < #(pairsF lab (rep e).1 (rep e).2) := by
    exact_mod_cast (pairsF_nonempty hcls).card_pos
  set u := (rep e).1
  set v := (rep e).2
  set x := (rep f).1
  set y := (rep f).2
  have hxy : x ≠ y := rep_ne f
  have heu : u ∈ e.1 := by rw [← rep_spec e]; exact Sym2.mem_mk_left _ _
  have hev : v ∈ e.1 := by rw [← rep_spec e]; exact Sym2.mem_mk_right _ _
  rw [avgW_eq, ut, ← mul_sub, abs_mul, abs_of_pos (by positivity)]
  have t1 : |(if (x, y) ∈ pairsF lab u v then (1 : ℝ) else 0) -
      (if matchQ lab u v (lab x) (lab y) then 1 else 0)| ≤
      if x ∈ e.1 ∨ y ∈ e.1 then 1 else 0 := by
    by_cases ht : x ∈ e.1 ∨ y ∈ e.1
    · rw [if_pos ht]; split_ifs <;> norm_num
    · rw [if_neg ht]; push_neg at ht
      have hiff : (x, y) ∈ pairsF lab u v ↔ matchQ lab u v (lab x) (lab y) := by
        rw [mem_pairsF hxy]
        exact ⟨fun h => h.1, fun h => ⟨h, fun _ => ⟨fun h' => ht.1 (h' ▸ heu),
          fun h' => ht.2 (h' ▸ hev)⟩⟩⟩
      simp only [hiff, sub_self, abs_zero, le_refl]
  have t2 : |(if (y, x) ∈ pairsF lab u v then (1 : ℝ) else 0) -
      (if matchQ lab u v (lab y) (lab x) then 1 else 0)| ≤
      if x ∈ e.1 ∨ y ∈ e.1 then 1 else 0 := by
    by_cases ht : x ∈ e.1 ∨ y ∈ e.1
    · rw [if_pos ht]; split_ifs <;> norm_num
    · rw [if_neg ht]; push_neg at ht
      have hiff : (y, x) ∈ pairsF lab u v ↔ matchQ lab u v (lab y) (lab x) := by
        rw [mem_pairsF hxy.symm]
        exact ⟨fun h => h.1, fun h => ⟨h, fun _ => ⟨fun h' => ht.2 (h' ▸ heu),
          fun h' => ht.1 (h' ▸ hev)⟩⟩⟩
      simp only [hiff, sub_self, abs_zero, le_refl]
  have : |((if (x, y) ∈ pairsF lab u v then (1 : ℝ) else 0) +
      (if (y, x) ∈ pairsF lab u v then 1 else 0)) -
      ((if matchQ lab u v (lab x) (lab y) then 1 else 0) +
        (if matchQ lab u v (lab y) (lab x) then 1 else 0))| ≤
      2 * (if x ∈ e.1 ∨ y ∈ e.1 then 1 else 0) := by
    calc _ = |((if (x, y) ∈ pairsF lab u v then (1 : ℝ) else 0) -
          (if matchQ lab u v (lab x) (lab y) then 1 else 0)) +
          ((if (y, x) ∈ pairsF lab u v then (1 : ℝ) else 0) -
          (if matchQ lab u v (lab y) (lab x) then 1 else 0))| := by ring_nf
      _ ≤ _ := (abs_add_le _ _).trans (by linarith)
  calc 1 / (#(pairsF lab u v) : ℝ) * |_| ≤ 1 / (#(pairsF lab u v) : ℝ) *
        (2 * (if x ∈ e.1 ∨ y ∈ e.1 then 1 else 0)) :=
      mul_le_mul_of_nonneg_left this (by positivity)
    _ = _ := by ring

end Average

end CDRBicolour.Absorption
