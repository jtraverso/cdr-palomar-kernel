/-
Copyright (c) 2026 Juan Pablo Traverso Gianini.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import RequestProject.TypedTriangle.SlotPairing

@[expose] public section

/-!
# A3 (parte 2) — Gadget por aparición firmada (S02 §3)

Para una aparición del triángulo permitido `abc`, se elige un ápice fresco `x` de `ab`, una
bisagra compuesta robusta `J` entre `abc` y `abx`, y en el modo `D^c` los triángulos `acy`,
`bcz` que cubren `ac`, `bc`. Con `Y = J \ (W_ac ∪ W_bc)`:

* `Y` es basal (retirar `acy`, `bcz` de `D^c`);
* `Y ∪ W_ab ∪ W_ac ∪ W_bc = J ∪ W_ab` es basal (modo `D^x`);
* cada cuña cierra su slot en un triángulo permitido, con ápices `x, y, z` frescos y distintos.
-/

open Finset

noncomputable section
open Classical

namespace TypedTriangle

variable {V I : Type*} [Fintype V]

omit [Fintype V] in
lemma eq_three_of_mem {T : Finset V} (hT : T.card = 3) {a c y : V} (ha : a ∈ T) (hc : c ∈ T)
    (hy : y ∈ T) (hac : a ≠ c) (hay : a ≠ y) (hcy : c ≠ y) : T = {a, c, y} := by
  symm
  refine Finset.eq_of_subset_of_card_le ?_ ?_
  · intro w hw
    simp only [Finset.mem_insert, Finset.mem_singleton] at hw
    rcases hw with rfl | rfl | rfl <;> assumption
  · rw [hT, Finset.card_insert_of_notMem (by simp [hac, hay]),
      Finset.card_insert_of_notMem (by simp [hcy]), Finset.card_singleton]

omit [Fintype V] in
lemma triEdges_three {a b c : V} (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    triEdges ({a, b, c} : Finset V) = {s(a, b), s(a, c), s(b, c)} := by
  rw [triEdges_eq_insert_wedge hab hac hbc]; rfl

/-- **Gadget de aparición (forma explícita).** -/
theorem exists_gadget_core {H : Host V I} {F : Set (Multiset I)} {α : ℝ} {h : ℕ}
    (hα : 0 < α) (hH3 : CommonNbrCond H F α) (hH4 : HingeCond H F α h) {a b c : V}
    (hT : IsAllowed H F {a, b, c}) (U : Finset V) (haU : a ∈ U) (hbU : b ∈ U) (hcU : c ∈ U)
    (B : Finset (Sym2 V)) (d : ℕ) (hdeg : ∀ x, degIn B x ≤ d)
    (hwin1 : (U.card : ℝ) + 3 + 4 * d < α * Fintype.card V)
    (hwin2 : ((U.card : ℝ) + 1 + h + 5 * d) * 2 ^ Nat.choose h 2 ≤ α / 2 * Fintype.card V) :
    ∃ (Y : Finset (Sym2 V)) (x y z : V),
      IsAllowed H F {a, b, x} ∧ IsAllowed H F {a, c, y} ∧ IsAllowed H F {b, c, z} ∧
      x ∉ U ∧ y ∉ U ∧ z ∉ U ∧ x ≠ y ∧ x ≠ z ∧ y ≠ z ∧
      Basal H F Y ∧ Basal H F (Y ∪ (wedge a b x ∪ wedge a c y ∪ wedge b c z)) ∧
      Disjoint Y (wedge a b x ∪ wedge a c y ∪ wedge b c z) ∧
      Disjoint (Y ∪ (wedge a b x ∪ wedge a c y ∪ wedge b c z)) B ∧ Fresh U Y ∧
      (U ∪ support (Y ∪ (wedge a b x ∪ wedge a c y ∪ wedge b c z))).card ≤
        U.card + (2 * h - 2) ∧ Y.card ≤ (2 * h - 2).choose 2 := by
  obtain ⟨hab, hac, hbc⟩ := distinct_of_card_three hT.1
  -- ápice `x` de `ab`
  set X := U ∪ nbrIn B a ∪ nbrIn B b
  have hXc : (X.card : ℝ) < α * Fintype.card V := by
    have h1 : X.card ≤ U.card + 2 * d := by
      have := fun w => (card_nbrIn_le B w).trans (hdeg w)
      have h2 := (Finset.card_union_le (U ∪ nbrIn B a) (nbrIn B b)).trans
        (Nat.add_le_add_right (Finset.card_union_le U (nbrIn B a)) _)
      linarith [this a, this b]
    have : (X.card : ℝ) ≤ U.card + 2 * d := by exact_mod_cast h1
    linarith
  obtain ⟨x, hTx, hxX⟩ := exists_fresh_apex hH3 hT X hXc
  simp only [X, Finset.mem_union, not_or, nbrIn, Finset.mem_filter, Finset.mem_univ,
    true_and] at hxX
  obtain ⟨⟨hxU, hxBa⟩, hxBb⟩ := hxX
  have hcx : c ≠ x := fun h' => hxU (h' ▸ hcU)
  have hax : a ≠ x := fun h' => hxU (h' ▸ haU)
  have hbx : b ≠ x := fun h' => hxU (h' ▸ hbU)
  -- bisagra compuesta robusta entre `abc` y `abx`
  have hcardx : ((insert x U).card : ℝ) ≤ U.card + 1 := by
    exact_mod_cast Finset.card_insert_le x U
  obtain ⟨J, hJ, hJB, hJcx, hJU, hJc⟩ := exists_robust_composite_hinge hα hH3 hH4 hcx hT hTx
    (insert x U) B d hdeg (by linarith)
    (le_trans (mul_le_mul_of_nonneg_right (by linarith) (by positivity)) hwin2)
  obtain ⟨hJsub, hJdisj, ⟨Dc, hDc⟩, ⟨Dx, hDx⟩⟩ := hJ
  have notJ : ∀ f, f ∈ triEdges ({a, b, c} : Finset V) ∪ triEdges ({a, b, x} : Finset V) →
      f ∉ J := fun f hf hfJ => Finset.disjoint_left.1 hJdisj hfJ hf
  have habJ : s(a, b) ∉ J := notJ _ (Finset.mem_union_left _ (mem_triEdges.2 ⟨by simp, by simp, hab⟩))
  have hacJ : s(a, c) ∉ J := notJ _ (Finset.mem_union_left _ (mem_triEdges.2 ⟨by simp, by simp, hac⟩))
  have hbcJ : s(b, c) ∉ J := notJ _ (Finset.mem_union_left _ (mem_triEdges.2 ⟨by simp, by simp, hbc⟩))
  have haxJ : s(a, x) ∉ J := notJ _ (Finset.mem_union_right _ (mem_triEdges.2 ⟨by simp, by simp, hax⟩))
  have hbxJ : s(b, x) ∉ J := notJ _ (Finset.mem_union_right _ (mem_triEdges.2 ⟨by simp, by simp, hbx⟩))
  have hfreshJ : Fresh (insert x U) J := (show IsHinge H F a b c x J from
    ⟨hJsub, hJdisj, ⟨Dc, hDc⟩, ⟨Dx, hDx⟩⟩).fresh hJcx (insert x U) hJU
  have hsuppJ : ∀ w, w ∈ support J → w ∉ ({a, b, c, x} : Finset V) → w ∉ U := by
    intro w hw hwR hwU
    exact hwR (hJU w (Finset.mem_insert_of_mem hwU) hw)
  -- triángulo `acy` de `D^c`
  obtain ⟨T1, hT1, y, haT1, hcT1, hyT1, hya, hyc, hay, hcy⟩ :=
    hDc.third (p := a) (q := c) (by simp [wedge])
  obtain ⟨T2, hT2, z, hbT2, hcT2, hzT2, hzb, hzc, hbz, hcz⟩ :=
    hDc.third (p := b) (q := c) (by simp [wedge])
  have hayJ : s(a, y) ∈ J := by
    simp only [Finset.mem_union, wedge, Finset.mem_insert, Finset.mem_singleton,
      Sym2.eq_iff] at hay
    rcases hay with h' | (⟨-, h'⟩ | ⟨h', -⟩) | (⟨h', -⟩ | ⟨h', -⟩)
    · exact h'
    · exact absurd h' hyc
    · exact absurd h' hac
    · exact absurd h' hab
    · exact absurd h' hac
  have hyb : y ≠ b := fun h' => habJ (h' ▸ hayJ)
  have hcyJ : s(c, y) ∈ J := by
    simp only [Finset.mem_union, wedge, Finset.mem_insert, Finset.mem_singleton,
      Sym2.eq_iff] at hcy
    rcases hcy with h' | (⟨h', -⟩ | ⟨-, h'⟩) | (⟨h', -⟩ | ⟨-, h'⟩)
    · exact h'
    · exact absurd h'.symm hac
    · exact absurd h' hya
    · exact absurd h'.symm hbc
    · exact absurd h' hyb
  have hyx : y ≠ x := fun h' => haxJ (h' ▸ hayJ)
  have hbzJ : s(b, z) ∈ J := by
    simp only [Finset.mem_union, wedge, Finset.mem_insert, Finset.mem_singleton,
      Sym2.eq_iff] at hbz
    rcases hbz with h' | (⟨h', -⟩ | ⟨h', -⟩) | (⟨-, h'⟩ | ⟨h', -⟩)
    · exact h'
    · exact absurd h'.symm hab
    · exact absurd h' hbc
    · exact absurd h' hzc
    · exact absurd h' hbc
  have hza : z ≠ a := fun h' => habJ (by rw [Sym2.eq_swap]; exact h' ▸ hbzJ)
  have hczJ : s(c, z) ∈ J := by
    simp only [Finset.mem_union, wedge, Finset.mem_insert, Finset.mem_singleton,
      Sym2.eq_iff] at hcz
    rcases hcz with h' | (⟨h', -⟩ | ⟨-, h'⟩) | (⟨h', -⟩ | ⟨-, h'⟩)
    · exact h'
    · exact absurd h'.symm hac
    · exact absurd h' hza
    · exact absurd h'.symm hbc
    · exact absurd h' hzb
  have hzx : z ≠ x := fun h' => hbxJ (h' ▸ hbzJ)
  have hyU : y ∉ U := hsuppJ y (mem_support_of_mem hayJ (by simp)) (by
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or]; exact ⟨hya, hyb, hyc, hyx⟩)
  have hzU : z ∉ U := hsuppJ z (mem_support_of_mem hbzJ (by simp)) (by
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or]; exact ⟨hza, hzb, hzc, hzx⟩)
  have hT1eq : T1 = {a, c, y} := eq_three_of_mem (hDc.1 T1 hT1).1 haT1 hcT1 hyT1 hac
    (Ne.symm hya) (Ne.symm hyc)
  have hT2eq : T2 = {b, c, z} := eq_three_of_mem (hDc.1 T2 hT2).1 hbT2 hcT2 hzT2 hbc
    (Ne.symm hzb) (Ne.symm hzc)
  have hyz : y ≠ z := by
    intro hyz
    have hne : T1 ≠ T2 := by
      intro h'
      rw [h', hT2eq] at haT1
      simp only [Finset.mem_insert, Finset.mem_singleton] at haT1
      rcases haT1 with h'' | h'' | h''
      exacts [hab h'', hac h'', hza h''.symm]
    exact hne (hDc.unique hT1 hT2 (by rw [hT1eq]; exact mem_triEdges.2 ⟨by simp, by simp, Ne.symm hyc⟩)
      (by rw [hT2eq, ← hyz]; exact mem_triEdges.2 ⟨by simp, by simp [hyz], Ne.symm hyc⟩))
  have hTacy : IsAllowed H F {a, c, y} := hT1eq ▸ hDc.1 T1 hT1
  have hTbcz : IsAllowed H F {b, c, z} := hT2eq ▸ hDc.1 T2 hT2
  -- el gadget
  set Wab := wedge a b x
  set Wac := wedge a c y
  set Wbc := wedge b c z
  have hWacJ : Wac ⊆ J := by
    intro f hf; simp only [Wac, wedge, Finset.mem_insert, Finset.mem_singleton] at hf
    rcases hf with rfl | rfl
    · exact hayJ
    · exact hcyJ
  have hWbcJ : Wbc ⊆ J := by
    intro f hf; simp only [Wbc, wedge, Finset.mem_insert, Finset.mem_singleton] at hf
    rcases hf with rfl | rfl
    · exact hbzJ
    · exact hczJ
  have hWabJ : Disjoint J Wab := by
    simp only [Wab, wedge, Finset.disjoint_insert_right, Finset.disjoint_singleton_right]
    exact ⟨haxJ, hbxJ⟩
  set Y := J \ (Wac ∪ Wbc) with hYdef
  have hYsub : Y ⊆ J := Finset.sdiff_subset
  have hall : Y ∪ (Wab ∪ Wac ∪ Wbc) = J ∪ Wab := by
    ext f; simp only [Y, Finset.mem_union, Finset.mem_sdiff]
    constructor
    · rintro (⟨hf, -⟩ | (hf | hf) | hf)
      · exact Or.inl hf
      · exact Or.inr hf
      · exact Or.inl (hWacJ hf)
      · exact Or.inl (hWbcJ hf)
    · rintro (hf | hf)
      · by_cases h1 : f ∈ Wac ∪ Wbc
        · rcases Finset.mem_union.1 h1 with h2 | h2
          · exact Or.inr (Or.inl (Or.inr h2))
          · exact Or.inr (Or.inr h2)
        · exact Or.inl ⟨hf, by simpa using h1⟩
      · exact Or.inr (Or.inl (Or.inl hf))
  have hYbasal : Basal H F Y := by
    have hsub : ({T1, T2} : Finset (Finset V)) ⊆ Dc := by
      intro T hT; simp only [Finset.mem_insert, Finset.mem_singleton] at hT
      rcases hT with rfl | rfl <;> assumption
    refine Basal.congr ⟨_, hDc.sdiff_sub hsub⟩ ?_
    rw [Finset.biUnion_insert, Finset.singleton_biUnion, hT1eq, hT2eq,
      triEdges_eq_insert_wedge hac (Ne.symm hya) (Ne.symm hyc),
      triEdges_eq_insert_wedge hbc (Ne.symm hzb) (Ne.symm hzc),
      show wedge a b c = {s(a, c), s(b, c)} from rfl,
      show wedge a c y = Wac from rfl, show wedge b c z = Wbc from rfl]
    ext f
    have h1 : f ∈ J → f ≠ s(a, c) := fun hf he => hacJ (he ▸ hf)
    have h2 : f ∈ J → f ≠ s(b, c) := fun hf he => hbcJ (he ▸ hf)
    simp only [Y, Finset.mem_sdiff, Finset.mem_union, Finset.mem_insert, Finset.mem_singleton]
    constructor
    · rintro ⟨hf | hf | hf, hn⟩
      · exact ⟨hf, fun h => hn (h.elim (fun h => Or.inl (Or.inr h)) (fun h => Or.inr (Or.inr h)))⟩
      · exact absurd (Or.inl (Or.inl hf)) hn
      · exact absurd (Or.inr (Or.inl hf)) hn
    · rintro ⟨hf, hn⟩
      refine ⟨Or.inl hf, ?_⟩
      rintro ((h | h) | h | h)
      · exact h1 hf h
      · exact hn (Or.inl h)
      · exact h2 hf h
      · exact hn (Or.inr h)
  have h6 : 6 ≤ h := by
    obtain ⟨i, hi6, hih, -⟩ := hH4 a b c x hcx hT hTx
    omega
  refine ⟨Y, x, y, z, hTx, hTacy, hTbcz, hxU, hyU, hzU, Ne.symm hyx, Ne.symm hzx, hyz, hYbasal,
    ?_, ?_, ?_, (hfreshJ.subset hYsub).anti (Finset.subset_insert x U), ?_, ?_⟩
  · rw [hall]; exact ⟨Dx, hDx⟩
  · refine Finset.disjoint_union_right.2 ⟨Finset.disjoint_union_right.2
      ⟨Disjoint.mono_left hYsub hWabJ, ?_⟩, ?_⟩
    · exact Disjoint.mono_right Finset.subset_union_left Finset.sdiff_disjoint
    · exact Disjoint.mono_right Finset.subset_union_right Finset.sdiff_disjoint
  · rw [hall]
    refine Finset.disjoint_union_left.2 ⟨hJB, ?_⟩
    simp only [Wab, wedge, Finset.disjoint_insert_left, Finset.disjoint_singleton_left]
    exact ⟨hxBa, hxBb⟩
  · rw [hall, support_union, show Wab = wedge a b x from rfl, support_wedge]
    have hsub : U ∪ (support J ∪ {a, b, x}) ⊆ insert x (U ∪ support J) := by
      intro w hw
      simp only [Finset.mem_union, Finset.mem_insert, Finset.mem_singleton] at hw ⊢
      rcases hw with hw | hw | hw | hw | hw
      · exact Or.inr (Or.inl hw)
      · exact Or.inr (Or.inr hw)
      · exact Or.inr (Or.inl (hw ▸ haU))
      · exact Or.inr (Or.inl (hw ▸ hbU))
      · exact Or.inl hw
    refine (Finset.card_le_card hsub).trans ((Finset.card_insert_le _ _).trans ?_)
    have := Finset.card_union_le U (support J)
    omega
  · have := card_le_choose_of_support_le hJc
    rw [show 2 * h - 3 + 1 = 2 * h - 2 by omega] at this
    exact (Finset.card_le_card hYsub).trans this

/-- **Gadget de aparición (forma uniforme por slots).** Para una aparición de un triángulo
permitido `T ⊆ U`, existen `Y` y ápices `ap e` (para `e ∈ E(T)`), frescos fuera de `U` y
distintos, tales que cada `e ∪ W_e` es un triángulo permitido, `Y` y `Y ∪ ⋃ W_e` son
basales, y el gadget evita `B` y no tiene aristas dentro de `U`. -/
theorem exists_slot_gadget {H : Host V I} {F : Set (Multiset I)} {α : ℝ} {h : ℕ}
    (hα : 0 < α) (hH3 : CommonNbrCond H F α) (hH4 : HingeCond H F α h) {T : Finset V}
    (hT : IsAllowed H F T) (U : Finset V) (hTU : T ⊆ U)
    (B : Finset (Sym2 V)) (d : ℕ) (hdeg : ∀ x, degIn B x ≤ d)
    (hwin1 : (U.card : ℝ) + 3 + 4 * d < α * Fintype.card V)
    (hwin2 : ((U.card : ℝ) + 1 + h + 5 * d) * 2 ^ Nat.choose h 2 ≤ α / 2 * Fintype.card V) :
    ∃ (Y : Finset (Sym2 V)) (ap : Sym2 V → V),
      (∀ e ∈ triEdges T, ap e ∉ U ∧ ap e ∉ e ∧ IsAllowed H F (slotTri e (ap e))) ∧
      (∀ e ∈ triEdges T, ∀ e' ∈ triEdges T, ap e = ap e' → e = e') ∧
      Basal H F Y ∧ Basal H F (Y ∪ (triEdges T).biUnion (fun e => wedgeOf e (ap e))) ∧
      Disjoint Y ((triEdges T).biUnion (fun e => wedgeOf e (ap e))) ∧
      Disjoint (Y ∪ (triEdges T).biUnion (fun e => wedgeOf e (ap e))) B ∧ Fresh U Y ∧
      (U ∪ support (Y ∪ (triEdges T).biUnion (fun e => wedgeOf e (ap e)))).card ≤
        U.card + (2 * h - 2) ∧ Y.card ≤ (2 * h - 2).choose 2 := by
  obtain ⟨a, b, c, hab, hac, hbc, rfl⟩ := Finset.card_eq_three.1 hT.1
  have haU : a ∈ U := hTU (by simp)
  have hbU : b ∈ U := hTU (by simp)
  have hcU : c ∈ U := hTU (by simp)
  obtain ⟨Y, x, y, z, hTx, hTy, hTz, hxU, hyU, hzU, hxy, hxz, hyz, hY, hYW, hYWd, hYB, hYU,
    hcard, hYe⟩ := exists_gadget_core hα hH3 hH4 hT U haU hbU hcU B d hdeg hwin1 hwin2
  set ap : Sym2 V → V := fun e => if e = s(a, b) then x else if e = s(a, c) then y else z
  have h1 : s(a, c) ≠ s(a, b) := by
    intro h'; rw [Sym2.eq_iff] at h'; rcases h' with ⟨-, h'⟩ | ⟨h', -⟩
    exacts [hbc h'.symm, hab h']
  have h2 : s(b, c) ≠ s(a, b) := by
    intro h'; rw [Sym2.eq_iff] at h'; rcases h' with ⟨h', -⟩ | ⟨-, h'⟩
    exacts [hab h'.symm, hac h'.symm]
  have h3 : s(b, c) ≠ s(a, c) := by
    intro h'; rw [Sym2.eq_iff] at h'; rcases h' with ⟨h', -⟩ | ⟨h', -⟩
    exacts [hab h'.symm, hbc h']
  have hapab : ap s(a, b) = x := by simp [ap]
  have hapac : ap s(a, c) = y := by simp [ap, h1]
  have hapbc : ap s(b, c) = z := by simp [ap, h2, h3]
  have hE := triEdges_three hab hac hbc
  have hW : (triEdges ({a, b, c} : Finset V)).biUnion (fun e => wedgeOf e (ap e)) =
      wedge a b x ∪ wedge a c y ∪ wedge b c z := by
    rw [hE, Finset.biUnion_insert, Finset.biUnion_insert, Finset.singleton_biUnion, hapab, hapac,
      hapbc, wedgeOf_mk, wedgeOf_mk, wedgeOf_mk, Finset.union_assoc]
  refine ⟨Y, ap, ?_, ?_, hY, by rw [hW]; exact hYW, by rw [hW]; exact hYWd,
    by rw [hW]; exact hYB, hYU, by rw [hW]; exact hcard, hYe⟩
  · intro e he
    rw [hE] at he
    simp only [Finset.mem_insert, Finset.mem_singleton] at he
    rcases he with rfl | rfl | rfl
    · rw [hapab, slotTri_mk]
      exact ⟨hxU, by simp only [Sym2.mem_iff, not_or]; exact ⟨fun h' => hxU (h' ▸ haU),
        fun h' => hxU (h' ▸ hbU)⟩, hTx⟩
    · rw [hapac, slotTri_mk]
      exact ⟨hyU, by simp only [Sym2.mem_iff, not_or]; exact ⟨fun h' => hyU (h' ▸ haU),
        fun h' => hyU (h' ▸ hcU)⟩, hTy⟩
    · rw [hapbc, slotTri_mk]
      exact ⟨hzU, by simp only [Sym2.mem_iff, not_or]; exact ⟨fun h' => hzU (h' ▸ hbU),
        fun h' => hzU (h' ▸ hcU)⟩, hTz⟩
  · intro e he e' he' hee
    rw [hE] at he he'
    simp only [Finset.mem_insert, Finset.mem_singleton] at he he'
    rcases he with rfl | rfl | rfl <;> rcases he' with rfl | rfl | rfl <;>
      simp only [hapab, hapac, hapbc] at hee <;> first | rfl | exact absurd hee ‹_› |
        exact absurd hee.symm ‹_›

end TypedTriangle
