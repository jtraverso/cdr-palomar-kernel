/-
Copyright (c) 2026 Juan Pablo Traverso Gianini.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import RequestProject.TypedTriangle.SlotGadget

@[expose] public section

/-!
# A3 (parte 3) — Fase de gadgets y absorbedor terminal por slots (S02 §§3–6)

Un certificado firmado de `P` es una familia finita de apariciones `o ∈ O` de triángulos
permitidos `tri o`, con signo `sgn o`, tal que para cada arista `e`

  `#{o positivas con e ∈ E(tri o)} = #{o negativas con e ∈ E(tri o)} + 1_P(e)`.

`slot_absorber` construye, bajo (H3), (H4) y ventanas explícitas, un absorbedor `A` de `P`
(`A` y `A ∪ P` basales) disjunto del grafo prohibido `B` y sin aristas dentro de
`Z ∪ S` (`S` = vértices del certificado), para familias `F` arbitrarias.
-/

open Finset

noncomputable section
open Classical

namespace TypedTriangle

variable {V I : Type*} [Fintype V] {ι : Type*}

/-- Slots de una familia de apariciones: pares `(o, e)` con `e ∈ E(tri o)`. -/
def occSlots (O : Finset ι) (tri : ι → Finset V) : Finset (ι × Sym2 V) :=
  O.biUnion (fun o => (triEdges (tri o)).image (fun e => (o, e)))

omit [Fintype V] in
lemma mem_occSlots {O : Finset ι} {tri : ι → Finset V} {s : ι × Sym2 V} :
    s ∈ occSlots O tri ↔ s.1 ∈ O ∧ s.2 ∈ triEdges (tri s.1) := by
  obtain ⟨o, e⟩ := s
  simp only [occSlots, Finset.mem_biUnion, Finset.mem_image, Prod.mk.injEq]
  constructor
  · rintro ⟨o', ho', e', he', rfl, rfl⟩; exact ⟨ho', he'⟩
  · rintro ⟨ho, he⟩; exact ⟨o, ho, e, he, rfl, rfl⟩

omit [Fintype V] in
lemma fresh_wedges {σ : Type*} {Sl : Finset σ} {base : σ → Sym2 V} {ap : σ → V}
    {U : Finset V} (h : ∀ s ∈ Sl, ap s ∉ U) :
    Fresh U (Sl.biUnion (fun s => wedgeOf (base s) (ap s))) := by
  intro f hf
  obtain ⟨s, hs, hf⟩ := Finset.mem_biUnion.1 hf
  obtain ⟨p, -, rfl⟩ := mem_wedgeOf.1 hf
  exact ⟨ap s, by simp, h s hs⟩

lemma support_subset_of_inside {U : Finset V} {X : Finset (Sym2 V)} (hX : Inside U X) :
    support X ⊆ U := by
  intro w hw
  simp only [support, Finset.mem_filter, Finset.mem_univ, true_and] at hw
  obtain ⟨e, he, hwe⟩ := hw
  exact hX e he w hwe

lemma apex_mem_support {e : Sym2 V} {w : V} (he : ¬ e.IsDiag) {X : Finset (Sym2 V)}
    (hX : wedgeOf e w ⊆ X) : w ∈ support X := by
  induction e using Sym2.ind with
  | _ p q =>
  exact mem_support_of_mem (hX (mem_wedgeOf.2 ⟨p, by simp, rfl⟩)) (by simp)

omit [Fintype V] in
lemma biUnion_filter_insert {O : Finset ι} {o : ι} (tri : ι → Finset V) (p : ι → Prop)
    [DecidablePred p] (f : ι × Sym2 V → Finset (Sym2 V)) :
    ((occSlots (insert o O) tri).filter (fun s => p s.1)).biUnion f =
      (if p o then (triEdges (tri o)).biUnion (fun e => f (o, e)) else ∅) ∪
        ((occSlots O tri).filter (fun s => p s.1)).biUnion f := by
  ext g
  simp only [Finset.mem_biUnion, Finset.mem_filter, mem_occSlots, Finset.mem_insert,
    Finset.mem_union]
  constructor
  · rintro ⟨⟨o', e⟩, ⟨⟨ho | ho, he⟩, hp⟩, hg⟩
    · simp only at ho; subst ho
      left; rw [if_pos hp]; exact Finset.mem_biUnion.2 ⟨e, he, hg⟩
    · exact Or.inr ⟨(o', e), ⟨⟨ho, he⟩, hp⟩, hg⟩
  · rintro (hg | ⟨s, ⟨⟨hs, he⟩, hp⟩, hg⟩)
    · split_ifs at hg with hp
      · obtain ⟨e, he, hg⟩ := Finset.mem_biUnion.1 hg
        exact ⟨(o, e), ⟨⟨Or.inl rfl, he⟩, hp⟩, hg⟩
      · simp at hg
    · exact ⟨s, ⟨⟨Or.inr hs, he⟩, hp⟩, hg⟩

/-- **Fase de gadgets (S02 §3).** Para cada familia `O` de apariciones de triángulos
permitidos contenidos en `U`, se construyen gadgets frescos: `Y` y ápices `ap` (uno por slot),
frescos fuera de `U`, distintos, en `U'`, tales que `Y ∪ W(slots positivos)` y
`Y ∪ W(slots negativos)` son basales. -/
theorem gadget_phase {H : Host V I} {F : Set (Multiset I)} {α : ℝ} {h : ℕ}
    (hα : 0 < α) (hH3 : CommonNbrCond H F α) (hH4 : HingeCond H F α h)
    (B : Finset (Sym2 V)) (d : ℕ) (hdeg : ∀ x, degIn B x ≤ d)
    (tri : ι → Finset V) (sgn : ι → Prop) (Ub : ℕ)
    (hwin1 : (Ub : ℝ) + 3 + 4 * d < α * Fintype.card V)
    (hwin2 : ((Ub : ℝ) + 1 + h + 5 * d) * 2 ^ Nat.choose h 2 ≤ α / 2 * Fintype.card V) :
    ∀ (O : Finset ι) (U : Finset V), (∀ o ∈ O, IsAllowed H F (tri o) ∧ tri o ⊆ U) →
      U.card + O.card * (2 * h - 2) ≤ Ub →
      ∃ (Y : Finset (Sym2 V)) (ap : ι × Sym2 V → V) (U' : Finset V),
        U ⊆ U' ∧ U'.card ≤ U.card + O.card * (2 * h - 2) ∧
        (∀ s ∈ occSlots O tri, ap s ∉ U ∧ ap s ∈ U' ∧ ap s ∉ s.2 ∧
          IsAllowed H F (slotTri s.2 (ap s))) ∧
        (∀ s ∈ occSlots O tri, ∀ s' ∈ occSlots O tri, ap s = ap s' → s = s') ∧
        Basal H F (Y ∪ ((occSlots O tri).filter (fun s => sgn s.1)).biUnion
          (fun s => wedgeOf s.2 (ap s))) ∧
        Basal H F (Y ∪ ((occSlots O tri).filter (fun s => ¬ sgn s.1)).biUnion
          (fun s => wedgeOf s.2 (ap s))) ∧
        Disjoint Y ((occSlots O tri).biUnion (fun s => wedgeOf s.2 (ap s))) ∧
        Disjoint (Y ∪ (occSlots O tri).biUnion (fun s => wedgeOf s.2 (ap s))) B ∧
        Fresh U Y ∧ Inside U' Y ∧ Y.card ≤ O.card * (2 * h - 2).choose 2 := by
  intro O
  induction O using Finset.induction_on with
  | empty =>
    intro U _ _
    refine ⟨∅, fun s => (Quot.out s.2).1, U, subset_refl _, by simp, by simp [occSlots],
      by simp [occSlots], ?_, ?_, by simp, by simp [occSlots], fun e he => by simp at he,
      fun e he => by simp at he, by simp⟩
    · simpa [occSlots] using Basal.empty H F
    · simpa [occSlots] using Basal.empty H F
  | @insert o O ho ih =>
    intro U hOU hU
    have hoU := hOU o (Finset.mem_insert_self _ _)
    have hcardins : (insert o O).card = O.card + 1 := Finset.card_insert_of_notMem ho
    have hUb : (U.card : ℝ) ≤ Ub := by
      have : U.card ≤ Ub := by rw [hcardins] at hU; nlinarith
      exact_mod_cast this
    obtain ⟨Y₀, ap₀, hap₀, hinj₀, hY₀, hY₀W, hY₀Wd, hY₀B, hY₀U, hcard₀, hY₀e⟩ :=
      exists_slot_gadget hα hH3 hH4 hoU.1 U hoU.2 B d hdeg (by linarith)
        (le_trans (mul_le_mul_of_nonneg_right (by linarith) (by positivity)) hwin2)
    set W₀ := (triEdges (tri o)).biUnion (fun e => wedgeOf e (ap₀ e))
    set U₁ := U ∪ support (Y₀ ∪ W₀)
    have hUU₁ : U ⊆ U₁ := Finset.subset_union_left
    have hin₁ : Inside U₁ (Y₀ ∪ W₀) := (inside_support _).mono Finset.subset_union_right
    obtain ⟨Y', ap', U', hU₁U', hU'c, hap', hinj', hY'pos, hY'neg, hY'Wd, hY'B, hY'U, hY'in,
      hY'e⟩ :=
      ih U₁ (fun o' ho' => ⟨(hOU o' (Finset.mem_insert_of_mem ho')).1,
        (hOU o' (Finset.mem_insert_of_mem ho')).2.trans hUU₁⟩) (by
          rw [hcardins] at hU
          have : (O.card + 1) * (2 * h - 2) = O.card * (2 * h - 2) + (2 * h - 2) := by ring
          have h0 : (U ∪ support (Y₀ ∪ W₀)).card ≤ U.card + (2 * h - 2) := hcard₀
          omega)
    set ap : ι × Sym2 V → V := fun s => if s.1 = o then ap₀ s.2 else ap' s
    have hap_o : ∀ e, ap (o, e) = ap₀ e := fun e => by simp [ap]
    have hap_O : ∀ s ∈ occSlots O tri, ap s = ap' s := fun s hs => by
      have : s.1 ≠ o := fun h' => ho (h' ▸ (mem_occSlots.1 hs).1)
      simp [ap, this]
    have hap₀U₁ : ∀ e ∈ triEdges (tri o), ap₀ e ∈ U₁ := fun e he =>
      Finset.mem_union_right _ (apex_mem_support (not_isDiag_of_mem_triEdges he)
        (fun f hf => Finset.mem_union_right _ (Finset.mem_biUnion.2 ⟨e, he, hf⟩)))
    have hW'eq : ∀ (q : ι × Sym2 V → Prop) [DecidablePred q],
        ((occSlots O tri).filter q).biUnion (fun s => wedgeOf s.2 (ap s)) =
        ((occSlots O tri).filter q).biUnion (fun s => wedgeOf s.2 (ap' s)) := fun q _ =>
      Finset.biUnion_congr rfl (fun s hs => by rw [hap_O s (Finset.mem_filter.1 hs).1])
    have hW₀eq : (triEdges (tri o)).biUnion (fun e => wedgeOf (o, e).2 (ap (o, e))) = W₀ :=
      Finset.biUnion_congr rfl (fun e _ => by rw [hap_o])
    have hfresh' : ∀ (q : ι × Sym2 V → Prop) [DecidablePred q],
        Fresh U₁ (((occSlots O tri).filter q).biUnion (fun s => wedgeOf s.2 (ap' s))) :=
      fun q _ => fresh_wedges (fun s hs => (hap' s (Finset.mem_filter.1 hs).1).1)
    have hsplit : ∀ (q : ι → Prop) [DecidablePred q],
        ((occSlots (insert o O) tri).filter (fun s => q s.1)).biUnion
          (fun s => wedgeOf s.2 (ap s)) = (if q o then W₀ else ∅) ∪
        ((occSlots O tri).filter (fun s => q s.1)).biUnion (fun s => wedgeOf s.2 (ap' s)) := by
      intro q _
      rw [biUnion_filter_insert, hW'eq (fun s => q s.1)]
      congr 1
      split_ifs
      · exact hW₀eq
      · rfl
    have hWall : (occSlots (insert o O) tri).biUnion (fun s => wedgeOf s.2 (ap s)) =
        W₀ ∪ (occSlots O tri).biUnion (fun s => wedgeOf s.2 (ap' s)) := by
      have := hsplit (fun _ => True)
      simp only [if_true, Finset.filter_true] at this
      exact this
    have hY'U₁ : Fresh U₁ Y' := hY'U
    have hfreshall : Fresh U₁ ((occSlots O tri).biUnion (fun s => wedgeOf s.2 (ap' s))) :=
      fresh_wedges (fun s hs => (hap' s hs).1)
    have hdisj₁ : ∀ X, Fresh U₁ X → Disjoint (Y₀ ∪ W₀) X := fun X hX => hin₁.disjoint_fresh hX
    have hmode : ∀ (q : ι → Prop) [DecidablePred q],
        Basal H F (Y' ∪ ((occSlots O tri).filter (fun s => q s.1)).biUnion
          (fun s => wedgeOf s.2 (ap' s))) →
        Basal H F ((Y₀ ∪ Y') ∪ ((occSlots (insert o O) tri).filter (fun s => q s.1)).biUnion
          (fun s => wedgeOf s.2 (ap s))) := by
      intro q _ hq
      rw [hsplit q]
      set X0 : Finset (Sym2 V) := if q o then W₀ else ∅ with hX0
      set R := ((occSlots O tri).filter (fun s => q s.1)).biUnion (fun s => wedgeOf s.2 (ap' s))
      have heq : Y₀ ∪ Y' ∪ (X0 ∪ R) = (Y₀ ∪ X0) ∪ (Y' ∪ R) := by
        ext; simp only [Finset.mem_union]; tauto
      have hX0sub : Y₀ ∪ X0 ⊆ Y₀ ∪ W₀ := by
        intro f hf
        rw [hX0] at hf
        split_ifs at hf
        · exact hf
        · exact Finset.mem_union_left _ (by simpa using hf)
      have hq0 : Basal H F (Y₀ ∪ X0) := by
        rw [hX0]; split_ifs
        · exact hY₀W
        · simpa using hY₀
      rw [heq]
      exact Basal.union hq0 hq (Disjoint.mono_left hX0sub (hdisj₁ _ (hY'U₁.union (hfresh' (fun s => q s.1)))))
    have hcardU₁ : U₁.card ≤ U.card + (2 * h - 2) := hcard₀
    refine ⟨Y₀ ∪ Y', ap, U', hUU₁.trans hU₁U', ?_, ?_, ?_, hmode sgn hY'pos, hmode (fun o => ¬ sgn o) hY'neg, ?_, ?_,
      hY₀U.union (hY'U.anti hUU₁),
      ((hin₁.subset Finset.subset_union_left).mono hU₁U').union hY'in, ?_⟩
    · rw [hcardins]
      have : U.card + (O.card + 1) * (2 * h - 2) = U.card + (2 * h - 2) + O.card * (2 * h - 2) :=
        by ring
      omega
    · intro s hs
      rw [mem_occSlots, Finset.mem_insert] at hs
      obtain ⟨hs1 | hs1, hs2⟩ := hs
      · obtain ⟨o', e⟩ := s
        simp only at hs1 hs2; subst hs1
        rw [hap_o]
        obtain ⟨h1, h2, h3⟩ := hap₀ e hs2
        exact ⟨h1, hU₁U' (hap₀U₁ e hs2), h2, h3⟩
      · have hs' : s ∈ occSlots O tri := mem_occSlots.2 ⟨hs1, hs2⟩
        rw [hap_O s hs']
        obtain ⟨h1, h2, h3, h4⟩ := hap' s hs'
        exact ⟨fun h' => h1 (hUU₁ h'), h2, h3, h4⟩
    · intro s hs s' hs' hss'
      rw [mem_occSlots, Finset.mem_insert] at hs hs'
      obtain ⟨hs1 | hs1, hs2⟩ := hs <;> obtain ⟨hs1' | hs1', hs2'⟩ := hs'
      · obtain ⟨o₁, e₁⟩ := s; obtain ⟨o₂, e₂⟩ := s'
        simp only at hs1 hs2 hs1' hs2' hss'; subst hs1; subst hs1'
        rw [hap_o, hap_o] at hss'
        rw [hinj₀ e₁ hs2 e₂ hs2' hss']
      · exfalso
        obtain ⟨o₁, e₁⟩ := s
        simp only at hs1 hs2 hss'; subst hs1
        have hs'' : s' ∈ occSlots O tri := mem_occSlots.2 ⟨hs1', hs2'⟩
        rw [hap_o, hap_O s' hs''] at hss'
        exact (hap' s' hs'').1 (hss' ▸ hap₀U₁ e₁ hs2)
      · exfalso
        obtain ⟨o₂, e₂⟩ := s'
        simp only at hs1' hs2' hss'; subst hs1'
        have hs'' : s ∈ occSlots O tri := mem_occSlots.2 ⟨hs1, hs2⟩
        rw [hap_o, hap_O s hs''] at hss'
        exact (hap' s hs'').1 (hss' ▸ hap₀U₁ e₂ hs2')
      · have h1 : s ∈ occSlots O tri := mem_occSlots.2 ⟨hs1, hs2⟩
        have h2 : s' ∈ occSlots O tri := mem_occSlots.2 ⟨hs1', hs2'⟩
        rw [hap_O s h1, hap_O s' h2] at hss'
        exact hinj' s h1 s' h2 hss'
    · rw [hWall]
      refine Finset.disjoint_union_left.2 ⟨Finset.disjoint_union_right.2 ⟨hY₀Wd, ?_⟩,
        Finset.disjoint_union_right.2 ⟨?_, hY'Wd⟩⟩
      · exact Disjoint.mono_left Finset.subset_union_left (hdisj₁ _ hfreshall)
      · exact (Disjoint.mono_left Finset.subset_union_right (hdisj₁ _ hY'U₁)).symm
    · rw [hWall]
      have h1 := Finset.disjoint_union_left.1 hY₀B
      have h2 := Finset.disjoint_union_left.1 hY'B
      have heq : Y₀ ∪ Y' ∪ (W₀ ∪ (occSlots O tri).biUnion (fun s => wedgeOf s.2 (ap' s))) =
          (Y₀ ∪ W₀) ∪ (Y' ∪ (occSlots O tri).biUnion (fun s => wedgeOf s.2 (ap' s))) := by
        ext; simp only [Finset.mem_union]; tauto
      rw [heq]
      exact Finset.disjoint_union_left.2 ⟨hY₀B, hY'B⟩
    · rw [hcardins, Nat.succ_mul]
      exact (Finset.card_union_le _ _).trans (by omega)

omit [Fintype V] in
lemma occSlots_filter_card {O : Finset ι} {tri : ι → Finset V} (q : ι → Prop) [DecidablePred q]
    (e : Sym2 V) :
    ((occSlots O tri).filter (fun s => q s.1 ∧ s.2 = e)).card =
      (O.filter (fun o => q o ∧ e ∈ triEdges (tri o))).card := by
  have : (occSlots O tri).filter (fun s => q s.1 ∧ s.2 = e) =
      (O.filter (fun o => q o ∧ e ∈ triEdges (tri o))).image (fun o => (o, e)) := by
    ext ⟨o, f⟩
    simp only [Finset.mem_filter, mem_occSlots, Finset.mem_image, Prod.mk.injEq]
    constructor
    · rintro ⟨⟨ho, hf⟩, hq, rfl⟩; exact ⟨o, ⟨ho, hq, hf⟩, rfl, rfl⟩
    · rintro ⟨o', ⟨ho', hq, he⟩, rfl, rfl⟩; exact ⟨⟨ho', he⟩, hq, rfl⟩
  rw [this, Finset.card_image_of_injective _ (fun a b h => by simpa using h)]

omit [Fintype V] in
lemma occSlots_card_le {O : Finset ι} {tri : ι → Finset V}
    (hO : ∀ o ∈ O, (tri o).card = 3) : (occSlots O tri).card ≤ 3 * O.card := by
  refine Finset.card_biUnion_le.trans ?_
  calc ∑ o ∈ O, ((triEdges (tri o)).image (fun e => (o, e))).card
      ≤ ∑ o ∈ O, (triEdges (tri o)).card := Finset.sum_le_sum fun o _ => Finset.card_image_le
    _ = ∑ _o ∈ O, 3 := Finset.sum_congr rfl fun o ho => by rw [card_triEdges, hO o ho]; rfl
    _ = 3 * O.card := by rw [Finset.sum_const, smul_eq_mul, mul_comm]

/-- **Absorbedor terminal por slots (S02, teorema terminal, familia `F` arbitraria).**
Sea `P` un grafo con vértices en `Z` y un certificado firmado formado por apariciones
`o ∈ O` de triángulos permitidos `tri o` con signos `sgn o`, cuyas aristas cuentan `1_P`
(identidad (4.1)). Bajo (H3), (H4) y las ventanas
`(Ub + 3 + 4d < α n)`, `((Ub + 1 + h + 5d) 2^{C(h,2)} ≤ (α/2) n)` con
`Ub ≥ |Z ∪ S| + |O|(2h−2) + 3|O|(2h−3)` (`S` = vértices del certificado), existe un
absorbedor `A` de `P` (`A` y `A ∪ P` basales, `A ∩ P = ∅`), disjunto del grafo prohibido `B`
(grado `≤ d`), sin aristas dentro de `Z ∪ S`, y con a lo sumo
`|O|(2h−2) + 3|O|(2h−3)` vértices nuevos. -/
theorem slot_absorber {H : Host V I} {F : Set (Multiset I)} {α : ℝ} {h : ℕ}
    (hα : 0 < α) (hH3 : CommonNbrCond H F α) (hH4 : HingeCond H F α h)
    (B : Finset (Sym2 V)) (d : ℕ) (hdeg : ∀ x, degIn B x ≤ d) (P : Finset (Sym2 V))
    (O : Finset ι) (tri : ι → Finset V) (sgn : ι → Prop) (hO : ∀ o ∈ O, IsAllowed H F (tri o))
    (hcert : ∀ e, ((O.filter (fun o => sgn o ∧ e ∈ triEdges (tri o))).card : ℤ) =
      (O.filter (fun o => ¬ sgn o ∧ e ∈ triEdges (tri o))).card + if e ∈ P then 1 else 0)
    (Z : Finset V) (hPZ : Inside Z P) (Ub : ℕ)
    (hUb : (Z ∪ O.biUnion tri).card + O.card * (2 * h - 2) + 3 * O.card * (2 * h - 3) ≤ Ub)
    (hwin1 : (Ub : ℝ) + 3 + 4 * d < α * Fintype.card V)
    (hwin2 : ((Ub : ℝ) + 1 + h + 5 * d) * 2 ^ Nat.choose h 2 ≤ α / 2 * Fintype.card V) :
    ∃ A, IsAbsorber H F A P ∧ Disjoint A B ∧ Fresh (Z ∪ O.biUnion tri) A ∧
      ((Z ∪ O.biUnion tri) ∪ support A).card ≤
        (Z ∪ O.biUnion tri).card + O.card * (2 * h - 2) + 3 * O.card * (2 * h - 3) ∧
      A.card ≤ O.card * (4 * (2 * h - 2).choose 2 + 6) := by
  set U₀ := Z ∪ O.biUnion tri
  have htriU₀ : ∀ o ∈ O, tri o ⊆ U₀ := fun o ho =>
    (Finset.subset_biUnion_of_mem tri ho).trans Finset.subset_union_right
  have hZU₀ : Z ⊆ U₀ := Finset.subset_union_left
  obtain ⟨Y, ap, U₁, hU₀₁, hU₁c, hap, hinj, hYpos, hYneg, hYWd, hYB, hYU₀, hYin, hYe⟩ :=
    gadget_phase hα hH3 hH4 B d hdeg tri sgn Ub hwin1 hwin2 O U₀
      (fun o ho => ⟨hO o ho, htriU₀ o ho⟩) (by omega)
  set Sl := occSlots O tri
  have hbaseU₀ : ∀ s ∈ Sl, ∀ p ∈ s.2, p ∈ U₀ := fun s hs p hp =>
    htriU₀ _ (mem_occSlots.1 hs).1 (mem_of_mem_triEdges (mem_occSlots.1 hs).2 hp)
  have hSF : SlotFamily H F Prod.snd ap Sl U₁ P :=
    ⟨fun s hs => ⟨not_isDiag_of_mem_triEdges (mem_occSlots.1 hs).2, (hap s hs).2.2.1,
      (hap s hs).2.2.2⟩, hinj, fun s hs s' hs' h' => (hap s hs).1 (hbaseU₀ s' hs' _ h'),
      fun s hs => ⟨fun p hp => hU₀₁ (hbaseU₀ s hs p hp), (hap s hs).2.1⟩,
      (hPZ.mono hZU₀).mono hU₀₁, fun e he s hs h' => (hap s hs).1 (hZU₀ (hPZ e he _ h'))⟩
  have hSC : SlotCount Prod.snd (fun s : ι × Sym2 V => sgn s.1) Sl P := by
    intro e
    have h1 := occSlots_filter_card (O := O) (tri := tri) sgn e
    have h2 := occSlots_filter_card (O := O) (tri := tri) (fun o => ¬ sgn o) e
    rw [h1, h2]; exact hcert e
  have hN : (Sl.filter (fun s => ¬ sgn s.1)).card ≤ 3 * O.card :=
    (Finset.card_filter_le _ _).trans (occSlots_card_le (fun o ho => (hO o ho).1))
  obtain ⟨J, hJneg, hJpos, hJB, hJU₁, hJc, hJe⟩ :=
    pairing_phase hα hH3 hH4 B d hdeg P Prod.snd ap (fun s => sgn s.1) Ub (by linarith)
      (le_trans (mul_le_mul_of_nonneg_right (by linarith) (by positivity)) hwin2)
      (3 * O.card) Sl U₁ hN (by nlinarith) hSF hSC
  set Wpos := (Sl.filter (fun s => sgn s.1)).biUnion (fun s => wedgeOf s.2 (ap s))
  set Wneg := (Sl.filter (fun s => ¬ sgn s.1)).biUnion (fun s => wedgeOf s.2 (ap s))
  have hWall : Sl.biUnion (fun s => wedgeOf s.2 (ap s)) = Wpos ∪ Wneg := by
    show _ = (Sl.filter _).biUnion _ ∪ (Sl.filter _).biUnion _
    rw [← Finset.union_biUnion, Finset.filter_union_filter_not_eq]
  have hWposneg : Disjoint Wpos Wneg := by
    rw [Finset.disjoint_biUnion_left]
    intro s hs
    exact hSF.wedge_disjoint_biUnion (Finset.mem_filter.1 hs).1 _ (Finset.filter_subset _ _)
      (fun h' => (Finset.mem_filter.1 h').2 (Finset.mem_filter.1 hs).2)
  have hWposin : Inside U₁ Wpos := hSF.inside_wedges _ (Finset.filter_subset _ _)
  have hWnegin : Inside U₁ Wneg := hSF.inside_wedges _ (Finset.filter_subset _ _)
  have hYWpos : Disjoint Y Wpos := Disjoint.mono_right (by rw [hWall]; exact
    Finset.subset_union_left) hYWd
  have hYWneg : Disjoint Y Wneg := Disjoint.mono_right (by rw [hWall]; exact
    Finset.subset_union_right) hYWd
  have hPU₁ : Inside U₁ P := hSF.insideP
  have hWP : ∀ X ⊆ Sl, Disjoint (X.biUnion (fun s => wedgeOf s.2 (ap s))) P := by
    intro X hX
    rw [Finset.disjoint_biUnion_left]
    intro s hs
    rw [Finset.disjoint_right]
    intro f hf
    exact not_mem_wedgeOf_of_not_mem (hSF.apexP f hf s (hX hs))
  have hYP : Disjoint Y P := ((hPZ.mono hZU₀).disjoint_fresh hYU₀).symm
  have hJP : Disjoint J P := (hPU₁.disjoint_fresh hJU₁).symm
  refine ⟨Y ∪ (Wpos ∪ Wneg) ∪ J, ⟨?_, ?_, ?_⟩, ?_, ?_, ?_, ?_⟩
  · refine Finset.disjoint_union_left.2 ⟨Finset.disjoint_union_left.2 ⟨hYP,
      Finset.disjoint_union_left.2 ⟨hWP _ (Finset.filter_subset _ _),
        hWP _ (Finset.filter_subset _ _)⟩⟩, hJP⟩
  · have heq : Y ∪ (Wpos ∪ Wneg) ∪ J = (Y ∪ Wpos) ∪ (J ∪ Wneg) := by
      ext; simp only [Finset.mem_union]; tauto
    rw [heq]
    refine Basal.union hYpos hJneg ?_
    refine Finset.disjoint_union_left.2 ⟨Finset.disjoint_union_right.2
      ⟨hYin.disjoint_fresh hJU₁, hYWneg⟩, Finset.disjoint_union_right.2
      ⟨hWposin.disjoint_fresh hJU₁, hWposneg⟩⟩
  · have heq : Y ∪ (Wpos ∪ Wneg) ∪ J ∪ P = (Y ∪ Wneg) ∪ (J ∪ Wpos ∪ P) := by
      ext; simp only [Finset.mem_union]; tauto
    rw [heq]
    refine Basal.union hYneg hJpos ?_
    refine Finset.disjoint_union_left.2 ⟨Finset.disjoint_union_right.2
      ⟨Finset.disjoint_union_right.2 ⟨hYin.disjoint_fresh hJU₁, hYWpos⟩, hYP⟩,
      Finset.disjoint_union_right.2 ⟨Finset.disjoint_union_right.2
      ⟨hWnegin.disjoint_fresh hJU₁, hWposneg.symm⟩, hWP _ (Finset.filter_subset _ _)⟩⟩
  · rw [← hWall]
    exact Finset.disjoint_union_left.2 ⟨hYB, hJB⟩
  · rw [← hWall]
    exact (hYU₀.union (fresh_wedges (fun s hs => (hap s hs).1))).union (hJU₁.anti hU₀₁)
  · have hsub : U₀ ∪ support (Y ∪ (Wpos ∪ Wneg) ∪ J) ⊆ U₁ ∪ support J := by
      rw [support_union, support_union, support_union]
      intro w hw
      simp only [Finset.mem_union] at hw ⊢
      rcases hw with hw | ((hw | hw | hw) | hw)
      · exact Or.inl (hU₀₁ hw)
      · exact Or.inl (support_subset_of_inside hYin hw)
      · exact Or.inl (support_subset_of_inside hWposin hw)
      · exact Or.inl (support_subset_of_inside hWnegin hw)
      · exact Or.inr hw
    refine (Finset.card_le_card hsub).trans (hJc.trans ?_)
    omega
  · have hSl : Sl.card ≤ 3 * O.card := occSlots_card_le (fun o ho => (hO o ho).1)
    have hW : (Wpos ∪ Wneg).card ≤ 2 * Sl.card := by
      rw [← hWall]
      refine Finset.card_biUnion_le.trans ?_
      rw [mul_comm, ← smul_eq_mul, ← Finset.sum_const]
      refine Finset.sum_le_sum fun s _ => ?_
      refine Finset.card_image_le.trans ?_
      induction s.2 using Sym2.ind with
      | _ x y => rw [Sym2.toFinset_mk_eq]; exact Finset.card_le_two
    refine (Finset.card_union_le _ _).trans ?_
    refine (Nat.add_le_add_right (Finset.card_union_le _ _) _).trans ?_
    have : 3 * O.card * (2 * h - 2).choose 2 = O.card * (3 * (2 * h - 2).choose 2) := by ring
    nlinarith

/-! ### Certificados enteros `1_P = Σ c_T 1_{E(T)}` -/

/-- Apariciones de un certificado entero: `|c_T|` copias de cada triángulo. -/
def coeffOcc (S : Finset (Finset V)) (c : Finset V → ℤ) : Finset (Finset V × ℕ) :=
  S.biUnion (fun T => (Finset.range (c T).natAbs).image (fun j => (T, j)))

omit [Fintype V] in
lemma mem_coeffOcc {S : Finset (Finset V)} {c : Finset V → ℤ} {o : Finset V × ℕ} :
    o ∈ coeffOcc S c ↔ o.1 ∈ S ∧ o.2 < (c o.1).natAbs := by
  obtain ⟨T, j⟩ := o
  simp only [coeffOcc, Finset.mem_biUnion, Finset.mem_image, Finset.mem_range, Prod.mk.injEq]
  constructor
  · rintro ⟨T', hT', j', hj', rfl, rfl⟩; exact ⟨hT', hj'⟩
  · rintro ⟨hT, hj⟩; exact ⟨T, hT, j, hj, rfl, rfl⟩

omit [Fintype V] in
lemma coeffOcc_filter_card (S : Finset (Finset V)) (c : Finset V → ℤ) (q : Finset V → Prop)
    [DecidablePred q] :
    ((coeffOcc S c).filter (fun o => q o.1)).card = ∑ T ∈ S.filter q, (c T).natAbs := by
  have : (coeffOcc S c).filter (fun o => q o.1) =
      (S.filter q).biUnion (fun T => (Finset.range (c T).natAbs).image (fun j => (T, j))) := by
    ext ⟨T, j⟩
    simp only [Finset.mem_filter, mem_coeffOcc, Finset.mem_biUnion, Finset.mem_image,
      Finset.mem_range, Prod.mk.injEq]
    constructor
    · rintro ⟨⟨hT, hj⟩, hq⟩; exact ⟨T, ⟨hT, hq⟩, j, hj, rfl, rfl⟩
    · rintro ⟨T', ⟨hT', hq⟩, j', hj', rfl, rfl⟩; exact ⟨⟨hT', hj'⟩, hq⟩
  rw [this, Finset.card_biUnion]
  · exact Finset.sum_congr rfl fun T _ => by
      rw [Finset.card_image_of_injective _ (fun a b h => by simpa using h), Finset.card_range]
  · intro T _ T' _ hTT'
    simp only [Function.onFun]
    rw [Finset.disjoint_left]
    intro o ho ho'
    simp only [Finset.mem_image] at ho ho'
    obtain ⟨j, -, rfl⟩ := ho
    obtain ⟨j', -, h⟩ := ho'
    exact hTT' (congrArg Prod.fst h).symm

/-- **Absorbedor terminal desde un certificado entero (S02 (1.1)).** Si
`1_P = Σ_T c_T 1_{E(T)}` con `c` soportado en triángulos permitidos y `Σ |c_T| ≤ K`, `P` tiene
sus vértices en `Z`, y se cumplen (H3), (H4) y las ventanas con
`Ub ≥ |Z ∪ S| + K(2h−2) + 3K(2h−3)` (`S` = vértices de los triángulos con `c_T ≠ 0`),
existe un absorbedor `A` de `P` que evita `B` y no tiene aristas dentro de `Z ∪ S`.
**Coste lineal de aristas (G2):** `|A| ≤ K (4 C(2h−2, 2) + 6)`, sumando el coste por gadget
(`≤ C(2h−2,2)` aristas por aparición), por par de emparejamiento (`≤ C(2h−2,2)` por slot
negativo, `≤ 3K` slots negativos) y por cuña (`2` aristas por slot, `≤ 3K` slots). -/
theorem slot_absorber_of_coeffs {H : Host V I} {F : Set (Multiset I)} {α : ℝ} {h : ℕ}
    (hα : 0 < α) (hH3 : CommonNbrCond H F α) (hH4 : HingeCond H F α h)
    (B : Finset (Sym2 V)) (d : ℕ) (hdeg : ∀ x, degIn B x ≤ d) (P : Finset (Sym2 V))
    (S : Finset (Finset V)) (hS : ∀ T ∈ S, IsAllowed H F T) (c : Finset V → ℤ)
    (hP : ∀ e, ind P e = ∑ T ∈ S, c T * ind (triEdges T) e) (K : ℕ)
    (hK : ∑ T ∈ S, (c T).natAbs ≤ K) (Z : Finset V) (hPZ : Inside Z P) (Ub : ℕ)
    (hUb : (Z ∪ (S.filter (fun T => c T ≠ 0)).biUnion id).card + K * (2 * h - 2) +
      3 * K * (2 * h - 3) ≤ Ub)
    (hwin1 : (Ub : ℝ) + 3 + 4 * d < α * Fintype.card V)
    (hwin2 : ((Ub : ℝ) + 1 + h + 5 * d) * 2 ^ Nat.choose h 2 ≤ α / 2 * Fintype.card V) :
    ∃ A, IsAbsorber H F A P ∧ Disjoint A B ∧
      Fresh (Z ∪ (S.filter (fun T => c T ≠ 0)).biUnion id) A ∧
      ((Z ∪ (S.filter (fun T => c T ≠ 0)).biUnion id) ∪ support A).card ≤
        (Z ∪ (S.filter (fun T => c T ≠ 0)).biUnion id).card + K * (2 * h - 2) +
          3 * K * (2 * h - 3) ∧
      A.card ≤ K * (4 * (2 * h - 2).choose 2 + 6) := by
  set O := coeffOcc S c
  have hOS : O.biUnion Prod.fst = (S.filter (fun T => c T ≠ 0)).biUnion id := by
    ext x
    simp only [Finset.mem_biUnion, mem_coeffOcc, Finset.mem_filter, id, O]
    constructor
    · rintro ⟨⟨T, j⟩, ⟨hT, hj⟩, hx⟩
      exact ⟨T, ⟨hT, fun h0 => by simp [h0] at hj⟩, hx⟩
    · rintro ⟨T, ⟨hT, hc⟩, hx⟩
      exact ⟨(T, 0), ⟨hT, by simpa [Int.natAbs_pos] using hc⟩, hx⟩
  have hOcard : O.card ≤ K := by
    have := coeffOcc_filter_card S c (fun _ => True)
    simp only [Finset.filter_true] at this
    show (coeffOcc S c).card ≤ K
    rw [this]; exact hK
  have hcert : ∀ e, ((O.filter (fun o => 0 < c o.1 ∧ e ∈ triEdges o.1)).card : ℤ) =
      (O.filter (fun o => ¬ 0 < c o.1 ∧ e ∈ triEdges o.1)).card + if e ∈ P then 1 else 0 := by
    intro e
    rw [coeffOcc_filter_card S c (fun T => 0 < c T ∧ e ∈ triEdges T),
      coeffOcc_filter_card S c (fun T => ¬ 0 < c T ∧ e ∈ triEdges T)]
    have hind : (if e ∈ P then (1 : ℤ) else 0) = ∑ T ∈ S.filter (fun T => e ∈ triEdges T), c T := by
      have := hP e
      simp only [ind] at this
      rw [this, Finset.sum_filter]
      exact Finset.sum_congr rfl fun T _ => by split_ifs <;> simp
    rw [hind, ← Finset.sum_filter_add_sum_filter_not (S.filter (fun T => e ∈ triEdges T))
      (fun T => 0 < c T), Finset.filter_filter, Finset.filter_filter]
    push_cast
    have h1 : ∑ T ∈ S.filter (fun T => 0 < c T ∧ e ∈ triEdges T), |c T| =
        ∑ T ∈ S.filter (fun T => e ∈ triEdges T ∧ 0 < c T), c T := by
      rw [show S.filter (fun T => e ∈ triEdges T ∧ 0 < c T) =
        S.filter (fun T => 0 < c T ∧ e ∈ triEdges T) from Finset.filter_congr (fun _ _ => and_comm)]
      exact Finset.sum_congr rfl fun T hT => by
        rw [abs_of_pos (Finset.mem_filter.1 hT).2.1]
    have h2 : ∑ T ∈ S.filter (fun T => ¬ 0 < c T ∧ e ∈ triEdges T), |c T| =
        -∑ T ∈ S.filter (fun T => e ∈ triEdges T ∧ ¬ 0 < c T), c T := by
      rw [show S.filter (fun T => e ∈ triEdges T ∧ ¬ 0 < c T) =
        S.filter (fun T => ¬ 0 < c T ∧ e ∈ triEdges T) from
          Finset.filter_congr (fun _ _ => and_comm), ← Finset.sum_neg_distrib]
      exact Finset.sum_congr rfl fun T hT => by
        rw [abs_of_nonpos (not_lt.1 (Finset.mem_filter.1 hT).2.1)]
    rw [h1, h2]; ring
  have hUb' : (Z ∪ O.biUnion Prod.fst).card + O.card * (2 * h - 2) +
      3 * O.card * (2 * h - 3) ≤ Ub := by
    rw [hOS]
    have := Nat.mul_le_mul_right (2 * h - 2) hOcard
    have := Nat.mul_le_mul_right (2 * h - 3) (Nat.mul_le_mul_left 3 hOcard)
    omega
  obtain ⟨A, hA, hAB, hAF, hAc, hAe⟩ := slot_absorber hα hH3 hH4 B d hdeg P O Prod.fst
    (fun o => 0 < c o.1) (fun o ho => hS _ (mem_coeffOcc.1 ho).1) (fun e => by convert hcert e)
    Z hPZ Ub hUb' hwin1 hwin2
  rw [hOS] at hAF hAc
  refine ⟨A, hA, hAB, hAF, hAc.trans ?_, hAe.trans (Nat.mul_le_mul_right _ hOcard)⟩
  have := Nat.mul_le_mul_right (2 * h - 2) hOcard
  have := Nat.mul_le_mul_right (2 * h - 3) (Nat.mul_le_mul_left 3 hOcard)
  omega

end TypedTriangle
