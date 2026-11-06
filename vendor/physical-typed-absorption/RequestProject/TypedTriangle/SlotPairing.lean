/-
Copyright (c) 2026 Juan Pablo Traverso Gianini.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import RequestProject.TypedTriangle.CompositeHinge

@[expose] public section

/-!
# A3 (parte 1) — Slots abiertos y fase de emparejamiento (S02 §4)

Un *slot* tiene una arista base `e` y un ápice privado `w`; su cuña es `W = {pw, qw}` si
`e = pq`, y `e ∪ W` es un triángulo permitido. Dada una familia de slots con signo que
satisface la identidad de conteo (4.1) de S02,

  `#{slots positivos en e} = #{slots negativos en e} + 1_P(e)`,

se empareja cada slot negativo con uno positivo de la misma base mediante bisagras
compuestas robustas (A2) frescas. El resultado `pairing_phase` produce un grafo `J` tal que
`J ∪ W(negativos)` y `J ∪ W(positivos) ∪ P` admiten descomposiciones permitidas.
-/

open Finset

noncomputable section
open Classical

namespace TypedTriangle

variable {V I : Type*} [Fintype V]

/-- `J` admite una descomposición permitida. -/
def Basal (H : Host V I) (F : Set (Multiset I)) (J : Finset (Sym2 V)) : Prop :=
  ∃ D, IsDecomposition H F J D

omit [Fintype V] in
lemma Basal.union {H : Host V I} {F : Set (Multiset I)} {J K : Finset (Sym2 V)}
    (hJ : Basal H F J) (hK : Basal H F K) (hd : Disjoint J K) : Basal H F (J ∪ K) := by
  obtain ⟨D, hD⟩ := hJ; obtain ⟨D', hD'⟩ := hK; exact ⟨_, hD.union hD' hd⟩

omit [Fintype V] in
lemma Basal.empty (H : Host V I) (F : Set (Multiset I)) : Basal H F ∅ :=
  ⟨∅, by simp, by simp, by simp⟩

omit [Fintype V] in
lemma Basal.congr {H : Host V I} {F : Set (Multiset I)} {J K : Finset (Sym2 V)}
    (hJ : Basal H F J) (h : J = K) : Basal H F K := h ▸ hJ

omit [Fintype V] in
lemma basal_triEdges {H : Host V I} {F : Set (Multiset I)} {T : Finset V}
    (hT : IsAllowed H F T) : Basal H F (triEdges T) :=
  ⟨{T}, by simp [hT], by simp, by simp⟩

omit [Fintype V] in
lemma basal_biUnion {H : Host V I} {F : Set (Multiset I)} {ι : Type*} (s : Finset ι)
    (J : ι → Finset (Sym2 V)) (hJ : ∀ i ∈ s, Basal H F (J i))
    (hdisj : (s : Set ι).PairwiseDisjoint J) : Basal H F (s.biUnion J) := by
  choose! D hD using hJ
  exact ⟨_, isDecomposition_biUnion s J D hD hdisj⟩

/-! ### Conjuntos de aristas dentro de / frescos respecto de un conjunto de vértices -/

/-- Todas las aristas de `X` tienen ambos extremos en `U`. -/
def Inside (U : Finset V) (X : Finset (Sym2 V)) : Prop := ∀ e ∈ X, ∀ w ∈ e, w ∈ U

/-- Toda arista de `Y` tiene un extremo fuera de `U`. -/
def Fresh (U : Finset V) (Y : Finset (Sym2 V)) : Prop := ∀ e ∈ Y, ∃ w ∈ e, w ∉ U

omit [Fintype V] in
lemma Inside.disjoint_fresh {U : Finset V} {X Y : Finset (Sym2 V)} (hX : Inside U X)
    (hY : Fresh U Y) : Disjoint X Y := by
  rw [Finset.disjoint_left]
  intro e heX heY
  obtain ⟨w, hw, hwU⟩ := hY e heY
  exact hwU (hX e heX w hw)

omit [Fintype V] in
lemma Inside.mono {U U' : Finset V} {X : Finset (Sym2 V)} (hX : Inside U X) (h : U ⊆ U') :
    Inside U' X := fun e he w hw => h (hX e he w hw)

omit [Fintype V] in
lemma Fresh.anti {U U' : Finset V} {Y : Finset (Sym2 V)} (hY : Fresh U' Y) (h : U ⊆ U') :
    Fresh U Y := fun e he => by
  obtain ⟨w, hw, hwU⟩ := hY e he; exact ⟨w, hw, fun h' => hwU (h h')⟩

omit [Fintype V] in
lemma Inside.union {U : Finset V} {X Y : Finset (Sym2 V)} (hX : Inside U X) (hY : Inside U Y) :
    Inside U (X ∪ Y) := fun e he => by
  rcases Finset.mem_union.1 he with h | h
  · exact hX e h
  · exact hY e h

omit [Fintype V] in
lemma Fresh.union {U : Finset V} {X Y : Finset (Sym2 V)} (hX : Fresh U X) (hY : Fresh U Y) :
    Fresh U (X ∪ Y) := fun e he => by
  rcases Finset.mem_union.1 he with h | h
  · exact hX e h
  · exact hY e h

omit [Fintype V] in
lemma Inside.subset {U : Finset V} {X Y : Finset (Sym2 V)} (hX : Inside U X) (h : Y ⊆ X) :
    Inside U Y := fun e he => hX e (h he)

omit [Fintype V] in
lemma Fresh.subset {U : Finset V} {X Y : Finset (Sym2 V)} (hX : Fresh U X) (h : Y ⊆ X) :
    Fresh U Y := fun e he => hX e (h he)

lemma inside_support (J : Finset (Sym2 V)) : Inside (support J) J :=
  fun _ he _ hw => mem_support_of_mem he hw

/-- Una bisagra sin la pareja `ab` y que evita `U` fuera de sus raíces es fresca respecto
de `U`. -/
lemma IsHinge.fresh {H : Host V I} {F : Set (Multiset I)} {u v a b : V} {J : Finset (Sym2 V)}
    (hJ : IsHinge H F u v a b J) (hab : s(a, b) ∉ J) (U : Finset V)
    (hU : ∀ z ∈ U, z ∈ support J → z ∈ ({u, v, a, b} : Finset V)) : Fresh U J := by
  intro e he
  induction e using Sym2.ind with
  | _ x y =>
  by_contra hcon
  push_neg at hcon
  have hx := hcon x (by simp)
  have hy := hcon y (by simp)
  have hxR := hU x hx (mem_support_of_mem he (by simp))
  have hyR := hU y hy (mem_support_of_mem he (by simp))
  exact hab (hJ.root_edge he hxR hyR ▸ he)

/-! ### Cuñas de slots -/

/-- Cuña de un slot de base `e` y ápice `w`: `{pw, qw}` si `e = pq`. -/
def wedgeOf (e : Sym2 V) (w : V) : Finset (Sym2 V) := e.toFinset.image (fun p => s(p, w))

omit [Fintype V] in
lemma wedgeOf_mk (p q w : V) : wedgeOf s(p, q) w = wedge p q w := by
  ext f
  simp [wedgeOf, wedge, Sym2.toFinset_mk_eq]

omit [Fintype V] in
lemma mem_wedgeOf {e f : Sym2 V} {w : V} : f ∈ wedgeOf e w ↔ ∃ p ∈ e, f = s(p, w) := by
  simp only [wedgeOf, Finset.mem_image, Sym2.mem_toFinset]
  constructor
  · rintro ⟨p, hp, rfl⟩; exact ⟨p, hp, rfl⟩
  · rintro ⟨p, hp, rfl⟩; exact ⟨p, hp, rfl⟩

/-- Triángulo cerrado por un slot. -/
def slotTri (e : Sym2 V) (w : V) : Finset V := insert w e.toFinset

omit [Fintype V] in
lemma slotTri_mk (p q w : V) : slotTri s(p, q) w = {p, q, w} := by
  ext x; simp [slotTri, Sym2.toFinset_mk_eq]; tauto

omit [Fintype V] in
lemma triEdges_slotTri {e : Sym2 V} {w : V} (he : ¬ e.IsDiag) (hw : w ∉ e) :
    triEdges (slotTri e w) = insert e (wedgeOf e w) := by
  induction e using Sym2.ind with
  | _ p q =>
  have hpq : p ≠ q := fun h => he (by simp [h])
  have hpw : p ≠ w := fun h => hw (by simp [h])
  have hqw : q ≠ w := fun h => hw (by simp [h])
  rw [slotTri_mk, wedgeOf_mk, triEdges_eq_insert_wedge hpq hpw hqw]

omit [Fintype V] in
lemma inside_wedgeOf {U : Finset V} {e : Sym2 V} {w : V} (he : ∀ p ∈ e, p ∈ U) (hw : w ∈ U) :
    Inside U (wedgeOf e w) := by
  intro f hf x hx
  obtain ⟨p, hp, rfl⟩ := mem_wedgeOf.1 hf
  rw [Sym2.mem_iff] at hx
  rcases hx with rfl | rfl
  · exact he _ hp
  · exact hw

omit [Fintype V] in
/-- Cuñas de dos slots con ápices distintos, cuyo segundo ápice no es extremo de la primera
base, son disjuntas. -/
lemma wedgeOf_disjoint {e e' : Sym2 V} {w w' : V} (hww' : w ≠ w') (hw' : w' ∉ e) : Disjoint (wedgeOf e w) (wedgeOf e' w') := by
  rw [Finset.disjoint_left]
  intro f hf hf'
  obtain ⟨p, hp, rfl⟩ := mem_wedgeOf.1 hf
  obtain ⟨p', hp', h⟩ := mem_wedgeOf.1 hf'
  rw [Sym2.eq_iff] at h
  rcases h with ⟨-, h⟩ | ⟨h1, h2⟩
  · exact hww' h
  · exact hw' (h1 ▸ hp)

omit [Fintype V] in
lemma not_mem_wedgeOf_of_not_mem {e f : Sym2 V} {w : V} (hw : w ∉ f) : f ∉ wedgeOf e w := by
  intro hf
  obtain ⟨p, -, rfl⟩ := mem_wedgeOf.1 hf
  exact hw (by simp)

omit [Fintype V] in
lemma Sym2.exists_mk_eq (e : Sym2 V) : ∃ u v, e = s(u, v) := by
  induction e using Sym2.ind with
  | _ u v => exact ⟨u, v, rfl⟩

/-! ### Fase de emparejamiento -/

section Pairing

variable {σ : Type*}

/-- Condiciones geométricas de una familia de slots respecto de un conjunto usado `U`. -/
structure SlotFamily (H : Host V I) (F : Set (Multiset I)) (base : σ → Sym2 V) (ap : σ → V)
    (Sl : Finset σ) (U : Finset V) (P : Finset (Sym2 V)) : Prop where
  tri : ∀ s ∈ Sl, ¬ (base s).IsDiag ∧ ap s ∉ base s ∧ IsAllowed H F (slotTri (base s) (ap s))
  inj : ∀ s ∈ Sl, ∀ s' ∈ Sl, ap s = ap s' → s = s'
  apex_base : ∀ s ∈ Sl, ∀ s' ∈ Sl, ap s ∉ base s'
  inside : ∀ s ∈ Sl, (∀ p ∈ base s, p ∈ U) ∧ ap s ∈ U
  insideP : Inside U P
  apexP : ∀ e ∈ P, ∀ s ∈ Sl, ap s ∉ e

omit [Fintype V] in
lemma SlotFamily.mono {H : Host V I} {F : Set (Multiset I)} {base : σ → Sym2 V} {ap : σ → V}
    {Sl Sl' : Finset σ} {U U' : Finset V} {P : Finset (Sym2 V)}
    (hS : SlotFamily H F base ap Sl U P) (hSl : Sl' ⊆ Sl) (hU : U ⊆ U') :
    SlotFamily H F base ap Sl' U' P where
  tri s hs := hS.tri s (hSl hs)
  inj s hs s' hs' := hS.inj s (hSl hs) s' (hSl hs')
  apex_base s hs s' hs' := hS.apex_base s (hSl hs) s' (hSl hs')
  inside s hs := ⟨fun p hp => hU ((hS.inside s (hSl hs)).1 p hp), hU (hS.inside s (hSl hs)).2⟩
  insideP := hS.insideP.mono hU
  apexP e he s hs := hS.apexP e he s (hSl hs)

omit [Fintype V] in
lemma SlotFamily.inside_wedges {H : Host V I} {F : Set (Multiset I)} {base : σ → Sym2 V}
    {ap : σ → V} {Sl : Finset σ} {U : Finset V} {P : Finset (Sym2 V)}
    (hS : SlotFamily H F base ap Sl U P) (Sl' : Finset σ) (hSl : Sl' ⊆ Sl) :
    Inside U (Sl'.biUnion fun s => wedgeOf (base s) (ap s)) := by
  intro f hf
  obtain ⟨s, hs, hf⟩ := Finset.mem_biUnion.1 hf
  exact inside_wedgeOf (hS.inside s (hSl hs)).1 (hS.inside s (hSl hs)).2 f hf

omit [Fintype V] in
lemma SlotFamily.wedge_disjoint {H : Host V I} {F : Set (Multiset I)} {base : σ → Sym2 V}
    {ap : σ → V} {Sl : Finset σ} {U : Finset V} {P : Finset (Sym2 V)}
    (hS : SlotFamily H F base ap Sl U P) {s s' : σ} (hs : s ∈ Sl) (hs' : s' ∈ Sl)
    (hne : s ≠ s') : Disjoint (wedgeOf (base s) (ap s)) (wedgeOf (base s') (ap s')) :=
  wedgeOf_disjoint (fun h => hne (hS.inj s hs s' hs' h)) (hS.apex_base s' hs' s hs)

omit [Fintype V] in
lemma SlotFamily.wedge_disjoint_biUnion {H : Host V I} {F : Set (Multiset I)}
    {base : σ → Sym2 V} {ap : σ → V} {Sl : Finset σ} {U : Finset V} {P : Finset (Sym2 V)}
    (hS : SlotFamily H F base ap Sl U P) {s : σ} (hs : s ∈ Sl) (Sl' : Finset σ)
    (hSl : Sl' ⊆ Sl) (hnot : s ∉ Sl') :
    Disjoint (wedgeOf (base s) (ap s)) (Sl'.biUnion fun s => wedgeOf (base s) (ap s)) := by
  rw [Finset.disjoint_biUnion_right]
  intro s' hs'
  exact hS.wedge_disjoint hs (hSl hs') (fun h => hnot (h ▸ hs'))

/-- Identidad de conteo (4.1) de S02 para una familia de slots con signo. -/
def SlotCount (base : σ → Sym2 V) (pos : σ → Prop) (Sl : Finset σ) (P : Finset (Sym2 V)) :
    Prop :=
  ∀ e, ((Sl.filter (fun s => pos s ∧ base s = e)).card : ℤ) =
    (Sl.filter (fun s => ¬ pos s ∧ base s = e)).card + if e ∈ P then 1 else 0

omit [Fintype V] in
/-- Caso base: sin slots negativos, las cuñas positivas junto con `P` se descomponen en los
triángulos cerrados por los slots positivos. -/
lemma basal_pos_slots {H : Host V I} {F : Set (Multiset I)} {base : σ → Sym2 V} {ap : σ → V}
    {pos : σ → Prop} {Sl : Finset σ} {U : Finset V} {P : Finset (Sym2 V)}
    (hS : SlotFamily H F base ap Sl U P) (hC : SlotCount base pos Sl P)
    (hneg : Sl.filter (fun s => ¬ pos s) = ∅) :
    Basal H F ((Sl.filter pos).biUnion (fun s => wedgeOf (base s) (ap s)) ∪ P) := by
  have hcount : ∀ e, ((Sl.filter (fun s => pos s ∧ base s = e)).card : ℤ) =
      if e ∈ P then 1 else 0 := by
    intro e
    have h0 : Sl.filter (fun s => ¬ pos s ∧ base s = e) = ∅ := by
      rw [Finset.eq_empty_iff_forall_notMem]
      intro s hs
      rw [Finset.mem_filter] at hs
      have : s ∈ Sl.filter (fun s => ¬ pos s) := Finset.mem_filter.2 ⟨hs.1, hs.2.1⟩
      rw [hneg] at this; simp at this
    rw [hC e, h0]; simp
  have heq : (Sl.filter pos).biUnion (fun s => wedgeOf (base s) (ap s)) ∪ P =
      (Sl.filter pos).biUnion (fun s => triEdges (slotTri (base s) (ap s))) := by
    ext f
    simp only [Finset.mem_union, Finset.mem_biUnion, Finset.mem_filter]
    constructor
    · rintro (⟨s, ⟨hs, hp⟩, hf⟩ | hf)
      · refine ⟨s, ⟨hs, hp⟩, ?_⟩
        rw [triEdges_slotTri (hS.tri s hs).1 (hS.tri s hs).2.1]
        exact Finset.mem_insert_of_mem hf
      · have h1 := hcount f
        rw [if_pos hf] at h1
        obtain ⟨s, hs⟩ : (Sl.filter (fun s => pos s ∧ base s = f)).Nonempty := by
          rw [← Finset.card_pos]; omega
        rw [Finset.mem_filter] at hs
        refine ⟨s, ⟨hs.1, hs.2.1⟩, ?_⟩
        rw [triEdges_slotTri (hS.tri s hs.1).1 (hS.tri s hs.1).2.1, hs.2.2]
        exact Finset.mem_insert_self _ _
    · rintro ⟨s, ⟨hs, hp⟩, hf⟩
      rw [triEdges_slotTri (hS.tri s hs).1 (hS.tri s hs).2.1, Finset.mem_insert] at hf
      rcases hf with rfl | hf
      · right
        by_contra hnot
        have h1 := hcount (base s)
        rw [if_neg hnot] at h1
        have : s ∈ Sl.filter (fun s' => pos s' ∧ base s' = base s) :=
          Finset.mem_filter.2 ⟨hs, hp, rfl⟩
        have := Finset.card_pos.2 ⟨s, this⟩
        omega
      · exact Or.inl ⟨s, ⟨hs, hp⟩, hf⟩
  rw [heq]
  refine basal_biUnion _ _ (fun s hs => basal_triEdges (hS.tri s (Finset.mem_filter.1 hs).1).2.2)
    ?_
  intro s hs s' hs' hne
  simp only [Finset.coe_filter, Set.mem_setOf_eq] at hs hs'
  simp only [Function.onFun]
  rw [triEdges_slotTri (hS.tri s hs.1).1 (hS.tri s hs.1).2.1,
    triEdges_slotTri (hS.tri s' hs'.1).1 (hS.tri s' hs'.1).2.1]
  have hbase : base s ≠ base s' := by
    intro hb
    have h1 := hcount (base s)
    have hsub : ({s, s'} : Finset σ) ⊆ Sl.filter (fun t => pos t ∧ base t = base s) := by
      intro t ht
      simp only [Finset.mem_insert, Finset.mem_singleton] at ht
      rcases ht with rfl | rfl
      · exact Finset.mem_filter.2 ⟨hs.1, hs.2, rfl⟩
      · exact Finset.mem_filter.2 ⟨hs'.1, hs'.2, hb.symm⟩
    have h2 := Finset.card_le_card hsub
    rw [Finset.card_pair hne] at h2
    split_ifs at h1 <;> omega
  rw [Finset.disjoint_insert_left, Finset.disjoint_insert_right]
  refine ⟨?_, not_mem_wedgeOf_of_not_mem (hS.apex_base s hs.1 s' hs'.1),
    hS.wedge_disjoint hs.1 hs'.1 hne⟩
  rw [Finset.mem_insert, not_or]
  exact ⟨hbase, not_mem_wedgeOf_of_not_mem (hS.apex_base s' hs'.1 s hs.1)⟩

omit [Fintype V] in
lemma filter_erase_erase_card {Sl : Finset σ} {p : σ → Prop} [DecidablePred p] {s₁ s₂ : σ}
    (h12 : s₁ ≠ s₂) :
    (((Sl.erase s₁).erase s₂).filter p).card + (if s₁ ∈ Sl ∧ p s₁ then 1 else 0) +
      (if s₂ ∈ Sl ∧ p s₂ then 1 else 0) = (Sl.filter p).card := by
  rw [Finset.filter_erase, Finset.filter_erase]
  by_cases h1 : s₁ ∈ Sl ∧ p s₁ <;> by_cases h2 : s₂ ∈ Sl ∧ p s₂
  · have hm1 : s₁ ∈ Sl.filter p := Finset.mem_filter.2 h1
    have hm2 : s₂ ∈ (Sl.filter p).erase s₁ := Finset.mem_erase.2 ⟨Ne.symm h12,
      Finset.mem_filter.2 h2⟩
    rw [if_pos h1, if_pos h2, Finset.card_erase_of_mem hm2, Finset.card_erase_of_mem hm1]
    have := Finset.card_pos.2 ⟨_, hm1⟩
    have := Finset.card_pos.2 ⟨_, hm2⟩
    rw [Finset.card_erase_of_mem hm1] at this
    omega
  · have hm1 : s₁ ∈ Sl.filter p := Finset.mem_filter.2 h1
    have hm2 : s₂ ∉ (Sl.filter p).erase s₁ := fun h =>
      h2 (Finset.mem_filter.1 (Finset.mem_of_mem_erase h))
    rw [if_pos h1, if_neg h2, Finset.erase_eq_of_notMem hm2, Finset.card_erase_of_mem hm1]
    have := Finset.card_pos.2 ⟨_, hm1⟩
    omega
  · have hm1 : s₁ ∉ Sl.filter p := fun h => h1 (Finset.mem_filter.1 h)
    have hm2 : s₂ ∈ Sl.filter p := Finset.mem_filter.2 h2
    rw [if_neg h1, if_pos h2, Finset.erase_eq_of_notMem hm1, Finset.card_erase_of_mem hm2]
    have := Finset.card_pos.2 ⟨_, hm2⟩
    omega
  · have hm1 : s₁ ∉ Sl.filter p := fun h => h1 (Finset.mem_filter.1 h)
    have hm2 : s₂ ∉ Sl.filter p := fun h => h2 (Finset.mem_filter.1 h)
    rw [if_neg h1, if_neg h2, Finset.erase_eq_of_notMem hm1, Finset.erase_eq_of_notMem hm2]
    simp

/-- Cota de aristas por el soporte: `|J| ≤ C(|V(J)| + 1, 2)`. -/
lemma card_le_choose_support (J : Finset (Sym2 V)) :
    J.card ≤ ((support J).card + 1).choose 2 := by
  rw [← Finset.card_sym2]
  refine Finset.card_le_card fun e he => ?_
  induction e using Sym2.ind with
  | _ x y =>
    rw [Finset.mk_mem_sym2_iff]
    exact ⟨mem_support_of_mem he (by simp), mem_support_of_mem he (by simp)⟩

/-- Versión con cota `m` del soporte. -/
lemma card_le_choose_of_support_le {J : Finset (Sym2 V)} {m : ℕ} (hm : (support J).card ≤ m) :
    J.card ≤ (m + 1).choose 2 :=
  (card_le_choose_support J).trans (Nat.choose_le_choose 2 (by omega))

/-- **Fase de emparejamiento (S02 §4).** Si una familia de slots cumple la identidad de
conteo (4.1), las condiciones geométricas `SlotFamily` respecto de `U`, y tiene a lo sumo `N`
slots negativos, entonces bajo las ventanas existe `J` fresco respecto de `U`, disjunto de
`B`, con `J ∪ W(negativos)` y `J ∪ W(positivos) ∪ P` basales, y que añade a lo sumo
`N (2h − 3)` vértices. -/
theorem pairing_phase {H : Host V I} {F : Set (Multiset I)} {α : ℝ} {h : ℕ}
    (hα : 0 < α) (hH3 : CommonNbrCond H F α) (hH4 : HingeCond H F α h)
    (B : Finset (Sym2 V)) (d : ℕ) (hdeg : ∀ x, degIn B x ≤ d) (P : Finset (Sym2 V))
    (base : σ → Sym2 V) (ap : σ → V) (pos : σ → Prop) (Ub : ℕ)
    (hwin1 : (Ub : ℝ) + 2 + 4 * d < α * Fintype.card V)
    (hwin2 : ((Ub : ℝ) + h + 5 * d) * 2 ^ Nat.choose h 2 ≤ α / 2 * Fintype.card V) :
    ∀ (N : ℕ) (Sl : Finset σ) (U : Finset V),
      (Sl.filter (fun s => ¬ pos s)).card ≤ N → U.card + N * (2 * h - 3) ≤ Ub →
      SlotFamily H F base ap Sl U P → SlotCount base pos Sl P →
      ∃ J, Basal H F (J ∪ (Sl.filter (fun s => ¬ pos s)).biUnion
          (fun s => wedgeOf (base s) (ap s))) ∧
        Basal H F (J ∪ (Sl.filter pos).biUnion (fun s => wedgeOf (base s) (ap s)) ∪ P) ∧
        Disjoint J B ∧ Fresh U J ∧ (U ∪ support J).card ≤ U.card + N * (2 * h - 3) ∧
        J.card ≤ N * (2 * h - 2).choose 2 := by
  intro N
  induction N with
  | zero =>
    intro Sl U hN _ hS hC
    have hneg : Sl.filter (fun s => ¬ pos s) = ∅ := Finset.card_eq_zero.1 (by omega)
    refine ⟨∅, ?_, ?_, by simp, fun e he => by simp at he, by simp [support], by simp⟩
    · rw [hneg]; simpa using Basal.empty H F
    · simpa using basal_pos_slots hS hC hneg
  | succ N ih =>
    intro Sl U hN hU hS hC
    by_cases hneg : Sl.filter (fun s => ¬ pos s) = ∅
    · refine ⟨∅, ?_, ?_, by simp, fun e he => by simp at he, by simp [support], by simp⟩
      · rw [hneg]; simpa using Basal.empty H F
      · simpa using basal_pos_slots hS hC hneg
    obtain ⟨sn, hsn⟩ := Finset.nonempty_iff_ne_empty.2 hneg
    rw [Finset.mem_filter] at hsn
    -- un slot positivo con la misma base
    obtain ⟨sp, hsp⟩ : (Sl.filter (fun s => pos s ∧ base s = base sn)).Nonempty := by
      rw [← Finset.card_pos]
      have h1 := hC (base sn)
      have h2 : 0 < (Sl.filter (fun s => ¬ pos s ∧ base s = base sn)).card :=
        Finset.card_pos.2 ⟨sn, Finset.mem_filter.2 ⟨hsn.1, hsn.2, rfl⟩⟩
      split_ifs at h1 <;> omega
    rw [Finset.mem_filter] at hsp
    obtain ⟨hspS, hspp, hspb⟩ := hsp
    have hne : sn ≠ sp := fun h' => hsn.2 (h' ▸ hspp)
    obtain ⟨u, v, he⟩ := Sym2.exists_mk_eq (base sn)
    have hTn := (hS.tri sn hsn.1).2.2
    have hTp := (hS.tri sp hspS).2.2
    rw [he, slotTri_mk] at hTn
    rw [hspb, he, slotTri_mk] at hTp
    have hab : ap sn ≠ ap sp := fun h' => hne (hS.inj sn hsn.1 sp hspS h')
    have hUb : (U.card : ℝ) ≤ Ub := by
      have : U.card ≤ Ub := by nlinarith
      exact_mod_cast this
    obtain ⟨J₀, hJ₀, hJ₀B, hJ₀ab, hJ₀U, hJ₀c⟩ := exists_robust_composite_hinge hα hH3 hH4 hab
      hTn hTp U B d hdeg (by linarith)
      (le_trans (mul_le_mul_of_nonneg_right (by linarith) (by positivity)) hwin2)
    set Sl' := (Sl.erase sn).erase sp
    set U' := U ∪ support J₀
    have hSl'sub : Sl' ⊆ Sl := (Finset.erase_subset _ _).trans (Finset.erase_subset _ _)
    have hsnSl' : sn ∉ Sl' := fun h' => by
      simp [Sl'] at h'
    have hspSl' : sp ∉ Sl' := fun h' => by simp [Sl'] at h'
    have hU'c : U'.card ≤ U.card + (2 * h - 3) :=
      (Finset.card_union_le _ _).trans (Nat.add_le_add_left hJ₀c _)
    have hS' : SlotFamily H F base ap Sl' U' P := hS.mono hSl'sub Finset.subset_union_left
    have hC' : SlotCount base pos Sl' P := by
      intro e
      have h1 := filter_erase_erase_card (Sl := Sl) (p := fun s => pos s ∧ base s = e) hne
      have h2 := filter_erase_erase_card (Sl := Sl) (p := fun s => ¬ pos s ∧ base s = e) hne
      have h3 := hC e
      by_cases hb : base sn = e
      · rw [if_neg (fun h' => hsn.2 h'.2.1), if_pos ⟨hspS, hspp, hspb.trans hb⟩] at h1
        rw [if_pos ⟨hsn.1, hsn.2, hb⟩, if_neg (fun h' => h'.2.1 hspp)] at h2
        simp only [Sl']
        split_ifs at h3 ⊢ <;> omega
      · have hb' : base sp ≠ e := hspb ▸ hb
        rw [if_neg (fun h' => hb h'.2.2), if_neg (fun h' => hb' h'.2.2)] at h1
        rw [if_neg (fun h' => hb h'.2.2), if_neg (fun h' => hb' h'.2.2)] at h2
        simp only [Sl']
        split_ifs at h3 ⊢ <;> omega
    have hN' : (Sl'.filter (fun s => ¬ pos s)).card ≤ N := by
      have h1 := filter_erase_erase_card (Sl := Sl) (p := fun s => ¬ pos s) hne
      rw [if_pos ⟨hsn.1, hsn.2⟩, if_neg (fun h' => h'.2 hspp)] at h1
      simp only [Sl']; omega
    have hU' : U'.card + N * (2 * h - 3) ≤ Ub := by
      have : U.card + (N + 1) * (2 * h - 3) = U.card + (2 * h - 3) + N * (2 * h - 3) := by ring
      omega
    obtain ⟨J', hJ'neg, hJ'pos, hJ'B, hJ'U, hJ'c, hJ'e⟩ := ih Sl' U' hN' hU' hS' hC'
    have hJ₀e : J₀.card ≤ (2 * h - 2).choose 2 := by
      have h6 : 6 ≤ h := by
        obtain ⟨i, hi6, hih, -⟩ := hH4 u v (ap sn) (ap sp) hab hTn hTp
        omega
      have := card_le_choose_of_support_le hJ₀c
      rwa [show 2 * h - 3 + 1 = 2 * h - 2 by omega] at this
    -- piezas
    have hJ₀fresh : Fresh U J₀ := hJ₀.fresh hJ₀ab U hJ₀U
    have hJ₀in : Inside U' J₀ := (inside_support J₀).mono Finset.subset_union_right
    have hWn : wedgeOf (base sn) (ap sn) = wedge u v (ap sn) := by rw [he, wedgeOf_mk]
    have hWp : wedgeOf (base sp) (ap sp) = wedge u v (ap sp) := by rw [hspb, he, wedgeOf_mk]
    have hWnin : Inside U (wedgeOf (base sn) (ap sn)) :=
      inside_wedgeOf (hS.inside sn hsn.1).1 (hS.inside sn hsn.1).2
    have hWpin : Inside U (wedgeOf (base sp) (ap sp)) :=
      inside_wedgeOf (hS.inside sp hspS).1 (hS.inside sp hspS).2
    have hnegeq : Sl.filter (fun s => ¬ pos s) = insert sn (Sl'.filter (fun s => ¬ pos s)) := by
      ext s
      simp only [Finset.mem_filter, Finset.mem_insert, Sl', Finset.mem_erase]
      constructor
      · rintro ⟨hs, hps⟩
        by_cases h1 : s = sn
        · exact Or.inl h1
        · exact Or.inr ⟨⟨fun h2 => hps (h2 ▸ hspp), h1, hs⟩, hps⟩
      · rintro (rfl | ⟨⟨-, -, hs⟩, hps⟩)
        · exact ⟨hsn.1, hsn.2⟩
        · exact ⟨hs, hps⟩
    have hposeq : Sl.filter pos = insert sp (Sl'.filter pos) := by
      ext s
      simp only [Finset.mem_filter, Finset.mem_insert, Sl', Finset.mem_erase]
      constructor
      · rintro ⟨hs, hps⟩
        by_cases h1 : s = sp
        · exact Or.inl h1
        · exact Or.inr ⟨⟨h1, fun h2 => hsn.2 (h2 ▸ hps), hs⟩, hps⟩
      · rintro (rfl | ⟨⟨-, -, hs⟩, hps⟩)
        · exact ⟨hspS, hspp⟩
        · exact ⟨hs, hps⟩
    have hnegsub : Sl'.filter (fun s => ¬ pos s) ⊆ Sl := (Finset.filter_subset _ _).trans hSl'sub
    have hpossub : Sl'.filter pos ⊆ Sl := (Finset.filter_subset _ _).trans hSl'sub
    refine ⟨J₀ ∪ J', ?_, ?_, Finset.disjoint_union_left.2 ⟨hJ₀B, hJ'B⟩,
      hJ₀fresh.union (hJ'U.anti Finset.subset_union_left), ?_, ?_⟩
    · rw [hnegeq, Finset.biUnion_insert]
      have heq : J₀ ∪ J' ∪ (wedgeOf (base sn) (ap sn) ∪
          (Sl'.filter (fun s => ¬ pos s)).biUnion (fun s => wedgeOf (base s) (ap s))) =
          (J₀ ∪ wedgeOf (base sn) (ap sn)) ∪
          (J' ∪ (Sl'.filter (fun s => ¬ pos s)).biUnion (fun s => wedgeOf (base s) (ap s))) := by
        ext; simp only [Finset.mem_union]; tauto
      rw [heq]
      refine Basal.union (by rw [hWn]; exact hJ₀.2.2.1) hJ'neg ?_
      refine Finset.disjoint_union_left.2 ⟨Finset.disjoint_union_right.2 ⟨?_, ?_⟩,
        Finset.disjoint_union_right.2 ⟨?_, ?_⟩⟩
      · exact hJ₀in.disjoint_fresh hJ'U
      · exact ((hS.inside_wedges _ hnegsub).disjoint_fresh hJ₀fresh).symm
      · exact (hWnin.mono Finset.subset_union_left).disjoint_fresh hJ'U
      · exact hS.wedge_disjoint_biUnion hsn.1 _ hnegsub (fun h' => hsnSl'
          (Finset.mem_filter.1 h').1)
    · rw [hposeq, Finset.biUnion_insert]
      have heq : J₀ ∪ J' ∪ (wedgeOf (base sp) (ap sp) ∪
          (Sl'.filter pos).biUnion (fun s => wedgeOf (base s) (ap s))) ∪ P =
          (J₀ ∪ wedgeOf (base sp) (ap sp)) ∪
          (J' ∪ (Sl'.filter pos).biUnion (fun s => wedgeOf (base s) (ap s)) ∪ P) := by
        ext; simp only [Finset.mem_union]; tauto
      rw [heq]
      refine Basal.union (by rw [hWp]; exact hJ₀.2.2.2) hJ'pos ?_
      refine Finset.disjoint_union_left.2 ⟨Finset.disjoint_union_right.2
        ⟨Finset.disjoint_union_right.2 ⟨?_, ?_⟩, ?_⟩, Finset.disjoint_union_right.2
        ⟨Finset.disjoint_union_right.2 ⟨?_, ?_⟩, ?_⟩⟩
      · exact hJ₀in.disjoint_fresh hJ'U
      · exact ((hS.inside_wedges _ hpossub).disjoint_fresh hJ₀fresh).symm
      · exact (hS.insideP.disjoint_fresh hJ₀fresh).symm
      · exact (hWpin.mono Finset.subset_union_left).disjoint_fresh hJ'U
      · exact hS.wedge_disjoint_biUnion hspS _ hpossub (fun h' => hspSl'
          (Finset.mem_filter.1 h').1)
      · rw [Finset.disjoint_right]
        intro f hf
        exact not_mem_wedgeOf_of_not_mem (hS.apexP f hf sp hspS)
    · have heq : U ∪ support (J₀ ∪ J') = U' ∪ support J' := by
        rw [support_union]; simp only [U', Finset.union_assoc]
      rw [heq]
      have : U.card + (N + 1) * (2 * h - 3) = U.card + (2 * h - 3) + N * (2 * h - 3) := by ring
      omega
    · refine (Finset.card_union_le _ _).trans ?_
      rw [Nat.succ_mul]
      omega

end Pairing

end TypedTriangle
