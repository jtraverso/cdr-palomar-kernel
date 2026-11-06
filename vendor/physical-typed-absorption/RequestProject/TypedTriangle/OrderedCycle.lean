/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import RequestProject.TypedTriangle.CirculationDecomp

@[expose] public section

/-!
# Orden cíclico de un ciclo simple (V12, Prioridad 1)

`Circulation.IsSimpleCycle src tgt C` describe un ciclo como *conjunto* de arcos. El zigzag de
S26 necesita un *orden cíclico*. Aquí se construye, sin premisas adicionales:

* `IsSimpleCycle.next` — el arco siguiente: el único `b ∈ C` con `src b = tgt a`
  (existe por `balanced`, es único por `src_inj`); es inyectivo por `tgt_inj`.
* `IsSimpleCycle.exists_cyclicOrder` — una enumeración `e : Fin C.card ≃ {a // a ∈ C}`,
  que empieza en un arco prescrito, con `tgt (e i) = src (e ((i+1) mod C.card))`.
  La minimalidad fuerza que la órbita de `next` sea todo `C` (una sola órbita).
* consecuencias: orígenes distintos (`src ∘ e` inyectiva), conservación exacta de las
  ocurrencias por vértice y por raíz, forma de lista (`exists_cyclicList`), y los casos
  `C.card = 1` (lazo `tgt a = src a`) y `C.card = 2` (dígono) explícitos.
* recíproco (`isSimpleCycle_of_cyclicOrder`): una enumeración cíclica con orígenes
  inyectivos define un `IsSimpleCycle`; así la formulación ordenada es equivalente.

Todo vale para un multigrafo dirigido arbitrario (incluidos lazos y arcos paralelos).
-/

open Finset Classical

noncomputable section

namespace TypedTriangle.Circulation

variable {V E : Type*} {src tgt : E → V} {C : Finset E}

namespace IsSimpleCycle

/-- Existencia y unicidad del arco siguiente. -/
lemma existsUnique_next (hC : IsSimpleCycle src tgt C) (a : E) (ha : a ∈ C) :
    ∃! b, b ∈ C ∧ src b = tgt a := by
  have : tgt a ∈ C.image src := hC.balanced ▸ Finset.mem_image_of_mem tgt ha
  obtain ⟨b, hb, hba⟩ := Finset.mem_image.mp this
  exact ⟨b, ⟨hb, hba⟩, fun c hc => hC.src_inj hc.1 hb (hc.2.trans hba.symm)⟩

/-- El arco siguiente de un arco del ciclo. -/
def next (hC : IsSimpleCycle src tgt C) (a : {a // a ∈ C}) : {a // a ∈ C} :=
  ⟨Classical.choose (hC.existsUnique_next a.1 a.2).exists,
    (Classical.choose_spec (hC.existsUnique_next a.1 a.2).exists).1⟩

lemma src_next (hC : IsSimpleCycle src tgt C) (a : {a // a ∈ C}) :
    src (hC.next a).1 = tgt a.1 :=
  (Classical.choose_spec (hC.existsUnique_next a.1 a.2).exists).2

lemma next_injective (hC : IsSimpleCycle src tgt C) : Function.Injective hC.next := by
  intro a b hab
  apply Subtype.ext
  apply hC.tgt_inj a.2 b.2
  rw [← hC.src_next a, ← hC.src_next b, hab]

/-- Un arco siguiente iterado conecta: `src (next^[k+1] a) = tgt (next^[k] a)`. -/
lemma src_iterate_succ (hC : IsSimpleCycle src tgt C) (a : {a // a ∈ C}) (k : ℕ) :
    src (hC.next^[k + 1] a).1 = tgt (hC.next^[k] a).1 := by
  rw [Function.iterate_succ_apply', hC.src_next]

/-- La órbita de `next` por `a₀`, como conjunto de arcos. -/
def orbit (hC : IsSimpleCycle src tgt C) (a₀ : {a // a ∈ C}) : Finset E :=
  (range (Function.minimalPeriod hC.next a₀)).image (fun k => (hC.next^[k] a₀).1)

lemma minimalPeriod_pos (hC : IsSimpleCycle src tgt C) (a₀ : {a // a ∈ C}) :
    0 < Function.minimalPeriod hC.next a₀ := by
  haveI : Finite {a // a ∈ C} := inferInstance
  exact Function.minimalPeriod_pos_of_mem_periodicPts
    (Function.Injective.mem_periodicPts hC.next_injective a₀)

/-- La órbita es balanceada, luego (minimalidad) es todo el ciclo. -/
lemma orbit_eq (hC : IsSimpleCycle src tgt C) (a₀ : {a // a ∈ C}) : hC.orbit a₀ = C := by
  set f := hC.next
  set p := Function.minimalPeriod f a₀
  have hp : 0 < p := hC.minimalPeriod_pos a₀
  apply hC.minimal
  · intro b hb
    obtain ⟨k, -, rfl⟩ := Finset.mem_image.mp hb
    exact (f^[k] a₀).2
  · exact ⟨_, Finset.mem_image_of_mem _ (Finset.mem_range.mpr hp)⟩
  · ext v
    simp only [orbit, Finset.mem_image, Finset.mem_range]
    constructor
    · rintro ⟨_, ⟨k, hk, rfl⟩, rfl⟩
      refine ⟨_, ⟨(k + p - 1) % p, Nat.mod_lt _ hp, rfl⟩, ?_⟩
      show tgt (f^[(k + p - 1) % p] a₀).1 = src (f^[k] a₀).1
      rw [Function.iterate_mod_minimalPeriod_eq, ← hC.src_iterate_succ,
        Nat.sub_add_cancel (by omega), Function.iterate_add_apply,
        Function.iterate_minimalPeriod]
    · rintro ⟨_, ⟨k, hk, rfl⟩, rfl⟩
      refine ⟨_, ⟨(k + 1) % p, Nat.mod_lt _ hp, rfl⟩, ?_⟩
      show src (f^[(k + 1) % p] a₀).1 = tgt (f^[k] a₀).1
      rw [Function.iterate_mod_minimalPeriod_eq, hC.src_iterate_succ]

/-- El período de cualquier arco bajo `next` es la longitud del ciclo. -/
lemma minimalPeriod_eq_card (hC : IsSimpleCycle src tgt C) (a₀ : {a // a ∈ C}) :
    Function.minimalPeriod hC.next a₀ = C.card := by
  conv_rhs => rw [← hC.orbit_eq a₀]
  rw [orbit, Finset.card_image_of_injOn, Finset.card_range]
  intro i hi j hj hij
  exact Function.iterate_injOn_Iio_minimalPeriod (Finset.mem_range.mp hi)
    (Finset.mem_range.mp hj) (Subtype.ext hij)

/-- Índice cíclico siguiente `(i+1) mod n`. -/
def succMod {n : ℕ} (i : Fin n) : Fin n := ⟨(i.1 + 1) % n, Nat.mod_lt _ i.pos⟩

/-- **Orden cíclico de un ciclo simple.** Existe una enumeración biyectiva
`e : Fin C.card ≃ {a // a ∈ C}` que empieza en cualquier arco prescrito `a₀` y en la que el
destino de cada arco es el origen del siguiente, cíclicamente. -/
theorem exists_cyclicOrder (hC : IsSimpleCycle src tgt C) (a₀ : {a // a ∈ C}) :
    ∃ e : Fin C.card ≃ {a // a ∈ C},
      e ⟨0, Finset.card_pos.mpr hC.nonempty⟩ = a₀ ∧
      ∀ i : Fin C.card, tgt (e i).1 = src (e (succMod i)).1 := by
  set f := hC.next
  have hpc := hC.minimalPeriod_eq_card a₀
  let g : Fin C.card → {a // a ∈ C} := fun i => f^[i.1] a₀
  have ginj : Function.Injective g := by
    intro i j hij
    apply Fin.ext
    have := @Function.iterate_injOn_Iio_minimalPeriod _ f a₀
    exact this (show i.1 < _ by rw [hpc]; exact i.2) (show j.1 < _ by rw [hpc]; exact j.2) hij
  have gbij : Function.Bijective g :=
    (Fintype.bijective_iff_injective_and_card g).mpr ⟨ginj, by simp⟩
  refine ⟨Equiv.ofBijective g gbij, rfl, fun i => ?_⟩
  show tgt (f^[i.1] a₀).1 = src (f^[(i.1 + 1) % C.card] a₀).1
  have hmod := @Function.iterate_mod_minimalPeriod_eq _ f a₀ (i.1 + 1)
  rw [hpc] at hmod
  rw [hmod, hC.src_iterate_succ]

end IsSimpleCycle

open IsSimpleCycle

/-! ### Consecuencias de un orden cíclico -/

section Consequences

variable {e : Fin C.card ≃ {a // a ∈ C}}

/-- Los orígenes de una enumeración de un ciclo simple son distintos. -/
lemma src_enum_injective (hC : IsSimpleCycle src tgt C) (e : Fin C.card ≃ {a // a ∈ C}) :
    Function.Injective (fun i => src (e i).1) := by
  intro i j hij
  exact e.injective (Subtype.ext (hC.src_inj (e i).2 (e j).2 hij))

/-- Una enumeración conserva el número de arcos que satisfacen cualquier predicado. -/
lemma card_filter_enum (e : Fin C.card ≃ {a // a ∈ C}) (P : E → Prop) :
    (univ.filter (fun i => P (e i).1)).card = (C.filter P).card := by
  refine Finset.card_bij (fun i _ => (e i).1) ?_ ?_ ?_
  · intro i hi
    exact Finset.mem_filter.mpr ⟨(e i).2, (Finset.mem_filter.mp hi).2⟩
  · intro i _ j _ hij
    exact e.injective (Subtype.ext hij)
  · intro b hb
    obtain ⟨hbC, hPb⟩ := Finset.mem_filter.mp hb
    exact ⟨e.symm ⟨b, hbC⟩, Finset.mem_filter.mpr ⟨Finset.mem_univ _, by simpa using hPb⟩,
      by simp⟩

/-- **Ocurrencias por vértice conservadas**: el número de posiciones cuyo estado de origen
es `v` coincide con el de arcos de `C` que salen de `v` (y es `≤ 1`). -/
lemma card_src_enum (e : Fin C.card ≃ {a // a ∈ C}) (v : V) :
    (univ.filter (fun i => src (e i).1 = v)).card = (C.filter (fun a => src a = v)).card := by
  convert card_filter_enum e (fun a => src a = v)

/-- **Ocurrencias por raíz conservadas** para cualquier asignación de raíces `ρ`. -/
lemma card_root_enum {R : Type*} (ρ : V → R) (e : Fin C.card ≃ {a // a ∈ C}) (r : R) :
    (univ.filter (fun i => ρ (src (e i).1) = r)).card =
      (C.filter (fun a => ρ (src a) = r)).card := by
  convert card_filter_enum e (fun a => ρ (src a) = r)

end Consequences

/-- **Forma de lista** (la usada por la triangulación): una lista sin repeticiones de los
arcos de `C`, de longitud `C.card`, con `tgt l[i] = src l[(i+1) mod |l|]`, empezando en
cualquier arco prescrito, y con orígenes distintos. -/
theorem IsSimpleCycle.exists_cyclicList (hC : IsSimpleCycle src tgt C) (a₀ : E) (ha₀ : a₀ ∈ C) :
    ∃ l : List E, l.Nodup ∧ l.toFinset = C ∧ l.length = C.card ∧ l.head? = some a₀ ∧
      (l.map src).Nodup ∧
      ∀ (i : ℕ) (hi : i < l.length),
        tgt l[i] = src (l[(i + 1) % l.length]'(Nat.mod_lt _ (by omega))) := by
  obtain ⟨e, he0, he⟩ := hC.exists_cyclicOrder ⟨a₀, ha₀⟩
  have hpos : 0 < C.card := Finset.card_pos.mpr hC.nonempty
  refine ⟨List.ofFn (fun i => (e i).1), ?_, ?_, by simp, ?_, ?_, ?_⟩
  · rw [List.nodup_ofFn]
    intro i j hij
    exact e.injective (Subtype.ext hij)
  · ext b
    simp only [List.mem_toFinset, List.mem_ofFn]
    constructor
    · rintro ⟨i, rfl⟩
      exact (e i).2
    · intro hb
      exact ⟨e.symm ⟨b, hb⟩, by simp⟩
  · obtain ⟨n, hn⟩ : ∃ n, C.card = n + 1 := ⟨C.card - 1, by omega⟩
    rw [List.head?_eq_getElem?]
    simp only [List.getElem?_ofFn]
    rw [dif_pos hpos]
    exact congrArg (fun a => some a.1) he0
  · rw [List.map_ofFn, List.nodup_ofFn]
    exact src_enum_injective hC e
  · intro i hi
    simp only [List.length_ofFn] at hi ⊢
    simp only [List.getElem_ofFn]
    exact he ⟨i, hi⟩

/-- **Caso `C.card = 1`**: un ciclo simple de un solo arco es un lazo. -/
theorem IsSimpleCycle.card_eq_one (hC : IsSimpleCycle src tgt C) (h1 : C.card = 1) :
    ∃ a, C = {a} ∧ tgt a = src a := by
  obtain ⟨a, rfl⟩ := Finset.card_eq_one.mp h1
  refine ⟨a, rfl, ?_⟩
  have := hC.balanced
  simp only [Finset.image_singleton, Finset.singleton_inj] at this
  exact this.symm

/-- **Caso `C.card = 2`**: un ciclo simple de dos arcos es un dígono `a : u → w`,
`b : w → u` con `a ≠ b` (en el grafo de estados de una cubierta, `u ≠ w`). -/
theorem IsSimpleCycle.card_eq_two (hC : IsSimpleCycle src tgt C) (h2 : C.card = 2) :
    ∃ a b, a ≠ b ∧ C = {a, b} ∧ tgt a = src b ∧ tgt b = src a ∧ src a ≠ src b := by
  obtain ⟨a, ha⟩ := hC.nonempty
  obtain ⟨e, he0, he⟩ := hC.exists_cyclicOrder ⟨a, ha⟩
  let i0 : Fin C.card := ⟨0, by omega⟩
  let i1 : Fin C.card := ⟨1, by omega⟩
  have h01 : i0 ≠ i1 := by simp [i0, i1, Fin.ext_iff]
  have hs0 : succMod i0 = i1 := by ext; simp [succMod, i0, i1, h2]
  have hs1 : succMod i1 = i0 := by ext; simp [succMod, i0, i1, h2]
  have hne : (e i0).1 ≠ (e i1).1 := fun h => h01 (e.injective (Subtype.ext h))
  refine ⟨(e i0).1, (e i1).1, hne, ?_, ?_, ?_, ?_⟩
  · apply (Finset.eq_of_subset_of_card_le _ _).symm
    · intro x hx
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl
      · exact (e i0).2
      · exact (e i1).2
    · rw [Finset.card_pair hne, h2]
  · have := he i0; rwa [hs0] at this
  · have := he i1; rwa [hs1] at this
  · exact fun h => hne (hC.src_inj (e i0).2 (e i1).2 h)

/-! ### Recíproco: un orden cíclico con orígenes distintos es un ciclo simple -/

lemma succMod_iterate_val {n : ℕ} (i : Fin n) (k : ℕ) :
    ((succMod)^[k] i).1 = (i.1 + k) % n := by
  induction k with
  | zero => simp [Nat.mod_eq_of_lt i.2]
  | succ k ih =>
    rw [Function.iterate_succ_apply', succMod]
    simp only [ih]
    rw [Nat.add_mod, Nat.mod_mod, ← Nat.add_mod, add_assoc]

lemma succMod_injective {n : ℕ} : Function.Injective (succMod : Fin n → Fin n) := by
  intro i j h
  have h' := congrArg Fin.val h
  simp only [succMod] at h'
  apply Fin.ext
  have hi := i.2
  have hj := j.2
  rcases Nat.lt_or_ge (i.1 + 1) n with h1 | h1 <;> rcases Nat.lt_or_ge (j.1 + 1) n with h2 | h2
  · rw [Nat.mod_eq_of_lt h1, Nat.mod_eq_of_lt h2] at h'; omega
  · rw [Nat.mod_eq_of_lt h1, show j.1 + 1 = n by omega, Nat.mod_self] at h'; omega
  · rw [Nat.mod_eq_of_lt h2, show i.1 + 1 = n by omega, Nat.mod_self] at h'; omega
  · omega

/-- **Recíproco.** Si `C` no es vacío, `src` es inyectiva en `C`, y una enumeración
`e : Fin C.card ≃ {a // a ∈ C}` satisface `tgt (e i) = src (e ((i+1) mod C.card))`, entonces
`C` es un ciclo simple. Junto con `exists_cyclicOrder`, la formulación ordenada es equivalente
a `IsSimpleCycle`. -/
theorem isSimpleCycle_of_cyclicOrder (hne : C.Nonempty) (hsrc : Set.InjOn src C)
    (e : Fin C.card ≃ {a // a ∈ C}) (he : ∀ i : Fin C.card, tgt (e i).1 = src (e (succMod i)).1) :
    IsSimpleCycle src tgt C := by
  have htgt_e : ∀ i, tgt (e i).1 = src (e (succMod i)).1 := he
  have hmemC : ∀ b (hb : b ∈ C), ∃ i, (e i).1 = b := fun b hb => ⟨e.symm ⟨b, hb⟩, by simp⟩
  -- clausura: un subconjunto balanceado contiene el sucesor de cada uno de sus arcos
  have hclosed : ∀ D ⊆ C, D.image src = D.image tgt → ∀ i, (e i).1 ∈ D → (e (succMod i)).1 ∈ D := by
    intro D hDC hbal i hi
    have : tgt (e i).1 ∈ D.image src := hbal ▸ Finset.mem_image_of_mem tgt hi
    obtain ⟨b, hb, hbs⟩ := Finset.mem_image.mp this
    rw [htgt_e] at hbs
    have := hsrc (hDC hb) (e (succMod i)).2 hbs
    rw [← this]; exact hb
  refine ⟨hne, hsrc, ?_, ?_, ?_⟩
  · intro a ha b hb hab
    obtain ⟨i, rfl⟩ := hmemC a ha
    obtain ⟨j, rfl⟩ := hmemC b hb
    rw [htgt_e, htgt_e] at hab
    have := hsrc (e (succMod i)).2 (e (succMod j)).2 hab
    rw [succMod_injective (e.injective (Subtype.ext this))]
  · ext v
    simp only [Finset.mem_image]
    constructor
    · rintro ⟨a, ha, rfl⟩
      obtain ⟨i, rfl⟩ := hmemC a ha
      -- predecesor de `i`
      obtain ⟨j, hj⟩ : ∃ j, succMod j = i := by
        have hsurj : Function.Surjective (succMod : Fin C.card → Fin C.card) :=
          Finite.injective_iff_surjective.mp succMod_injective
        exact hsurj i
      exact ⟨(e j).1, (e j).2, by rw [htgt_e, hj]⟩
    · rintro ⟨a, ha, rfl⟩
      obtain ⟨i, rfl⟩ := hmemC a ha
      exact ⟨(e (succMod i)).1, (e (succMod i)).2, (htgt_e i).symm⟩
  · intro D hDC hDne hbal
    apply Finset.Subset.antisymm hDC
    obtain ⟨a, ha⟩ := hDne
    obtain ⟨i, rfl⟩ := hmemC a (hDC ha)
    have hit : ∀ k, (e ((succMod)^[k] i)).1 ∈ D := by
      intro k
      induction k with
      | zero => simpa using ha
      | succ k ih =>
        rw [Function.iterate_succ_apply']
        exact hclosed D hDC hbal _ ih
    intro b hb
    obtain ⟨j, rfl⟩ := hmemC b hb
    have hk : (succMod)^[(j.1 + C.card - i.1)] i = j := by
      apply Fin.ext
      rw [succMod_iterate_val]
      have := i.2
      have := j.2
      rw [show i.1 + (j.1 + C.card - i.1) = j.1 + C.card by omega, Nat.add_mod_right,
        Nat.mod_eq_of_lt j.2]
    rw [← hk]
    exact hit _

/-- **Equivalencia** entre `IsSimpleCycle` y la existencia de un orden cíclico con orígenes
distintos. -/
theorem isSimpleCycle_iff_cyclicOrder :
    IsSimpleCycle src tgt C ↔ C.Nonempty ∧ Set.InjOn src C ∧
      ∃ e : Fin C.card ≃ {a // a ∈ C}, ∀ i : Fin C.card, tgt (e i).1 = src (e (succMod i)).1 := by
  constructor
  · intro hC
    obtain ⟨a, ha⟩ := hC.nonempty
    obtain ⟨e, -, he⟩ := hC.exists_cyclicOrder ⟨a, ha⟩
    exact ⟨hC.nonempty, hC.src_inj, e, he⟩
  · rintro ⟨hne, hsrc, e, he⟩
    exact isSimpleCycle_of_cyclicOrder hne hsrc e he

end TypedTriangle.Circulation
