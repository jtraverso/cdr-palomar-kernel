/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import Mathlib

@[expose] public section

/-!
# Descomposición conforme de circulaciones enteras en ciclos simples (V10, S26 paso 2)

Bloque genérico del paso 2 de la Prioridad B: una circulación entera sobre un multigrafo
dirigido finito arbitrario (`src tgt : E → V`) se descompone en una lista finita de ciclos
dirigidos simples, conservando EXACTAMENTE

* la suma: `f e = Σ_C χ_C(e)` coordenada a coordenada (sin saturación racional);
* la norma total: `Σ_e |f e| = Σ_C |C|`;
* las ocurrencias por vértice: el número de ciclos que pasan por `v` es el flujo
  saliente orientado de `|f|` en `v`.

La descomposición es conforme: cada arco aparece en un ciclo sólo en el sentido del signo
de `f`. Nada aquí supone la conclusión: la lista de ciclos se CONSTRUYE (inducción fuerte
sobre la norma; cada paso extrae un conjunto mínimo de arcos balanceado e inyectivo del
soporte, obtenido como conjunto cerrado mínimo de una función sucesor).

No se instancia aquí el grafo de filas de componentes de S26 (cuyo documento fuente no
llegó en este envío); el resultado se enuncia para un multigrafo arbitrario para poder
aplicarse a ese grafo (incluidas columnas virtuales como arcos adicionales) sin cambios.
-/

open Finset

noncomputable section
open Classical

namespace TypedTriangle.Circulation

variable {V E : Type*} [Fintype V] [Fintype E]

/-- Flujo de `f` por los arcos con `s e = v` (saliente si `s = src`, entrante si `s = tgt`). -/
def flowAt (s : E → V) (f : E → ℕ) (v : V) : ℕ := ∑ e ∈ univ.filter (fun e => s e = v), f e

/-- `f : E → ℕ` es una circulación: flujo entrante = flujo saliente en cada vértice. -/
def IsCirc (src tgt : E → V) (f : E → ℕ) : Prop := ∀ v, flowAt tgt f v = flowAt src f v

/-- Ciclo dirigido simple, como conjunto de arcos: no vacío, a lo sumo un arco sale y a lo
sumo uno entra en cada vértice, el conjunto de orígenes es el de destinos, y ningún
subconjunto propio no vacío es balanceado (conexión: un solo ciclo). -/
structure IsSimpleCycle (src tgt : E → V) (C : Finset E) : Prop where
  nonempty : C.Nonempty
  src_inj : Set.InjOn src C
  tgt_inj : Set.InjOn tgt C
  balanced : C.image src = C.image tgt
  minimal : ∀ D ⊆ C, D.Nonempty → D.image src = D.image tgt → D = C

/-- Indicador de un conjunto de arcos. -/
def ind (C : Finset E) (e : E) : ℕ := if e ∈ C then 1 else 0

omit [Fintype V] [Fintype E] in
lemma card_filter_of_injOn (s : E → V) (C : Finset E) (h : Set.InjOn s C) (v : V) :
    (C.filter (fun e => s e = v)).card = if v ∈ C.image s then 1 else 0 := by
  split_ifs with hv
  · obtain ⟨e, he, rfl⟩ := Finset.mem_image.mp hv
    rw [Finset.card_eq_one]
    refine ⟨e, ?_⟩
    ext x
    simp only [Finset.mem_filter, Finset.mem_singleton]
    constructor
    · rintro ⟨hx, hxe⟩
      exact h hx he hxe
    · rintro rfl
      exact ⟨he, rfl⟩
  · rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    intro x hx hxv
    exact hv (Finset.mem_image.mpr ⟨x, hx, hxv⟩)

omit [Fintype V] in
lemma flowAt_ind (s : E → V) (C : Finset E) (v : V) :
    flowAt s (ind C) v = (C.filter (fun e => s e = v)).card := by
  unfold flowAt ind
  rw [Finset.sum_boole, Nat.cast_id, Finset.filter_filter]
  congr 1
  ext x
  simp [and_comm]

omit [Fintype V] in
lemma flowAt_ind_of_injOn (s : E → V) (C : Finset E) (h : Set.InjOn s C) (v : V) :
    flowAt s (ind C) v = if v ∈ C.image s then 1 else 0 := by
  rw [flowAt_ind, card_filter_of_injOn s C h]

omit [Fintype V] in
lemma IsSimpleCycle.isCirc {src tgt : E → V} {C : Finset E} (hC : IsSimpleCycle src tgt C) :
    IsCirc src tgt (ind C) := by
  intro v
  rw [flowAt_ind_of_injOn _ _ hC.tgt_inj, flowAt_ind_of_injOn _ _ hC.src_inj, hC.balanced]

/-- Existencia de un conjunto de arcos del soporte, no vacío, balanceado y con orígenes y
destinos inyectivos. -/
lemma exists_balanced_in_support (src tgt : E → V) (f : E → ℕ) (hf : IsCirc src tgt f)
    (e₀ : E) (he₀ : 0 < f e₀) :
    ∃ C : Finset E, C.Nonempty ∧ (∀ e ∈ C, 0 < f e) ∧ Set.InjOn src C ∧ Set.InjOn tgt C ∧
      C.image src = C.image tgt := by
  set W : Finset V := univ.filter (fun v => ∃ e, src e = v ∧ 0 < f e) with hW
  let a : V → E := fun v => if h : ∃ e, src e = v ∧ 0 < f e then h.choose else e₀
  have ha : ∀ v ∈ W, src (a v) = v ∧ 0 < f (a v) := by
    intro v hv
    have h : ∃ e, src e = v ∧ 0 < f e := (Finset.mem_filter.mp hv).2
    simp only [a, dif_pos h]
    exact h.choose_spec
  let succ : V → V := fun v => tgt (a v)
  have hsucc : ∀ v ∈ W, succ v ∈ W := by
    intro v hv
    obtain ⟨h1, h2⟩ := ha v hv
    have hin : 0 < flowAt tgt f (succ v) := by
      unfold flowAt
      exact lt_of_lt_of_le h2
        (Finset.single_le_sum (fun _ _ => Nat.zero_le _)
          (Finset.mem_filter.mpr ⟨Finset.mem_univ _, rfl⟩))
    rw [hf] at hin
    unfold flowAt at hin
    have hex : ∃ e ∈ univ.filter (fun e => src e = succ v), 0 < f e := by
      by_contra hcon
      push_neg at hcon
      have h0 : ∑ e ∈ univ.filter (fun e => src e = succ v), f e = 0 :=
        Finset.sum_eq_zero (fun e he => Nat.eq_zero_of_le_zero (hcon e he))
      omega
    obtain ⟨e, he, hpos⟩ := hex
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at he
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, e, he, hpos⟩
  have hWne : W.Nonempty := ⟨src e₀, Finset.mem_filter.mpr ⟨Finset.mem_univ _, e₀, rfl, he₀⟩⟩
  set 𝒳 : Finset (Finset V) :=
    W.powerset.filter (fun X => X.Nonempty ∧ ∀ x ∈ X, succ x ∈ X) with h𝒳
  have hW𝒳 : W ∈ 𝒳 := Finset.mem_filter.mpr ⟨Finset.mem_powerset_self _, hWne, hsucc⟩
  obtain ⟨X, hX, hXmin⟩ := Finset.exists_min_image 𝒳 Finset.card ⟨W, hW𝒳⟩
  obtain ⟨hXW, hXne, hXcl⟩ := Finset.mem_filter.mp hX
  rw [Finset.mem_powerset] at hXW
  have himgX : X.image succ ⊆ X := by
    intro y hy
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hy
    exact hXcl x hx
  have himg𝒳 : X.image succ ∈ 𝒳 := by
    refine Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr (himgX.trans hXW), hXne.image _, ?_⟩
    intro y hy
    exact Finset.mem_image.mpr ⟨y, himgX hy, rfl⟩
  have hXeq : X.image succ = X :=
    Finset.eq_of_subset_of_card_le himgX (hXmin _ himg𝒳)
  have hinj : Set.InjOn succ X := by
    apply Finset.injOn_of_card_image_eq
    rw [hXeq]
  have haX : ∀ x ∈ X, src (a x) = x ∧ 0 < f (a x) := fun x hx => ha x (hXW hx)
  refine ⟨X.image a, hXne.image _, ?_, ?_, ?_, ?_⟩
  · intro e he
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp he
    exact (haX x hx).2
  · intro e₁ he₁ e₂ he₂ h
    obtain ⟨x₁, hx₁, rfl⟩ := Finset.mem_image.mp (Finset.mem_coe.mp he₁)
    obtain ⟨x₂, hx₂, rfl⟩ := Finset.mem_image.mp (Finset.mem_coe.mp he₂)
    rw [(haX x₁ hx₁).1, (haX x₂ hx₂).1] at h
    rw [h]
  · intro e₁ he₁ e₂ he₂ h
    obtain ⟨x₁, hx₁, rfl⟩ := Finset.mem_image.mp (Finset.mem_coe.mp he₁)
    obtain ⟨x₂, hx₂, rfl⟩ := Finset.mem_image.mp (Finset.mem_coe.mp he₂)
    have : x₁ = x₂ := hinj hx₁ hx₂ h
    rw [this]
  · rw [Finset.image_image, Finset.image_image]
    have h1 : X.image (src ∘ a) = X := by
      have h1' : X.image (src ∘ a) = X.image id :=
        Finset.image_congr (fun x hx => (haX x hx).1)
      rw [h1', Finset.image_id]
    have h2 : X.image (tgt ∘ a) = X.image succ := rfl
    rw [h1, h2, hXeq]

/-- Existencia de un ciclo simple dentro del soporte de una circulación no nula. -/
lemma exists_simpleCycle_in_support (src tgt : E → V) (f : E → ℕ) (hf : IsCirc src tgt f)
    (e₀ : E) (he₀ : 0 < f e₀) :
    ∃ C : Finset E, IsSimpleCycle src tgt C ∧ ∀ e ∈ C, 0 < f e := by
  set 𝒞 : Finset (Finset E) := (univ : Finset E).powerset.filter (fun C =>
    C.Nonempty ∧ (∀ e ∈ C, 0 < f e) ∧ Set.InjOn src C ∧ Set.InjOn tgt C ∧
      C.image src = C.image tgt) with h𝒞
  obtain ⟨C₀, hC₀⟩ := exists_balanced_in_support src tgt f hf e₀ he₀
  have hC₀𝒞 : C₀ ∈ 𝒞 :=
    Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr (Finset.subset_univ _), hC₀⟩
  obtain ⟨C, hC, hCmin⟩ := Finset.exists_min_image 𝒞 Finset.card ⟨C₀, hC₀𝒞⟩
  obtain ⟨-, hne, hpos, hs, ht, hbal⟩ := Finset.mem_filter.mp hC
  refine ⟨C, ⟨hne, hs, ht, hbal, ?_⟩, hpos⟩
  intro D hDC hDne hDbal
  have hD𝒞 : D ∈ 𝒞 := Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr (Finset.subset_univ _),
    hDne, fun e he => hpos e (hDC he), hs.mono (by exact_mod_cast hDC),
    ht.mono (by exact_mod_cast hDC), hDbal⟩
  exact Finset.eq_of_subset_of_card_le hDC (hCmin D hD𝒞)

/-- Intercambio de una suma finita con la suma de una lista. -/
lemma sum_list_map_comm {ι κ : Type*} (s : Finset ι) (L : List κ) (g : κ → ι → ℕ) :
    ∑ i ∈ s, (L.map (fun C => g C i)).sum = (L.map (fun C => ∑ i ∈ s, g C i)).sum := by
  induction L with
  | nil => simp
  | cons C L ih => simp [Finset.sum_add_distrib, ih]

/-- `countP` como suma de indicadores. -/
lemma countP_eq_sum_ite {κ : Type*} (p : κ → Bool) (L : List κ) :
    L.countP p = (L.map (fun C => if p C then 1 else 0)).sum := by
  induction L with
  | nil => simp
  | cons C L ih =>
    rw [List.countP_cons, ih]
    by_cases h : p C <;> simp [h, add_comm]

/-- Diferencia de sumas de listas, en `ℤ`. -/
lemma cast_sum_map_sub {κ : Type*} (L : List κ) (g h : κ → ℕ) :
    ((L.map g).sum : ℤ) - (L.map h).sum = (L.map (fun C => (g C : ℤ) - h C)).sum := by
  induction L with
  | nil => simp
  | cons C L ih =>
    simp only [List.map_cons, List.sum_cons, Nat.cast_add]
    rw [← ih]
    ring

/-- **Descomposición en ciclos (versión no negativa).** Toda circulación `f : E → ℕ` es la
suma exacta de los indicadores de una lista finita de ciclos dirigidos simples. -/
theorem exists_cycle_decomp (src tgt : E → V) (f : E → ℕ) (hf : IsCirc src tgt f) :
    ∃ L : List (Finset E), (∀ C ∈ L, IsSimpleCycle src tgt C) ∧
      ∀ e, f e = (L.map (fun C => ind C e)).sum := by
  induction h : ∑ e, f e using Nat.strong_induction_on generalizing f with
  | _ n ih =>
  by_cases hz : ∀ e, f e = 0
  · exact ⟨[], by simp, fun e => by simp [hz e]⟩
  push_neg at hz
  obtain ⟨e₀, he₀⟩ := hz
  obtain ⟨C, hC, hCpos⟩ :=
    exists_simpleCycle_in_support src tgt f hf e₀ (Nat.pos_of_ne_zero he₀)
  have hle : ∀ e, ind C e ≤ f e := by
    intro e
    unfold ind
    split_ifs with he
    · exact hCpos e he
    · exact Nat.zero_le _
  set f' : E → ℕ := fun e => f e - ind C e with hf'
  have hf'circ : IsCirc src tgt f' := by
    intro v
    unfold flowAt
    simp only [hf']
    rw [Finset.sum_tsub_distrib _ (fun e _ => hle e),
      Finset.sum_tsub_distrib _ (fun e _ => hle e)]
    have h1 := hf v
    have h2 := hC.isCirc v
    unfold flowAt at h1 h2
    rw [h1, h2]
  have hsum : ∑ e, f' e < n := by
    simp only [hf']
    rw [Finset.sum_tsub_distrib _ (fun e _ => hle e), ← h]
    have hpos : 0 < ∑ e, ind C e := by
      obtain ⟨c, hc⟩ := hC.nonempty
      exact lt_of_lt_of_le (by simp [ind, hc] : 0 < ind C c)
        (Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ c))
    have hle' : ∑ e, ind C e ≤ ∑ e, f e := Finset.sum_le_sum (fun e _ => hle e)
    omega
  obtain ⟨L, hL, hLsum⟩ := ih _ hsum f' hf'circ rfl
  refine ⟨C :: L, ?_, ?_⟩
  · intro D hD
    rcases List.mem_cons.mp hD with rfl | hD
    · exact hC
    · exact hL D hD
  · intro e
    simp only [List.map_cons, List.sum_cons]
    rw [← hLsum e]
    simp only [hf']
    have := hle e
    omega

/-- Cardinal de un ciclo como suma de su indicador. -/
lemma sum_ind (C : Finset E) : ∑ e, ind C e = C.card := by
  unfold ind
  rw [Finset.sum_boole, Nat.cast_id]
  congr 1
  ext; simp

/-- **Descomposición en ciclos con norma y ocurrencias exactas (versión no negativa).** -/
theorem exists_cycle_decomp_counts (src tgt : E → V) (f : E → ℕ) (hf : IsCirc src tgt f) :
    ∃ L : List (Finset E), (∀ C ∈ L, IsSimpleCycle src tgt C) ∧
      (∀ e, f e = (L.map (fun C => ind C e)).sum) ∧
      ∑ e, f e = (L.map Finset.card).sum ∧
      ∀ v, flowAt src f v = L.countP (fun C => v ∈ C.image src) := by
  obtain ⟨L, hL, hsum⟩ := exists_cycle_decomp src tgt f hf
  refine ⟨L, hL, hsum, ?_, ?_⟩
  · rw [Finset.sum_congr rfl (fun e _ => hsum e), sum_list_map_comm]
    congr 1
    exact List.map_congr_left (fun C _ => sum_ind C)
  · intro v
    unfold flowAt
    rw [Finset.sum_congr rfl (fun e _ => hsum e), sum_list_map_comm, countP_eq_sum_ite]
    -- cada término es el flujo saliente del indicador
    congr 1
    refine List.map_congr_left (fun C hC => ?_)
    have := flowAt_ind_of_injOn src C (hL C hC).src_inj v
    unfold flowAt at this
    rw [this]
    simp

/-! ### Versión con signo -/

/-- Circulación entera con signo: `Σ_{tgt e = v} f e = Σ_{src e = v} f e`. -/
def IsCircZ (src tgt : E → V) (f : E → ℤ) : Prop :=
  ∀ v, ∑ e ∈ univ.filter (fun e => tgt e = v), f e = ∑ e ∈ univ.filter (fun e => src e = v), f e

/-- Origen de un arco orientado (`true`: sentido del arco; `false`: sentido opuesto). -/
def sSrc (src tgt : E → V) : E × Bool → V := fun p => if p.2 then src p.1 else tgt p.1

/-- Destino de un arco orientado. -/
def sTgt (src tgt : E → V) : E × Bool → V := fun p => if p.2 then tgt p.1 else src p.1

/-- Partes positiva y negativa de `f`, como flujo no negativo en los arcos orientados. -/
def posNeg (f : E → ℤ) : E × Bool → ℕ := fun p => if p.2 then (f p.1).toNat else (-f p.1).toNat

/-- Indicador con signo de un ciclo de arcos orientados. -/
def sInd (C : Finset (E × Bool)) (e : E) : ℤ := (ind C (e, true) : ℤ) - ind C (e, false)

omit [Fintype V] in
lemma flowAt_eq_sum_ite {ι : Type*} [Fintype ι] (s : ι → V) (g : ι → ℕ) (v : V) :
    flowAt s g v = ∑ i, if s i = v then g i else 0 := by
  unfold flowAt
  rw [Finset.sum_filter]

omit [Fintype V] in
lemma posNeg_isCirc (src tgt : E → V) (f : E → ℤ) (hf : IsCircZ src tgt f) :
    IsCirc (sSrc src tgt) (sTgt src tgt) (posNeg f) := by
  intro v
  rw [flowAt_eq_sum_ite, flowAt_eq_sum_ite, Fintype.sum_prod_type, Fintype.sum_prod_type]
  simp only [Fintype.sum_bool, sTgt, sSrc, posNeg, if_true, Bool.false_eq_true, if_false]
  have h := hf v
  rw [Finset.sum_filter, Finset.sum_filter] at h
  have key : ∀ e : E, f e = ((f e).toNat : ℤ) - ((-f e).toNat : ℤ) :=
    fun e => (Int.toNat_sub_toNat_neg (f e)).symm
  apply Nat.cast_injective (R := ℤ)
  simp only [Nat.cast_sum, Nat.cast_add, Nat.cast_ite, Nat.cast_zero]
  have h' : ∑ e : E, (if tgt e = v then ((f e).toNat : ℤ) - ((-f e).toNat : ℤ) else 0) =
      ∑ e : E, (if src e = v then ((f e).toNat : ℤ) - ((-f e).toNat : ℤ) else 0) := by
    simpa only [← key] using h
  have hsplit : ∀ (s : E → V),
      ∑ e : E, (if s e = v then ((f e).toNat : ℤ) - ((-f e).toNat : ℤ) else 0) =
      ∑ e : E, (if s e = v then ((f e).toNat : ℤ) else 0) -
        ∑ e : E, (if s e = v then ((-f e).toNat : ℤ) else 0) := by
    intro s
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl (fun e _ => ?_)
    split_ifs <;> simp
  rw [hsplit, hsplit] at h'
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
  linarith

/-- **Descomposición conforme de una circulación entera con signo.** Para toda circulación
`f : E → ℤ` existe una lista finita de ciclos dirigidos simples en el grafo de arcos
orientados tal que:
* (conformidad) cada arco orientado de cada ciclo va en el sentido del signo de `f`;
* (suma exacta) `f e = Σ_C sInd C e` para todo `e`;
* (norma exacta) `Σ_e |f e| = Σ_C |C|`;
* (ocurrencias exactas) el número de ciclos que pasan por `v` es
  `Σ_{src e = v} (f e)⁺ + Σ_{tgt e = v} (f e)⁻`. -/
theorem exists_signed_cycle_decomp (src tgt : E → V) (f : E → ℤ) (hf : IsCircZ src tgt f) :
    ∃ L : List (Finset (E × Bool)),
      (∀ C ∈ L, IsSimpleCycle (sSrc src tgt) (sTgt src tgt) C) ∧
      (∀ C ∈ L, ∀ p ∈ C, (p.2 = true → 0 < f p.1) ∧ (p.2 = false → f p.1 < 0)) ∧
      (∀ e, f e = (L.map (fun C => sInd C e)).sum) ∧
      (∑ e, |f e| = ((L.map Finset.card).sum : ℤ)) ∧
      ∀ v, L.countP (fun C => v ∈ C.image (sSrc src tgt)) =
        ∑ e ∈ univ.filter (fun e => src e = v), (f e).toNat +
          ∑ e ∈ univ.filter (fun e => tgt e = v), (-f e).toNat := by
  obtain ⟨L, hL, hsum, hnorm, hocc⟩ :=
    exists_cycle_decomp_counts (sSrc src tgt) (sTgt src tgt) (posNeg f)
      (posNeg_isCirc src tgt f hf)
  refine ⟨L, hL, ?_, ?_, ?_, ?_⟩
  · intro C hC p hp
    have hle : 1 ≤ posNeg f p := by
      rw [hsum p]
      have : ind C p ∈ L.map (fun C => ind C p) := List.mem_map_of_mem hC
      have h1 := List.le_sum_of_mem this
      simpa [ind, hp] using h1
    obtain ⟨e, b⟩ := p
    cases b
    · refine ⟨fun h => absurd h (by simp), fun _ => ?_⟩
      simp [posNeg] at hle ⊢
      omega
    · refine ⟨fun _ => ?_, fun h => absurd h (by simp)⟩
      simp [posNeg] at hle ⊢
      omega
  · intro e
    have h1 := hsum (e, true)
    have h2 := hsum (e, false)
    simp only [posNeg, if_true, Bool.false_eq_true, if_false] at h1 h2
    have key := (Int.toNat_sub_toNat_neg (f e)).symm
    rw [h1, h2, cast_sum_map_sub] at key
    exact key
  · have habs : ∀ e, |f e| = (((f e).toNat + (-f e).toNat : ℕ) : ℤ) := by
      intro e
      rw [Nat.cast_add]
      rcases abs_cases (f e) with ⟨h, h'⟩ | ⟨h, h'⟩ <;> omega
    rw [Finset.sum_congr rfl (fun e _ => habs e), ← Nat.cast_sum, ← hnorm,
      Fintype.sum_prod_type]
    simp [posNeg]
  · intro v
    rw [← hocc v, flowAt_eq_sum_ite, Fintype.sum_prod_type, Finset.sum_filter,
      Finset.sum_filter, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun e _ => ?_)
    simp [sSrc, posNeg]

/-- Reagrupación por fibras de una función de raíces `ρ : V → R`. -/
lemma sum_fiber_root {R : Type*} (ρ : V → R) (r : R) (s : E → V) (g : E → ℕ) :
    ∑ v ∈ univ.filter (fun v => ρ v = r), ∑ e ∈ univ.filter (fun e => s e = v), g e =
      ∑ e ∈ univ.filter (fun e => ρ (s e) = r), g e := by
  rw [← Finset.sum_fiberwise_of_maps_to (s := univ.filter (fun e => ρ (s e) = r))
    (t := univ.filter (fun v => ρ v = r)) (g := s)
    (fun x hx => by simpa using hx)]
  refine Finset.sum_congr rfl (fun v hv => ?_)
  congr 1
  ext e
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hv ⊢
  constructor
  · intro h; exact ⟨h ▸ hv, h⟩
  · exact fun h => h.2

/-- **Descomposición conforme con ocurrencias por raíz física.** Misma descomposición que
`exists_signed_cycle_decomp`; además, para cualquier asignación de raíces `ρ : V → R`
(p. ej. estado ↦ vértice físico), el número total de pasos de los ciclos por estados de
raíz `r` es exactamente `Σ_{ρ(src e) = r} (f e)⁺ + Σ_{ρ(tgt e) = r} (f e)⁻`. -/
theorem exists_signed_cycle_decomp_roots {R : Type*} (ρ : V → R) (src tgt : E → V)
    (f : E → ℤ) (hf : IsCircZ src tgt f) :
    ∃ L : List (Finset (E × Bool)),
      (∀ C ∈ L, IsSimpleCycle (sSrc src tgt) (sTgt src tgt) C) ∧
      (∀ C ∈ L, ∀ p ∈ C, (p.2 = true → 0 < f p.1) ∧ (p.2 = false → f p.1 < 0)) ∧
      (∀ e, f e = (L.map (fun C => sInd C e)).sum) ∧
      (∑ e, |f e| = ((L.map Finset.card).sum : ℤ)) ∧
      (∀ v, L.countP (fun C => v ∈ C.image (sSrc src tgt)) =
        ∑ e ∈ univ.filter (fun e => src e = v), (f e).toNat +
          ∑ e ∈ univ.filter (fun e => tgt e = v), (-f e).toNat) ∧
      ∀ r, ∑ v ∈ univ.filter (fun v => ρ v = r),
          L.countP (fun C => v ∈ C.image (sSrc src tgt)) =
        ∑ e ∈ univ.filter (fun e => ρ (src e) = r), (f e).toNat +
          ∑ e ∈ univ.filter (fun e => ρ (tgt e) = r), (-f e).toNat := by
  obtain ⟨L, h1, h2, h3, h4, h5⟩ := exists_signed_cycle_decomp src tgt f hf
  refine ⟨L, h1, h2, h3, h4, h5, fun r => ?_⟩
  rw [Finset.sum_congr rfl (fun v _ => h5 v), Finset.sum_add_distrib,
    sum_fiber_root ρ r src, sum_fiber_root ρ r tgt]

end TypedTriangle.Circulation
