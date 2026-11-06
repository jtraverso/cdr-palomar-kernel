/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import RequestProject.TypedTriangle.SignedCover

@[expose] public section

/-!
# Lift de una demanda del núcleo aumentado a una circulación de la cubierta (S26 §4) — V11

Se expande `(x, z)` en unidades con signo (`|x p|` copias de la unidad de la columna `p`,
`|z j|` de la vertical de `j`). Cada unidad tiene dos semiaristas, con signo dado por su
coeficiente y el signo de su coordenada. La ecuación `B_aug(x, z) = 0` hace par el grado de
cada fila; la orientación euleriana (`EulerOrient`) empareja en cada fila salidas con
entradas, y la transición de estados de S26 §2 convierte las unidades orientadas en arcos
de la cubierta. El flujo resultante es una circulación conforme cuya proyección es
exactamente `(x, z)`.
-/

open Finset Classical

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace TypedTriangle.SignedCover

open TypedTriangle.Circulation TypedTriangle.EulerOrient

variable {R P : Type*} [Fintype R] [Fintype P] (S : RowSystem R P)

/-- Extremo de una unidad: `(fila, signo de la semiarista, ¿es el extremo 1?)`. -/
abbrev End (R : Type*) := R × Bool × Bool

/-- Etiqueta de una unidad: columna física o fila virtual. -/
abbrev Tag := P ⊕ VRow S

/-- Unidad: etiqueta y dos extremos. -/
abbrev Piece := Tag S × End R × End R

/-- Signo (booleano) de un entero; el caso `0` es irrelevante (multiplicidad nula). -/
def posB (y : ℤ) : Bool := decide (0 ≤ y)

lemma abs_mul_sgn (y : ℤ) (a : Bool) : |y| * sgn (posB y == a) = sgn a * y := by
  unfold posB
  by_cases hy : 0 ≤ y
  · rw [abs_of_nonneg hy]; cases a <;> simp [hy, sgn]
  · rw [abs_of_neg (by omega)]; cases a <;> simp [hy, sgn]

lemma abs_mul_sgn_posB (y : ℤ) : |y| * sgn (posB y) = y := by
  simpa using abs_mul_sgn y true

lemma sgn_posB_mul_pos {y : ℤ} (hy : y ≠ 0) : 0 < sgn (posB y) * y := by
  unfold posB sgn
  by_cases h : 0 ≤ y
  · simp [h]; omega
  · simp [h]; omega

variable (x : P → ℤ) (z : R → ℤ)

/-- Unidad de la columna física `p`. -/
def unitP (p : P) : Piece S :=
  (Sum.inl p, (S.r1 p, posB (x p) == S.a1 p, true), (S.r2 p, posB (x p) == S.a2 p, false))

/-- Unidad de la columna virtual de `j` (sus dos semiaristas tienen signo `−sgn z_j`). -/
def unitV (j : VRow S) : Piece S :=
  (Sum.inr j, (j.1, !posB (z j.1), true), (j.1, !posB (z j.1), false))

/-- Multiconjunto de unidades de `(x, z)`. -/
def units : Multiset (Piece S) :=
  ∑ p, Multiset.replicate (x p).natAbs (unitP S x p) +
    ∑ j : VRow S, Multiset.replicate (z j.1).natAbs (unitV S z j)

/-- Arco de la cubierta recorrido por una unidad orientada. -/
def arcOf : Piece S → Arc S
  | (Sum.inl p, w, _) => Sum.inl (p, w.2.2, w.2.1)
  | (Sum.inr j, w, _) => Sum.inr (j, w.2.1)

/-- Proyección física prescrita por la etiqueta. -/
def tP : Tag S → P → ℤ
  | Sum.inl p, q => if p = q then sgn (posB (x q)) else 0
  | Sum.inr _, _ => 0

/-- Proyección virtual prescrita por la etiqueta. -/
def tV : Tag S → R → ℤ
  | Sum.inl _, _ => 0
  | Sum.inr k, j => if k.1 = j then sgn (posB (z j)) else 0

lemma sum_map_finset_sum {α ι : Type*} (s : Finset ι) (F : ι → Multiset α) (g : α → ℤ) :
    ((∑ i ∈ s, F i).map g).sum = ∑ i ∈ s, ((F i).map g).sum := by
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, Multiset.map_add,
      Multiset.sum_add, ih]

lemma sum_map_units (g : Piece S → ℤ) :
    ((units S x z).map g).sum = ∑ p, ((x p).natAbs : ℤ) * g (unitP S x p) +
      ∑ j : VRow S, ((z j.1).natAbs : ℤ) * g (unitV S z j) := by
  unfold units
  rw [Multiset.map_add, Multiset.sum_add, sum_map_finset_sum, sum_map_finset_sum]
  simp [Multiset.map_replicate, Multiset.sum_replicate]

lemma mem_units {u : Piece S} (hu : u ∈ units S x z) :
    (∃ p, x p ≠ 0 ∧ u = unitP S x p) ∨ (∃ j, z j.1 ≠ 0 ∧ u = unitV S z j) := by
  unfold units at hu
  rcases Multiset.mem_add.mp hu with h | h
  · obtain ⟨p, -, hp⟩ := Multiset.mem_sum.mp h
    obtain ⟨hn, rfl⟩ := Multiset.mem_replicate.mp hp
    exact Or.inl ⟨p, by simpa using hn, rfl⟩
  · obtain ⟨j, -, hj⟩ := Multiset.mem_sum.mp h
    obtain ⟨hn, rfl⟩ := Multiset.mem_replicate.mp hj
    exact Or.inr ⟨j, by simpa using hn, rfl⟩

omit [Fintype R] [Fintype P] in
/-- Propiedades de una unidad orientada: estados de salida/llegada y proyección. -/
lemma piece_props {u o : Piece S}
    (hu : (∃ p, u = unitP S x p) ∨ (∃ j, u = unitV S z j)) (ho : Flip u o) :
    src S (arcOf S o) = (o.2.1.1, o.2.1.2.1) ∧ tgt S (arcOf S o) = (o.2.2.1, !o.2.2.2.1) ∧
      (∀ q, projP S (arcOf S o) q = tP S x o.1 q) ∧
      (∀ j, projV S (arcOf S o) j = tV S z o.1 j) := by
  rcases hu with ⟨p, rfl⟩ | ⟨k, rfl⟩ <;> rcases ho with rfl | rfl
  · refine ⟨by simp [unitP, arcOf, src], ?_, fun q => ?_, fun j => by simp [unitP, arcOf, projV, tV]⟩
    · simp only [unitP, arcOf, tgt, if_true, Prod.mk.injEq, true_and]
      unfold tsign; cases posB (x p) <;> cases S.a1 p <;> cases S.a2 p <;> simp
    · simp only [unitP, arcOf, projP, tP, if_true]
      by_cases hpq : p = q
      · subst hpq; simp only [if_true]
        cases posB (x p) <;> cases S.a1 p <;> decide
      · simp [hpq]
  · refine ⟨by simp [unitP, EulerOrient.flip, arcOf, src], ?_, fun q => ?_,
      fun j => by simp [unitP, EulerOrient.flip, arcOf, projV, tV]⟩
    · simp only [unitP, EulerOrient.flip, arcOf, tgt, Bool.false_eq_true, if_false, Prod.mk.injEq, true_and]
      unfold tsign; cases posB (x p) <;> cases S.a1 p <;> cases S.a2 p <;> simp
    · simp only [unitP, EulerOrient.flip, arcOf, projP, tP, Bool.false_eq_true, if_false]
      by_cases hpq : p = q
      · subst hpq; simp only [if_true]
        cases posB (x p) <;> cases S.a2 p <;> decide
      · simp [hpq]
  · refine ⟨by simp [unitV, arcOf, src], by simp [unitV, arcOf, tgt], fun q => by
      simp [unitV, arcOf, projP, tP], fun j => ?_⟩
    simp only [unitV, arcOf, projV, tV]
    split_ifs with h
    · subst h; cases posB (z k.1) <;> rfl
    · rfl
  · refine ⟨by simp [unitV, EulerOrient.flip, arcOf, src], by simp [unitV, EulerOrient.flip, arcOf, tgt], fun q => by
      simp [unitV, EulerOrient.flip, arcOf, projP, tP], fun j => ?_⟩
    simp only [unitV, EulerOrient.flip, arcOf, projV, tV]
    split_ifs with h
    · subst h; cases posB (z k.1) <;> rfl
    · rfl


/-! ### Sumas sobre multiconjuntos -/

omit [Fintype R] [Fintype P] in
lemma countP_eq_sum_map {A : Type*} (O : Multiset A) (q : A → Prop) [DecidablePred q] :
    ((O.countP q : ℕ) : ℤ) = (O.map (fun a => if q a then (1 : ℤ) else 0)).sum := by
  induction O using Multiset.induction_on with
  | empty => simp
  | cons a O ih =>
    rw [Multiset.countP_cons, Multiset.map_cons, Multiset.sum_cons]
    push_cast; rw [ih]; split_ifs <;> ring

omit [Fintype R] [Fintype P] in
lemma sum_countP_mul {A B : Type*} [Fintype B] (O : Multiset A) (g : A → B) (h : B → ℤ)
    {d : ∀ b, DecidablePred fun a => g a = b} :
    ∑ b, ((@Multiset.countP _ (fun a => g a = b) (d b) O : ℕ) : ℤ) * h b = (O.map (fun a => h (g a))).sum := by
  induction O using Multiset.induction_on with
  | empty => simp
  | cons a O ih =>
    simp only [Multiset.countP_cons, Multiset.map_cons, Multiset.sum_cons, Nat.cast_add,
      add_mul, Finset.sum_add_distrib, ih]
    rw [add_comm]; congr 1
    rw [Finset.sum_eq_single (g a) (fun b _ hb => by simp [Ne.symm hb]) (by simp)]
    simp

omit [Fintype R] [Fintype P] in
lemma sum_filter_countP {A B C : Type*} [Fintype B] (O : Multiset A) (g : A → B) (st : B → C)
    (v : C) {d : ∀ b, DecidablePred fun a => g a = b} {d2 : DecidablePred fun b => st b = v}
    [DecidablePred fun a => st (g a) = v] :
    ∑ b ∈ @Finset.filter _ (fun b => st b = v) d2 univ,
        @Multiset.countP _ (fun a => g a = b) (d b) O =
      O.countP (fun a => st (g a) = v) := by
  induction O using Multiset.induction_on with
  | empty => simp
  | cons a O ih =>
    simp only [Multiset.countP_cons, Finset.sum_add_distrib, ih]
    congr 1
    by_cases hst : st (g a) = v
    · rw [Finset.sum_eq_single (g a) (fun b _ hb => by simp [Ne.symm hb]) (by simp [hst])]
      simp [hst]
    · rw [Finset.sum_eq_zero (fun b hb => by
        have : st b = v := (Finset.mem_filter.mp hb).2
        have hne : g a ≠ b := fun h => hst (h ▸ this)
        simp [hne])]
      simp [hst]

omit [Fintype P] in
lemma sum_vrow_ite (j : R) (c : ℤ) (hc : S.nb j = false → c = 0) :
    ∑ k : VRow S, (if k.1 = j then c else 0) = c := by
  by_cases hj : S.nb j = true
  · rw [Finset.sum_eq_single ⟨j, hj⟩ (fun b _ hb => by
      rw [if_neg]; intro h; exact hb (Subtype.ext h)) (by simp)]
    simp
  · rw [hc (by simpa using hj)]; simp

omit [Fintype P] in
lemma sum_vrow_abs (hz : ∀ j, S.nb j = false → z j = 0) :
    ∑ k : VRow S, ((z k.1).natAbs : ℤ) = ∑ j, |z j| := by
  have h1 : ∑ j, |z j| = ∑ j ∈ univ.filter (fun j => S.nb j = true), |z j| := by
    rw [Finset.sum_filter]
    refine Finset.sum_congr rfl fun j _ => ?_
    split_ifs with h
    · rfl
    · rw [hz j (by cases hb : S.nb j <;> simp_all)]; simp
  rw [h1]
  simp only [Int.natCast_natAbs]
  exact (Finset.sum_subtype (p := fun j => S.nb j = true) _ (fun j => by simp)
    (fun j => |z j|)).symm

/-! ### Funciones por fila -/

/-- Indicador de fila de un extremo. -/
def rowI (j : R) (w : End R) : ℤ := if w.1 = j then 1 else 0

/-- Signo de semiarista de un extremo en la fila `j`. -/
def rowS (j : R) (w : End R) : ℤ := if w.1 = j then sgn w.2.1 else 0

/-- Grado de una unidad en la fila `j`. -/
def dg (j : R) (u : Piece S) : ℤ := rowI j u.2.1 + rowI j u.2.2

/-- Carga con signo de una unidad en la fila `j`. -/
def sc (j : R) (u : Piece S) : ℤ := rowS j u.2.1 + rowS j u.2.2

lemma sum_sc_units (hz : ∀ j, S.nb j = false → z j = 0) (j : R) :
    ((units S x z).map (sc S j)).sum = baug S x z j := by
  rw [sum_map_units]
  unfold baug
  rw [sub_eq_add_neg]
  congr 1
  · refine Finset.sum_congr rfl fun p _ => ?_
    simp only [sc, rowS, unitP, mul_add]
    congr 1 <;> split_ifs <;> simp_all [abs_mul_sgn]
  · have : ∀ k : VRow S, ((z k.1).natAbs : ℤ) * sc S j (unitV S z k) =
        if k.1 = j then -(2 * z j) else 0 := by
      intro k
      simp only [sc, rowS, unitV]
      split_ifs with h
      · subst h
        have h2 : sgn (!posB (z k.1)) = - sgn (posB (z k.1)) := by
          cases posB (z k.1) <;> rfl
        rw [h2]
        have := abs_mul_sgn_posB (z k.1)
        simp only [Int.natCast_natAbs, ite_true]
        linear_combination (-2 : ℤ) * this
      · simp [h]
    rw [Finset.sum_congr rfl (fun k _ => this k)]
    exact sum_vrow_ite S j _ (fun h => by rw [hz j h]; simp)

omit [Fintype R] [Fintype P] in
lemma dg_eq (j : R) (u : Piece S) :
    dg S j u = 2 * ((if u.2.1.1 = j ∧ u.2.1.2.1 = true then 1 else 0) +
      (if u.2.2.1 = j ∧ u.2.2.2.1 = true then 1 else 0)) - sc S j u := by
  obtain ⟨t, ⟨r, a, b⟩, ⟨r', a', b'⟩⟩ := u
  simp only [dg, sc, rowI, rowS]
  by_cases h1 : r = j <;> by_cases h2 : r' = j <;> cases a <;> cases a' <;> simp [h1, h2, sgn]

omit [Fintype R] [Fintype P] in
lemma circ_eq (j : R) (s : Bool) (o : Piece S) :
    2 * ((if (o.2.1.1, o.2.1.2.1) = (j, s) then (1 : ℤ) else 0) -
      (if (o.2.2.1, !o.2.2.2.1) = (j, s) then 1 else 0)) =
      (rowI j o.2.1 - rowI j o.2.2) + sgn s * sc S j o := by
  obtain ⟨t, ⟨r, a, b⟩, ⟨r', a', b'⟩⟩ := o
  simp only [sc, rowI, rowS, Prod.mk.injEq]
  by_cases h1 : r = j <;> by_cases h2 : r' = j <;> cases a <;> cases a' <;> cases s <;>
    simp [h1, h2, sgn]

omit [Fintype R] [Fintype P] in
lemma row_eq (j : R) (o : Piece S) :
    (if (o.2.1.1, o.2.1.2.1) = (j, true) then (1 : ℤ) else 0) +
      (if (o.2.1.1, o.2.1.2.1) = (j, false) then 1 else 0) = rowI j o.2.1 := by
  obtain ⟨t, ⟨r, a, b⟩, w⟩ := o
  simp only [rowI, Prod.mk.injEq]
  by_cases h1 : r = j <;> cases a <;> simp [h1]

/-- **Lift de una demanda del núcleo aumentado (S26 §4).** Para `(x, z)` con
`B_aug(x, z) = 0` y `z` soportado en las filas virtuales, existe una circulación no
negativa `f` de la cubierta aumentada tal que:
* su proyección física es exactamente `x` y la virtual exactamente `z`;
* su masa es `‖x‖₁ + ‖z‖₁`;
* en cada fila `j`, el doble del flujo saliente de sus dos estados es el número de
  semiaristas de la fila: `Σ_p |x p| ([r1 p = j] + [r2 p = j]) + 2 |z j|`;
* es conforme: todo arco usado tiene proyección del signo de la coordenada. -/
theorem exists_lift_circulation (hz : ∀ j, S.nb j = false → z j = 0)
    (hker : ∀ j, baug S x z j = 0) :
    ∃ f : Arc S → ℕ, IsCirc (src S) (tgt S) f ∧ flowP S f = x ∧ flowV S f = z ∧
      ((∑ α, f α : ℕ) : ℤ) = ∑ p, |x p| + ∑ j, |z j| ∧
      (∀ j, 2 * ((flowAt (src S) f (j, true) + flowAt (src S) f (j, false) : ℕ) : ℤ) =
        ∑ p, ((if S.r1 p = j then |x p| else 0) + (if S.r2 p = j then |x p| else 0)) +
          2 * |z j|) ∧
      ∀ α, 0 < f α → (∀ q, projP S α q = 0 ∨ 0 < projP S α q * x q) ∧
        (∀ j, projV S α j = 0 ∨ 0 < projV S α j * z j) := by
  set M := units S x z with hMdef
  -- grados pares
  have hdeg : ∀ j, Even (degC (fun w : End R => w.1) M j) := by
    intro j
    have hcast : ((degC (fun w : End R => w.1) M j : ℕ) : ℤ) = (M.map (dg S j)).sum := by
      unfold degC outC inC
      push_cast
      rw [countP_eq_sum_map, countP_eq_sum_map, ← Multiset.sum_map_add]
      rfl
    have h2 : (M.map (dg S j)).sum = 2 * (M.map (fun u : Piece S =>
        ((if u.2.1.1 = j ∧ u.2.1.2.1 = true then 1 else 0) +
          (if u.2.2.1 = j ∧ u.2.2.2.1 = true then 1 else 0) : ℤ))).sum := by
      rw [Multiset.map_congr rfl (fun u _ => dg_eq S j u), Multiset.sum_map_sub,
        Multiset.sum_map_mul_left, hMdef, sum_sc_units S x z hz j, hker j, sub_zero]
    rw [← Int.even_coe_nat, hcast, h2]
    exact even_two_mul _
  obtain ⟨O, hrel, hbal⟩ := exists_euler_orientation (fun w : End R => w.1) M hdeg
  have hunit : ∀ o ∈ O, ∃ u, Flip u o ∧
      ((∃ p, x p ≠ 0 ∧ u = unitP S x p) ∨ (∃ k, z k.1 ≠ 0 ∧ u = unitV S z k)) := by
    intro o ho
    obtain ⟨u, hu, huo⟩ := Rel.exists_of_mem hrel ho
    exact ⟨u, huo, mem_units S x z hu⟩
  have hpp : ∀ o ∈ O, src S (arcOf S o) = (o.2.1.1, o.2.1.2.1) ∧
      tgt S (arcOf S o) = (o.2.2.1, !o.2.2.2.1) ∧
      (∀ q, projP S (arcOf S o) q = tP S x o.1 q) ∧
      (∀ j, projV S (arcOf S o) j = tV S z o.1 j) := by
    intro o ho
    obtain ⟨u, huo, hu⟩ := hunit o ho
    refine piece_props S x z ?_ huo
    rcases hu with ⟨p, -, rfl⟩ | ⟨k, -, rfl⟩
    · exact Or.inl ⟨p, rfl⟩
    · exact Or.inr ⟨k, rfl⟩
  have htag : ∀ g : Tag S → ℤ, (O.map (fun o => g o.1)).sum = (M.map (fun o => g o.1)).sum := by
    intro g
    rw [Rel.map_eq_of_flip_inv hrel (fun o => g o.1) (fun u _ => rfl)]
  have hsc : ∀ j, (O.map (sc S j)).sum = 0 := by
    intro j
    rw [Rel.map_eq_of_flip_inv hrel (sc S j) (fun u _ => by
      simp only [sc, EulerOrient.flip]; ring), hMdef, sum_sc_units S x z hz j, hker j]
  have hdg : ∀ j, (O.map (dg S j)).sum = (M.map (dg S j)).sum := by
    intro j
    rw [Rel.map_eq_of_flip_inv hrel (dg S j) (fun u _ => by
      simp only [dg, EulerOrient.flip]; ring)]
  have hE1 : ∀ j, (O.map (fun o => rowI j o.2.1 - rowI j o.2.2)).sum = 0 := by
    intro j
    have := hbal j
    unfold outC inC at this
    have h' := congrArg (fun n : ℕ => (n : ℤ)) this
    simp only [countP_eq_sum_map] at h'
    rw [Multiset.sum_map_sub, sub_eq_zero]
    exact h'
  set f : Arc S → ℕ := fun α => O.countP (fun o => arcOf S o = α) with hf
  refine ⟨f, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- circulación
    rintro ⟨j, s⟩
    unfold flowAt
    try simp only [hf]
    rw [sum_filter_countP, sum_filter_countP]
    apply Nat.cast_injective (R := ℤ)
    try simp only
    rw [countP_eq_sum_map, countP_eq_sum_map]
    have hT : O.map (fun o => if tgt S (arcOf S o) = (j, s) then (1 : ℤ) else 0) =
        O.map (fun o => if (o.2.2.1, !o.2.2.2.1) = (j, s) then 1 else 0) :=
      Multiset.map_congr rfl (fun o ho => by rw [(hpp o ho).2.1])
    have hS : O.map (fun o => if src S (arcOf S o) = (j, s) then (1 : ℤ) else 0) =
        O.map (fun o => if (o.2.1.1, o.2.1.2.1) = (j, s) then 1 else 0) :=
      Multiset.map_congr rfl (fun o ho => by rw [(hpp o ho).1])
    rw [hT, hS]
    have key := congrArg Multiset.sum (Multiset.map_congr (s := O) rfl
      (fun o _ => circ_eq S j s o))
    rw [Multiset.sum_map_mul_left, Multiset.sum_map_sub, Multiset.sum_map_add, hE1 j,
      Multiset.sum_map_mul_left, hsc j] at key
    linarith
  · -- proyección física
    funext q
    unfold flowP
    try simp only [hf]
    rw [sum_countP_mul O (arcOf S) (fun α => projP S α q),
      Multiset.map_congr rfl (fun o ho => (hpp o ho).2.2.1 q), htag (fun t => tP S x t q),
      hMdef, sum_map_units]
    simp only [unitP, unitV, tP, mul_zero, Finset.sum_const_zero, add_zero, mul_ite]
    rw [Finset.sum_ite_eq']
    simp [abs_mul_sgn_posB]
  · -- proyección virtual
    funext j
    unfold flowV
    try simp only [hf]
    rw [sum_countP_mul O (arcOf S) (fun α => projV S α j),
      Multiset.map_congr rfl (fun o ho => (hpp o ho).2.2.2 j), htag (fun t => tV S z t j),
      hMdef, sum_map_units]
    simp only [unitP, unitV, tV, mul_zero, Finset.sum_const_zero, zero_add]
    have : ∀ k : VRow S, ((z k.1).natAbs : ℤ) * (if k.1 = j then sgn (posB (z j)) else 0) =
        if k.1 = j then z j else 0 := by
      intro k
      split_ifs with h
      · subst h; rw [Int.natCast_natAbs]; exact abs_mul_sgn_posB _
      · simp
    rw [Finset.sum_congr rfl (fun k _ => this k)]
    exact sum_vrow_ite S j _ (hz j)
  · -- masa
    have h1 := sum_countP_mul O (arcOf S) (fun _ => (1 : ℤ)) (d := fun b => inferInstance)
    simp only [mul_one] at h1
    push_cast
    try simp only [hf]
    rw [h1, htag (fun _ => 1), hMdef, sum_map_units]
    simp only [mul_one, Int.natCast_natAbs]
    rw [← sum_vrow_abs S z hz]
    simp
  · -- ocurrencias por fila
    intro j
    unfold flowAt
    try simp only [hf]
    rw [sum_filter_countP, sum_filter_countP]
    push_cast
    rw [countP_eq_sum_map, countP_eq_sum_map, ← Multiset.sum_map_add]
    have hS : O.map (fun o => (if src S (arcOf S o) = (j, true) then (1 : ℤ) else 0) +
        (if src S (arcOf S o) = (j, false) then (1 : ℤ) else 0)) =
        O.map (fun o => rowI j o.2.1) :=
      Multiset.map_congr rfl (fun o ho => by rw [(hpp o ho).1]; exact row_eq S j o)
    rw [hS]
    have h1 : 2 * (O.map (fun o => rowI j o.2.1)).sum = (O.map (dg S j)).sum := by
      have := hE1 j
      rw [Multiset.sum_map_sub] at this
      unfold dg
      rw [Multiset.sum_map_add]
      linarith
    rw [h1, hdg j, hMdef, sum_map_units]
    congr 1
    · refine Finset.sum_congr rfl fun p _ => ?_
      simp only [dg, rowI, unitP, mul_add, Int.natCast_natAbs]
      by_cases h1 : S.r1 p = j <;> by_cases h2 : S.r2 p = j <;> simp [h1, h2]
    · have : ∀ k : VRow S, ((z k.1).natAbs : ℤ) * dg S j (unitV S z k) =
          if k.1 = j then 2 * |z j| else 0 := by
        intro k
        simp only [dg, rowI, unitV]
        split_ifs with h
        · subst h; simp; ring
        · simp [h]
      rw [Finset.sum_congr rfl (fun k _ => this k)]
      exact sum_vrow_ite S j _ (fun h => by rw [hz j h]; simp)
  · -- conformidad
    intro α hα
    obtain ⟨o, ho, rfl⟩ := Multiset.countP_pos.mp hα
    obtain ⟨u, huo, hu⟩ := hunit o ho
    have h1 : o.1 = u.1 := by rcases huo with rfl | rfl <;> rfl
    refine ⟨fun q => ?_, fun j => ?_⟩
    · rw [(hpp o ho).2.2.1 q, h1]
      rcases hu with ⟨p, hp, rfl⟩ | ⟨k, -, rfl⟩
      · simp only [unitP, tP]
        split_ifs with hpq
        · subst hpq; exact Or.inr (sgn_posB_mul_pos hp)
        · exact Or.inl rfl
      · exact Or.inl rfl
    · rw [(hpp o ho).2.2.2 j, h1]
      rcases hu with ⟨p, -, rfl⟩ | ⟨k, hk, rfl⟩
      · exact Or.inl rfl
      · simp only [unitV, tV]
        split_ifs with hkj
        · subst hkj; exact Or.inr (sgn_posB_mul_pos hk)
        · exact Or.inl rfl


omit [Fintype R] [Fintype P] in
lemma sum_list_ind_mul {E : Type*} [Fintype E] (L : List (Finset E)) (h : E → ℤ) :
    ∑ e, (((L.map (fun C => Circulation.ind C e)).sum : ℕ) : ℤ) * h e =
      (L.map (fun C => ∑ e, ((Circulation.ind C e : ℕ) : ℤ) * h e)).sum := by
  induction L with
  | nil => simp
  | cons C L ih =>
    simp only [List.map_cons, List.sum_cons, Nat.cast_add, add_mul, Finset.sum_add_distrib, ih]

/-- **Descomposición en ciclos de la cubierta (S26 §4).** Para `(x, z)` en el núcleo
aumentado (con `z` soportado en las filas virtuales) existe una lista finita de ciclos
simples de la cubierta aumentada tal que:
* cada ciclo se proyecta al núcleo aumentado;
* las proyecciones suman exactamente `x` (físicas) y `z` (virtuales): pertenencia entera,
  sin saturación racional;
* la longitud total es `‖x‖₁ + ‖z‖₁`;
* en cada fila, el doble del número de pasos de los ciclos por sus dos estados es el
  número de semiaristas de la fila;
* es conforme: cada arco usado tiene proyección del signo de la coordenada (en
  particular no hay retrocesos que cancelen). -/
theorem exists_cover_cycle_decomp (hz : ∀ j, S.nb j = false → z j = 0)
    (hker : ∀ j, baug S x z j = 0) :
    ∃ L : List (Finset (Arc S)),
      (∀ C ∈ L, IsSimpleCycle (src S) (tgt S) C) ∧
      (∀ C ∈ L, ∀ j, baug S (flowP S (Circulation.ind C)) (flowV S (Circulation.ind C)) j = 0) ∧
      (∀ q, (L.map (fun C => flowP S (Circulation.ind C) q)).sum = x q) ∧
      (∀ j, (L.map (fun C => flowV S (Circulation.ind C) j)).sum = z j) ∧
      (((L.map Finset.card).sum : ℕ) : ℤ) = ∑ p, |x p| + ∑ j, |z j| ∧
      (∀ j, 2 * ((L.countP (fun C => (j, true) ∈ C.image (src S)) +
          L.countP (fun C => (j, false) ∈ C.image (src S)) : ℕ) : ℤ) =
        ∑ p, ((if S.r1 p = j then |x p| else 0) + (if S.r2 p = j then |x p| else 0)) +
          2 * |z j|) ∧
      ∀ C ∈ L, ∀ α ∈ C, (∀ q, projP S α q = 0 ∨ 0 < projP S α q * x q) ∧
        (∀ j, projV S α j = 0 ∨ 0 < projV S α j * z j) := by
  obtain ⟨f, hcirc, hP, hV, hmass, hrow, hconf⟩ := exists_lift_circulation S x z hz hker
  obtain ⟨L, hL, hsum, hcard, hocc⟩ := exists_cycle_decomp_counts (src S) (tgt S) f hcirc
  refine ⟨L, hL, fun C hC j => baug_cycle_eq_zero S (hL C hC) j, fun q => ?_, fun j => ?_,
    ?_, fun j => ?_, fun C hC α hα => hconf α ?_⟩
  · rw [← congrFun hP q]
    unfold flowP
    rw [Finset.sum_congr rfl (fun α _ => by rw [hsum α]), sum_list_ind_mul]
  · rw [← congrFun hV j]
    unfold flowV
    rw [Finset.sum_congr rfl (fun α _ => by rw [hsum α]), sum_list_ind_mul]
  · rw [← hcard, hmass]
  · have := hrow j
    rw [hocc, hocc] at this
    convert this
  · rw [hsum α]
    have h1 : Circulation.ind C α = 1 := by simp [Circulation.ind, hα]
    have h2 : Circulation.ind C α ≤ (L.map (fun C => Circulation.ind C α)).sum :=
      List.le_sum_of_mem (List.mem_map.mpr ⟨C, hC, rfl⟩)
    omega


omit [Fintype R] in
/-- Cota (2) de S26: `2 |z_j|` es a lo sumo la masa física incidente en la fila `j`. -/
lemma two_abs_z_le {j : R} (hj : baug S x z j = 0) :
    2 * |z j| ≤ ∑ p, ((if S.r1 p = j then |x p| else 0) + (if S.r2 p = j then |x p| else 0)) := by
  unfold baug at hj
  have h2 : 2 * z j = ∑ p, ((if S.r1 p = j then sgn (S.a1 p) * x p else 0) +
      (if S.r2 p = j then sgn (S.a2 p) * x p else 0)) := by linarith
  have hsgn : ∀ b : Bool, |sgn b| = 1 := fun b => by cases b <;> simp [sgn]
  calc 2 * |z j| = |2 * z j| := by rw [abs_mul]; norm_num
    _ = |∑ p, ((if S.r1 p = j then sgn (S.a1 p) * x p else 0) +
          (if S.r2 p = j then sgn (S.a2 p) * x p else 0))| := by rw [h2]
    _ ≤ ∑ p, |(if S.r1 p = j then sgn (S.a1 p) * x p else 0) +
          (if S.r2 p = j then sgn (S.a2 p) * x p else 0)| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ _ := by
      refine Finset.sum_le_sum fun p _ => (abs_add_le _ _).trans ?_
      apply add_le_add <;> split_ifs <;> simp [abs_mul, hsgn]

/-- **Descomposición en ciclos con presupuesto por raíz física (S26 §4).** Además de
`exists_cover_cycle_decomp`: `‖z‖₁ ≤ ‖x‖₁` y, para toda asignación `ρ` de filas a raíces
físicas, el número total de posiciones de ciclos sobre las filas (y ambos estados) de
la raíz `v` es a lo sumo la masa de `x` en las columnas con un extremo en `v`. -/
theorem exists_cover_cycle_decomp_roots {W : Type*} (ρ : R → W)
    (hz : ∀ j, S.nb j = false → z j = 0) (hker : ∀ j, baug S x z j = 0) :
    ∃ L : List (Finset (Arc S)),
      (∀ C ∈ L, IsSimpleCycle (src S) (tgt S) C) ∧
      (∀ C ∈ L, ∀ j, baug S (flowP S (Circulation.ind C)) (flowV S (Circulation.ind C)) j = 0) ∧
      (∀ q, (L.map (fun C => flowP S (Circulation.ind C) q)).sum = x q) ∧
      (∀ j, (L.map (fun C => flowV S (Circulation.ind C) j)).sum = z j) ∧
      (((L.map Finset.card).sum : ℕ) : ℤ) = ∑ p, |x p| + ∑ j, |z j| ∧
      ∑ j, |z j| ≤ ∑ p, |x p| ∧
      (∀ v, ((∑ j ∈ univ.filter (fun j => ρ j = v),
          (L.countP (fun C => (j, true) ∈ C.image (src S)) +
            L.countP (fun C => (j, false) ∈ C.image (src S))) : ℕ) : ℤ) ≤
        ∑ p, |x p| * ((if ρ (S.r1 p) = v then 1 else 0) + (if ρ (S.r2 p) = v then 1 else 0))) ∧
      ∀ C ∈ L, ∀ α ∈ C, (∀ q, projP S α q = 0 ∨ 0 < projP S α q * x q) ∧
        (∀ j, projV S α j = 0 ∨ 0 < projV S α j * z j) := by
  obtain ⟨L, h1, h2, h3, h4, h5, h6, h7⟩ := exists_cover_cycle_decomp S x z hz hker
  have hrowle : ∀ j, ((L.countP (fun C => (j, true) ∈ C.image (src S)) +
      L.countP (fun C => (j, false) ∈ C.image (src S)) : ℕ) : ℤ) ≤
      ∑ p, ((if S.r1 p = j then |x p| else 0) + (if S.r2 p = j then |x p| else 0)) := by
    intro j
    have := h6 j
    have := two_abs_z_le S x z (hker j)
    linarith
  refine ⟨L, h1, h2, h3, h4, h5, ?_, fun v => ?_, h7⟩
  · have hsum : ∑ j, 2 * |z j| ≤ ∑ j, ∑ p, ((if S.r1 p = j then |x p| else 0) +
        (if S.r2 p = j then |x p| else 0)) :=
      Finset.sum_le_sum fun j _ => two_abs_z_le S x z (hker j)
    rw [Finset.sum_comm] at hsum
    simp only [Finset.sum_add_distrib, Finset.sum_ite_eq, Finset.mem_univ, if_true,
      ← Finset.mul_sum] at hsum
    linarith
  · push_cast
    calc _ ≤ ∑ j ∈ univ.filter (fun j => ρ j = v), ∑ p, ((if S.r1 p = j then |x p| else 0) +
          (if S.r2 p = j then |x p| else 0)) := Finset.sum_le_sum fun j _ => by
            have := hrowle j; push_cast at this; exact this
      _ = _ := by
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun p _ => ?_
        rw [Finset.sum_add_distrib, Finset.sum_ite_eq, Finset.sum_ite_eq]
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        split_ifs <;> ring

end TypedTriangle.SignedCover
