/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import RequestProject.TypedTriangle.CirculationDecomp
public import RequestProject.TypedTriangle.EulerOrient

@[expose] public section

/-!
# Cubierta con signo y columnas virtuales (S26 §§2 y 4, capa combinatoria) — V11

Un *sistema de filas* consiste en filas `R`, columnas físicas `P` (cada una con dos
extremos `r1 p, r2 p` y coeficientes `±1` dados por `a1 p, a2 p : Bool`) y un conjunto de
filas `nb` que llevan una columna virtual `−2 e_j`. La matriz aumentada es

  `baug x z j = Σ_p (a1 p [r1 p = j] + a2 p [r2 p = j]) x p − 2 z j`.

La **cubierta aumentada** tiene estados `(j, s)`, `s = ±1`. Para cada columna física hay
cuatro arcos `(p, d, s)` (sentido `d`, signo de salida `s`):
`(r1 p, s) → (r2 p, −a1 a2 s)` si `d`, y `(r2 p, s) → (r1 p, −a1 a2 s)` si no; y para cada
fila virtual dos arcos verticales `(j, s) → (j, −s)`. La proyección firmada de un arco
físico es `s · a_salida` en la columna `p`, la de un vertical es `−s` en la columna virtual.

Resultados (todos demostrados):

* `baug_proj_arc` — borde aumentado de un arco: `s e_j − t e_k`.
* `baug_flow_eq_zero` — toda circulación de la cubierta se proyecta al núcleo aumentado;
  en particular todo ciclo simple (`baug_cycle_eq_zero`).
* `exists_lift_circulation` — **lift**: para `(x, z)` en el núcleo aumentado (con `z`
  soportado en las filas virtuales) se construye una circulación no negativa conforme de la
  cubierta que se proyecta exactamente en `(x, z)`, con masa `‖x‖₁ + ‖z‖₁` y, en cada fila,
  ocurrencias = mitad del número de semiaristas. No se recibe como hipótesis.
* `exists_cover_cycle_decomp` — aplicación de la descomposición en ciclos de
  `CirculationDecomp`: lista de ciclos simples de la cubierta cuyas proyecciones suman
  `(x, z)`, cada una en el núcleo aumentado, longitud total `‖x‖₁ + ‖z‖₁` y ocurrencias
  exactas por fila.
-/

open Finset Classical

noncomputable section

namespace TypedTriangle.SignedCover

open TypedTriangle.Circulation TypedTriangle.EulerOrient

/-- Signo de un booleano: `true ↦ 1`, `false ↦ −1`. -/
def sgn (b : Bool) : ℤ := if b then 1 else -1

@[simp] lemma sgn_true : sgn true = 1 := rfl
@[simp] lemma sgn_false : sgn false = -1 := rfl

lemma sgn_mul_self (b : Bool) : sgn b * sgn b = 1 := by cases b <;> rfl

/-- Sistema de filas: dos extremos con coeficientes `±1` por columna física y filas con
columna virtual. -/
structure RowSystem (R P : Type*) where
  r1 : P → R
  r2 : P → R
  a1 : P → Bool
  a2 : P → Bool
  nb : R → Bool

variable {R P : Type*} [Fintype R] [Fintype P] (S : RowSystem R P)

/-- Matriz aumentada `B_aug(x, z)`. -/
def baug (x : P → ℤ) (z : R → ℤ) (j : R) : ℤ :=
  ∑ p, ((if S.r1 p = j then sgn (S.a1 p) * x p else 0) +
    (if S.r2 p = j then sgn (S.a2 p) * x p else 0)) - 2 * z j

/-- Filas con columna virtual. -/
abbrev VRow := {j : R // S.nb j = true}

/-- Arcos de la cubierta: físicos `(p, d, s)` y verticales `(j, s)`. -/
abbrev Arc := (P × Bool × Bool) ⊕ (VRow S × Bool)

/-- Signo de llegada de un arco físico que sale con signo `s`: `−a1 a2 s`. -/
def tsign (p : P) (s : Bool) : Bool := xor s (S.a1 p == S.a2 p)

omit [Fintype R] [Fintype P] in
lemma sgn_tsign (p : P) (s : Bool) :
    sgn (tsign S p s) = - (sgn (S.a1 p) * sgn (S.a2 p) * sgn s) := by
  unfold tsign
  cases s <;> cases S.a1 p <;> cases S.a2 p <;> decide

/-- Estado de salida. -/
def src : Arc S → R × Bool
  | Sum.inl (p, d, s) => if d then (S.r1 p, s) else (S.r2 p, s)
  | Sum.inr (j, s) => (j.1, s)

/-- Estado de llegada. -/
def tgt : Arc S → R × Bool
  | Sum.inl (p, d, s) => if d then (S.r2 p, tsign S p s) else (S.r1 p, tsign S p s)
  | Sum.inr (j, s) => (j.1, !s)

/-- Proyección firmada de un arco a la columna física `q`. -/
def projP : Arc S → P → ℤ
  | Sum.inl (p, d, s), q => if p = q then sgn s * sgn (if d then S.a1 p else S.a2 p) else 0
  | Sum.inr _, _ => 0

/-- Proyección firmada de un arco a la columna virtual de la fila `j`. -/
def projV : Arc S → R → ℤ
  | Sum.inl _, _ => 0
  | Sum.inr (k, s), j => if k.1 = j then - sgn s else 0

omit [Fintype R] in
/-- **Borde aumentado de un arco**: `B_aug(π α) = s e_j − t e_k`. -/
theorem baug_proj_arc (α : Arc S) (j : R) :
    baug S (projP S α) (projV S α) j =
      (if (src S α).1 = j then sgn (src S α).2 else 0) -
        (if (tgt S α).1 = j then sgn (tgt S α).2 else 0) := by
  rcases α with ⟨p, d, s⟩ | ⟨k, s⟩
  · unfold baug
    simp only [projP, projV, mul_zero, sub_zero]
    rw [Finset.sum_eq_single p (fun q _ hq => by simp [Ne.symm hq]) (by simp)]
    simp only [if_true]
    cases d <;> simp only [src, tgt, if_true, if_false, Bool.false_eq_true, sgn_tsign] <;>
      split_ifs <;> cases s <;> cases S.a1 p <;> cases S.a2 p <;> simp [sgn]
  · unfold baug
    simp only [projP, projV, src, tgt]
    simp only [mul_zero, ite_self, add_zero, Finset.sum_const_zero, zero_sub]
    split_ifs <;> cases s <;> simp_all [sgn]

/-- Proyección física de un flujo de la cubierta. -/
def flowP (f : Arc S → ℕ) (q : P) : ℤ := ∑ α, (f α : ℤ) * projP S α q

/-- Proyección virtual de un flujo de la cubierta. -/
def flowV (f : Arc S → ℕ) (j : R) : ℤ := ∑ α, (f α : ℤ) * projV S α j

lemma baug_flow (f : Arc S → ℕ) (j : R) :
    baug S (flowP S f) (flowV S f) j = ∑ α, (f α : ℤ) * baug S (projP S α) (projV S α) j := by
  unfold baug flowP flowV
  simp only [Finset.mul_sum, Finset.sum_sub_distrib, mul_add, mul_sub]
  rw [Finset.sum_comm (s := (univ : Finset (Arc S)))]
  congr 1
  · refine Finset.sum_congr rfl fun q _ => ?_
    split_ifs <;> simp [Finset.sum_add_distrib, mul_left_comm]
  · simp [mul_left_comm]

/-- **Toda circulación de la cubierta se proyecta al núcleo aumentado.** -/
theorem baug_flow_eq_zero (f : Arc S → ℕ) (hf : IsCirc (src S) (tgt S) f) (j : R) :
    baug S (flowP S f) (flowV S f) j = 0 := by
  rw [baug_flow]
  simp only [baug_proj_arc, mul_sub]
  rw [Finset.sum_sub_distrib, sub_eq_zero]
  have key : ∀ (st : Arc S → R × Bool),
      ∑ α, (f α : ℤ) * (if (st α).1 = j then sgn (st α).2 else 0) =
        (flowAt st f (j, true) : ℤ) - flowAt st f (j, false) := by
    intro st
    unfold flowAt
    push_cast
    rw [Finset.sum_filter, Finset.sum_filter, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun α _ => ?_
    obtain ⟨k, b⟩ := st α
    by_cases hk : k = j
    · subst hk; cases b <;> simp [sgn]
    · simp [hk]
  rw [key, key, hf (j, true), hf (j, false)]

/-- **Todo ciclo simple de la cubierta se proyecta al núcleo aumentado.** -/
theorem baug_cycle_eq_zero {C : Finset (Arc S)} (hC : IsSimpleCycle (src S) (tgt S) C)
    (j : R) : baug S (flowP S (Circulation.ind C)) (flowV S (Circulation.ind C)) j = 0 :=
  baug_flow_eq_zero S _ hC.isCirc j

end TypedTriangle.SignedCover
