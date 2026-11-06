/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import RequestProject.TypedTriangle.ZigzagGlobal

@[expose] public section

/-!
# Presupuesto de enrutamiento: caminos diagonales con congestión acotada (V13, S26 §5, C)

Los caminos diagonales se CONSTRUYEN secuencialmente (no se recibe una selección de caminos
como premisa). Se mantiene una carga `a(v)` por vértice físico: un camino para la diagonal
de extremos `X, Y` carga `2` por cada estado del camino con raíz `v`, salvo si `v` es la
raíz física de `X` o de `Y` (esas visitas se cargan a las incidencias de los extremos, es
decir, a los vértices del polígono). Varios estados pueden tener la misma raíz: se cuentan
todas las visitas (`List.countP`), nunca raíces distintas.

Antes de cada diagonal se prohíben los vértices saturados (`a(v) ≥ q`) salvo las dos raíces de
los extremos; el borrado preparado (`DeletionHyp` para todo conjunto de tamaño `≤ m`) y
`surv_dist_lt` de V12 dan un camino de longitud `≤ D` en la cubierta superviviente.

* `route_one` — un paso: con `Σ a < q(m+1)` hay a lo sumo `m` saturados; el camino nuevo sólo
  carga vértices no saturados y añade `≤ 2(D-1)` a cada uno y `≤ 2D` en total.
* `route_cycles` — todas las diagonales de todos los ciclos; carga final `< q + 2D`.
* `routing_budget` — **resultado final de la parte C** (condicional a la preparación):
  celdas con signo como en la parte B y, para cada vértice físico `v`,
  `#{i : v ∈ supp b_i} < 3·d_abs(x)(v) + q + 2D`; en particular `≤ (4D+3)·d_abs(x)(v) + q + 2D`.
* `routing_budget_real` — la misma conclusión con `q = ⌈32De/(δn)⌉`, `e = ‖x‖₁ > 0`,
  `δ > 0`, `Cδ ≤ 4`, y borrado preparado para todo conjunto de tamaño `≤ δn`.
-/

open Finset Classical

noncomputable section

namespace TypedTriangle.ActiveCover

open TypedTriangle.ComponentRows TypedTriangle.SignedCover TypedTriangle.Circulation
open TypedTriangle.Zigzag

variable {V I : Type*} [Fintype V] {G : SimpleGraph V} {lab : V → I} {F : Set (Multiset I)}

/-- Carga de un camino `w` de la diagonal con extremos `X, Y` en el vértice físico `v`:
número de visitas de `w` a estados de raíz `v`, salvo si `v` es raíz de un extremo. -/
def charge (X Y : St V) (w : List (St V)) (v : V) : ℕ :=
  if X.1.1 = v ∨ Y.1.1 = v then 0 else w.countP (fun Z => Z.1.1 = v)

lemma sum_countP_root (w : List (St V)) (Q : V → Prop) [DecidablePred Q] :
    ∑ v, w.countP (fun Z => decide (Z.1.1 = v ∧ Q v)) = w.countP (fun Z => decide (Q Z.1.1)) := by
  induction w with
  | nil => simp
  | cons Z w ih =>
    simp only [List.countP_cons, Finset.sum_add_distrib, ih]
    congr 1
    by_cases hQ : Q Z.1.1
    · rw [Finset.sum_eq_single Z.1.1 (fun b _ hb => by simp [Ne.symm hb]) (by simp)]
      simp [hQ]
    · rw [Finset.sum_eq_zero (fun b _ => ?_)]
      · simp [hQ]
      · by_cases hb : Z.1.1 = b
        · subst hb; simp [hQ]
        · simp [hb]

omit [Fintype V] in
lemma countP_le_length_sub_two {P : St V → Prop} [DecidablePred P] {X Y : St V}
    {w : List (St V)}
    (h1 : w.head? = some X) (h2 : w.getLast? = some Y) (hX : ¬ P X) (hY : ¬ P Y) :
    w.countP (fun Z => decide (P Z)) ≤ w.length - 2 := by
  cases w with
  | nil => simp
  | cons a t =>
    simp only [List.head?_cons, Option.some.injEq] at h1
    subst h1
    rw [List.countP_cons, if_neg (by simpa using hX), add_zero, List.length_cons]
    rcases List.eq_nil_or_concat t with rfl | ⟨t', b, rfl⟩
    · simp
    · rw [List.concat_eq_append] at h2 ⊢
      have hb : b = Y := by
        rw [← List.cons_append, List.getLast?_concat] at h2
        simpa using h2
      subst hb
      rw [List.countP_append, List.countP_singleton, if_neg (by simpa using hY), add_zero,
        List.length_append, List.length_singleton]
      exact (List.countP_le_length).trans (by omega)

/-- Masa total de la carga de un camino: a lo sumo `longitud − 2` (sin los extremos). -/
lemma sum_charge_le {X Y : St V} {w : List (St V)} (h1 : w.head? = some X)
    (h2 : w.getLast? = some Y) : ∑ v, charge X Y w v ≤ w.length - 2 := by
  have e1 : ∑ v, charge X Y w v =
      ∑ v, w.countP (fun Z => decide (Z.1.1 = v ∧ ¬ (X.1.1 = v ∨ Y.1.1 = v))) := by
    refine Finset.sum_congr rfl fun v _ => ?_
    unfold charge
    split_ifs with h
    · symm; rw [List.countP_eq_zero]; intro Z _; simp [h]
    · congr 1; funext Z; simp [h]
  rw [e1]
  refine le_of_eq_of_le (sum_countP_root w (fun v => ¬ (X.1.1 = v ∨ Y.1.1 = v))) ?_
  exact countP_le_length_sub_two (P := fun Z => ¬ (X.1.1 = Z.1.1 ∨ Y.1.1 = Z.1.1)) h1 h2
    (by simp) (by simp)

omit [Fintype V] in
lemma charge_le {X Y : St V} {w : List (St V)} (h1 : w.head? = some X)
    (h2 : w.getLast? = some Y) (v : V) : charge X Y w v ≤ w.length - 2 := by
  unfold charge
  split_ifs with h
  · exact Nat.zero_le _
  · push_neg at h
    exact countP_le_length_sub_two (P := fun Z => Z.1.1 = v) h1 h2 h.1 h.2

/-- Hipótesis preparadas del núcleo (las mismas de V12), con las constantes fijadas. -/
structure PreparedRouting (G : SimpleGraph V) (lab : V → I) (F : Set (Multiset I))
    (C m D : ℕ) : Prop where
  card_pos : 0 < Fintype.card V
  rows : ∀ v, (univ.filter (fun j : Row V => j.1 = v ∧ IsActiveRow G lab F j)).card ≤ C
  deg : ∀ j : Row V, IsActiveRow G lab F j → Fintype.card V ≤ C * j.2.card
  del : ∀ A : Finset V, A.card ≤ m → DeletionHyp G lab F A
  small : 2 * C * m ≤ Fintype.card V
  D_pos : 1 ≤ D
  D_ge : 12 * C ^ 2 ≤ D + 1

/-- **Un paso del enrutamiento.** -/
theorem route_one {C m D q : ℕ} (hP : PreparedRouting G lab F C m D) (a : V → ℕ)
    (ha : ∀ v, a v < q + 2 * D) (hmass : ∑ v, a v < q * (m + 1))
    (X Y : AState G lab F) (hXY : (stateGraph G lab F).Reachable X Y) :
    ∃ w : List (St V), IsStPath G lab F X.1 Y.1 w ∧ w.length ≤ D + 1 ∧
      (∀ v, a v + 2 * charge X.1 Y.1 w v < q + 2 * D) ∧
      ∑ v, 2 * charge X.1 Y.1 w v ≤ 2 * D := by
  set sat := univ.filter (fun v => q ≤ a v) with hsat
  have hsat_card : sat.card ≤ m := by
    have h1 : sat.card * q ≤ ∑ v, a v := by
      calc sat.card * q = ∑ v ∈ sat, q := by simp
        _ ≤ ∑ v ∈ sat, a v := Finset.sum_le_sum fun v hv => (mem_filter.mp hv).2
        _ ≤ ∑ v, a v := Finset.sum_le_sum_of_subset (subset_univ _)
    have hq : 0 < q := by
      rcases Nat.eq_zero_or_pos q with h | h
      · rw [h] at hmass; simp at hmass
      · exact h
    by_contra hc
    push_neg at hc
    have : q * (m + 1) ≤ sat.card * q := by rw [mul_comm]; exact Nat.mul_le_mul_right _ hc
    omega
  set A := sat \ {X.1.1.1, Y.1.1.1} with hA
  have hAcard : A.card ≤ m := (card_le_card sdiff_subset).trans hsat_card
  have hXA : X.1.1.1 ∉ A := by simp [hA]
  have hYA : Y.1.1.1 ∉ A := by simp [hA]
  obtain ⟨hr, hd⟩ := surv_dist_lt (hP.del A hAcard) C hP.card_pos hP.rows hP.deg
    ((Nat.mul_le_mul_left _ hAcard).trans hP.small) hXA hYA hXY
  obtain ⟨wW, hwW⟩ := hr.exists_walk_length_eq_dist
  have hpath := walk_isStPath (G := G) (lab := lab) (F := F) (H := survGraph G lab F A)
    (fun a b h => h) wW
  set w := wW.support.map Subtype.val with hw
  have hp1 : IsStPath G lab F X.1 Y.1 w := hpath.1
  have hp2 : w.length = wW.length + 1 := hpath.2
  have hgood : ∀ Z ∈ w, Z.1.1 ∉ A := by
    intro Z hZ
    obtain ⟨z, -, rfl⟩ := List.mem_map.mp hZ
    exact z.2.2
  have hlen : w.length ≤ D + 1 := by
    rw [hp2, hwW]; have := hP.D_ge; omega
  refine ⟨w, hp1, hlen, fun v => ?_, ?_⟩
  · by_cases hc : charge X.1 Y.1 w v = 0
    · rw [hc]; simpa using ha v
    · have hcle := charge_le hp1.1 hp1.2.1 v
      unfold charge at hc
      split_ifs at hc with hend
      · exact absurd rfl hc
      · obtain ⟨Z, hZ, hZv⟩ := List.countP_pos_iff.mp (Nat.pos_of_ne_zero hc)
        simp only [decide_eq_true_eq] at hZv
        have hvA : v ∉ A := hZv ▸ hgood Z hZ
        have hvsat : v ∉ sat := by
          intro hv
          push_neg at hend
          exact hvA (by simp [hA, hv, Ne.symm hend.1, Ne.symm hend.2])
        have hav : a v < q := by simpa [hsat] using hvsat
        omega
  · rw [← Finset.mul_sum]
    have := sum_charge_le hp1.1 hp1.2.1
    omega

/-- Carga total de las diagonales de índice en `S` de un ciclo con caminos `dw`. -/
def cycCharge (c : OrdCycle G lab F) (dw : ℕ → List (St V)) (S : Finset ℕ) (v : V) : ℕ :=
  ∑ i ∈ S, 2 * charge (c.st (lo i)) (c.st (hi c.arcs.length i)) (dw i) v

/-- **Enrutamiento de las diagonales de un ciclo** (inducción sobre el conjunto de índices). -/
theorem route_diags {C m D q : ℕ} (hP : PreparedRouting G lab F C m D) (c : OrdCycle G lab F)
    (hact : ∀ i, IsActiveRow G lab F (c.st i).1) (S : Finset ℕ)
    (hS : S ⊆ Icc 1 (c.arcs.length - 3)) (a : V → ℕ) (ha : ∀ v, a v < q + 2 * D)
    (hmass : ∑ v, a v + 2 * D * S.card < q * (m + 1)) :
    ∃ dw : ℕ → List (St V),
      (∀ i ∈ S, IsStPath G lab F (c.st (lo i)) (c.st (hi c.arcs.length i)) (dw i) ∧
        (dw i).length ≤ D + 1) ∧
      (∀ v, a v + cycCharge c dw S v < q + 2 * D) ∧
      ∑ v, (a v + cycCharge c dw S v) ≤ ∑ v, a v + 2 * D * S.card := by
  induction S using Finset.induction_on with
  | empty => exact ⟨fun _ => [], by simp, by simpa [cycCharge] using ha, by simp [cycCharge]⟩
  | insert j S hj ih =>
    have hS' : S ⊆ Icc 1 (c.arcs.length - 3) := (subset_insert _ _).trans hS
    rw [card_insert_of_notMem hj, Nat.mul_add, mul_one] at hmass
    obtain ⟨dw, hdw1, hdw2, hdw3⟩ := ih hS' (by omega)
    have hm1 : ∑ v, (a v + cycCharge c dw S v) < q * (m + 1) := by omega
    obtain ⟨w, hw1, hw2, hw3, hw4⟩ := route_one hP (fun v => a v + cycCharge c dw S v) hdw2 hm1
      ⟨c.st (lo j), hact _⟩ ⟨c.st (hi c.arcs.length j), hact _⟩ (c.reachable hact _ _)
    have hw3' : ∀ v, a v + cycCharge c dw S v +
        2 * charge (c.st (lo j)) (c.st (hi c.arcs.length j)) w v < q + 2 * D := hw3
    have hw4' : ∑ v, 2 * charge (c.st (lo j)) (c.st (hi c.arcs.length j)) w v ≤ 2 * D := hw4
    have hupd : ∀ i ∈ S, Function.update dw j w i = dw i := fun i hi =>
      Function.update_of_ne (fun h : i = j => hj (h ▸ hi)) _ _
    have hcc : ∀ v, cycCharge c (Function.update dw j w) (insert j S) v =
        2 * charge (c.st (lo j)) (c.st (hi c.arcs.length j)) w v + cycCharge c dw S v := by
      intro v
      unfold cycCharge
      rw [Finset.sum_insert hj, Function.update_self]
      congr 1
      exact Finset.sum_congr rfl fun i hi => by rw [hupd i hi]
    refine ⟨Function.update dw j w, fun i hi => ?_, fun v => ?_, ?_⟩
    · rcases mem_insert.mp hi with rfl | hi
      · rw [Function.update_self]; exact ⟨hw1, hw2⟩
      · rw [hupd i hi]; exact hdw1 i hi
    · rw [hcc]; have := hw3' v; omega
    · simp only [hcc]
      have e : ∀ v, a v + (2 * charge (c.st (lo j)) (c.st (hi c.arcs.length j)) w v +
          cycCharge c dw S v) = (a v + cycCharge c dw S v) +
          2 * charge (c.st (lo j)) (c.st (hi c.arcs.length j)) w v := fun v => by ring
      simp only [e, Finset.sum_add_distrib] at hdw3 hw4' ⊢
      rw [card_insert_of_notMem hj, Nat.mul_add, mul_one]
      omega

/-- **Enrutamiento de todas las diagonales de todos los ciclos.** -/
theorem route_cycles {C m D q : ℕ} (hP : PreparedRouting G lab F C m D)
    (cs : List (OrdCycle G lab F)) (hact : ∀ c ∈ cs, ∀ i, IsActiveRow G lab F (c.st i).1)
    (a : V → ℕ) (ha : ∀ v, a v < q + 2 * D)
    (hmass : ∑ v, a v + 2 * D * (cs.map (fun c => (Icc 1 (c.arcs.length - 3)).card)).sum < q * (m + 1)) :
    ∃ cd : List (OrdCycle G lab F × (ℕ → List (St V))), cd.map Prod.fst = cs ∧
      (∀ p ∈ cd, p.1.DiagSpec p.2 D) ∧
      (∀ v, a v + (cd.map (fun p => cycCharge p.1 p.2 (Icc 1 (p.1.arcs.length - 3)) v)).sum <
        q + 2 * D) ∧
      ∑ v, (a v + (cd.map (fun p => cycCharge p.1 p.2 (Icc 1 (p.1.arcs.length - 3)) v)).sum) ≤
        ∑ v, a v + 2 * D * (cs.map (fun c => (Icc 1 (c.arcs.length - 3)).card)).sum := by
  induction cs generalizing a with
  | nil => exact ⟨[], rfl, by simp, by simpa using ha, by simp⟩
  | cons c cs ih =>
    simp only [List.map_cons, List.sum_cons] at hmass ⊢
    rw [Nat.mul_add (2 * D)] at hmass ⊢
    obtain ⟨dw, hdw1, hdw2, hdw3⟩ := route_diags hP c (hact c (by simp)) _ subset_rfl a ha
      (by omega)
    obtain ⟨cd, hcd1, hcd2, hcd3, hcd4⟩ := ih (fun c' h => hact c' (List.mem_cons_of_mem _ h))
      (fun v => a v + cycCharge c dw (Icc 1 (c.arcs.length - 3)) v) hdw2 (by omega)
    refine ⟨(c, dw) :: cd, by simp [hcd1], fun p hp => ?_, fun v => ?_, ?_⟩
    · rcases List.mem_cons.mp hp with rfl | hp
      · intro i hi1 hi2; exact hdw1 i (mem_Icc.mpr ⟨hi1, hi2⟩)
      · exact hcd2 p hp
    · have := hcd3 v
      simp only [List.map_cons, List.sum_cons]
      omega
    · simp only [List.map_cons, List.sum_cons, ← add_assoc]
      omega

lemma chargedCount_le (p : OrdCycle G lab F × (ℕ → List (St V))) (v : V) :
    2 * chargedCount p v ≤ cycCharge p.1 p.2 (Icc 1 (p.1.arcs.length - 3)) v := by
  unfold chargedCount cycCharge
  rw [Finset.card_filter, Finset.mul_sum]
  refine Finset.sum_le_sum fun i _ => ?_
  split_ifs with h
  · obtain ⟨⟨Z, hZ, hZv⟩, h1, h2⟩ := h
    have : 1 ≤ charge (p.1.st (lo i)) (p.1.st (hi p.1.arcs.length i)) (p.2 i) v := by
      unfold charge
      rw [if_neg (by tauto)]
      exact List.countP_pos_iff.mpr ⟨Z, hZ, by simpa using hZv⟩
    omega
  · omega

/-- **S26 §5, parte C: enrutamiento con presupuesto (condicional a la preparación).**
Constantes fijadas antes: `C` (filas activas por raíz y tamaño de componentes), `m` (tamaño de
los conjuntos prohibidos con borrado preparado), `D` (longitud de los caminos, `12C² ≤ D+1`),
`q` (umbral de saturación) con `4D‖x‖₁ < q(m+1)`. Para todo perfil local `x` se CONSTRUYEN
caminos diagonales y celdas con signo tales que (además de las propiedades de la parte B)
para todo vértice físico `v`:
`#{i : v ∈ supp b_i} < 3·d_abs(x)(v) + q + 2D`. -/
theorem routing_budget (x : Sym2 V → ℤ) (hx : IsLocalProfile G lab F x) {C m D q : ℕ}
    (hP : PreparedRouting G lab F C m D) (hcap : 4 * D * norm1 G x < q * (m + 1)) :
    ∃ cells : List (Sym2 V → ℤ), (∀ b ∈ cells, IsLocalProfile G lab F b) ∧
      (∀ e, (cells.map (fun b => b e)).sum = x e) ∧
      (cells.length : ℤ) ≤ 2 * norm1 G x ∧
      (∀ b ∈ cells, norm1 G b ≤ 3 * D) ∧
      (cells.map (norm1 G)).sum ≤ 6 * D * norm1 G x ∧
      ∀ v, (cells.countP (fun b => decide (InSupp G v b)) : ℤ) < 3 * dabs G x v + q + 2 * D := by
  obtain ⟨cs, hs1, hs2, hs3, hs4⟩ := exists_ordCycles x hx
  set N := (cs.map (fun c => (Icc 1 (c.arcs.length - 3)).card)).sum with hN
  have hnd : N ≤ (cs.map (fun c => c.arcs.length)).sum :=
    List.sum_le_sum fun c _ => by simp
  have hNz : (N : ℤ) ≤ 2 * norm1 G x := (Nat.cast_le.mpr hnd).trans hs2
  have hmass : ∑ _v : V, (0 : ℕ) + 2 * D * N < q * (m + 1) := by
    simp only [Finset.sum_const_zero, zero_add]
    have h1 : (2 * D * N : ℤ) ≤ 4 * D * norm1 G x := by
      have hD0 : (0 : ℤ) ≤ D := by positivity
      nlinarith
    have : ((2 * D * N : ℕ) : ℤ) < ((q * (m + 1) : ℕ) : ℤ) := by
      push_cast; linarith
    exact_mod_cast this
  obtain ⟨cd, hcd1, hcd2, hcd3, -⟩ := route_cycles (q := q) hP cs hs3 (fun _ => 0)
    (fun v => by show 0 < q + 2 * D; have := hP.D_pos; omega) hmass
  have hcd_sum : ∀ e : Col G,
      (cd.map (fun p => flowP _ (Circulation.ind p.1.arcs.toFinset) e)).sum = x e.1 := by
    intro e
    rw [← hs1 e, ← hcd1, List.map_map]; rfl
  have hcd_len : (((cd.map (fun p => p.1.arcs.length)).sum : ℕ) : ℤ) ≤ 2 * norm1 G x := by
    rw [← hcd1, List.map_map] at hs2; exact hs2
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := cells_assembly x hx D hP.D_pos cd hcd_sum hcd_len hcd2
  refine ⟨_, h1, h2, h3, h4, h5, fun v => ?_⟩
  have hc := h6 v
  have hocc : (cd.map (fun p => occCount p.1 v)).sum = (cs.map (fun c =>
      ((range c.arcs.length).filter (fun p => (c.st p).1.1 = v)).card)).sum := by
    rw [← hcd1, List.map_map]; rfl
  have hch : (cd.map (fun p => 2 * chargedCount p v)).sum < q + 2 * D := by
    have := hcd3 v
    simp only [zero_add] at this
    exact lt_of_le_of_lt (List.sum_le_sum fun p _ => chargedCount_le p v) this
  have hsplit : (cd.map (fun p => 3 * occCount p.1 v + 2 * chargedCount p v)).sum =
      3 * (cd.map (fun p => occCount p.1 v)).sum + (cd.map (fun p => 2 * chargedCount p v)).sum := by
    rw [List.sum_map_add, List.sum_map_mul_left]
  rw [hsplit, hocc] at hc
  have h4' := hs4 v
  have : (((cd.flatMap cellsOf).countP (fun b => decide (InSupp G v b)) : ℕ) : ℤ) <
      3 * (((cs.map (fun c => ((range c.arcs.length).filter
        (fun p => (c.st p).1.1 = v)).card)).sum : ℕ) : ℤ) + q + 2 * D := by
    have := Nat.lt_of_le_of_lt hc (Nat.add_lt_add_left hch _)
    exact_mod_cast (show _ < _ from by omega)
  linarith

/-- La forma pedida: `#{i : v ∈ supp b_i} ≤ (4D+3)·d_abs(x)(v) + q + 2D`. -/
theorem routing_budget_weak (x : Sym2 V → ℤ) (hx : IsLocalProfile G lab F x) {C m D q : ℕ}
    (hP : PreparedRouting G lab F C m D) (hcap : 4 * D * norm1 G x < q * (m + 1)) :
    ∃ cells : List (Sym2 V → ℤ), (∀ b ∈ cells, IsLocalProfile G lab F b) ∧
      (∀ e, (cells.map (fun b => b e)).sum = x e) ∧
      (cells.length : ℤ) ≤ 2 * norm1 G x ∧
      (∀ b ∈ cells, norm1 G b ≤ 3 * D) ∧
      (cells.map (norm1 G)).sum ≤ 6 * D * norm1 G x ∧
      ∀ v, (cells.countP (fun b => decide (InSupp G v b)) : ℤ) ≤
        (4 * D + 3) * dabs G x v + q + 2 * D := by
  obtain ⟨cells, h1, h2, h3, h4, h5, h6⟩ := routing_budget x hx hP hcap
  refine ⟨cells, h1, h2, h3, h4, h5, fun v => ?_⟩
  have hd : 0 ≤ dabs G x v := Finset.sum_nonneg fun e _ => by split_ifs <;> simp
  have := h6 v
  nlinarith

/-- **Parte C con las constantes de S26**: `e = ‖x‖₁ > 0`, `δ > 0`, `n > 0`,
`q = ⌈32De/(δn)⌉`. Se usa el borrado preparado para todo conjunto físico de tamaño `≤ δn`
y `Cδ ≤ 4` (que da `2C|A| ≤ n` para `|A| ≤ δn/8`). El número de vértices saturados es
`≤ δn/8` (`m = ⌊δn/8⌋`). -/
theorem routing_budget_real (x : Sym2 V → ℤ) (hx : IsLocalProfile G lab F x) {C D : ℕ}
    (δ : ℝ) (hδ : 0 < δ) (hδC : C * δ ≤ 4) (he : 0 < norm1 G x)
    (hn : 0 < Fintype.card V)
    (hrows : ∀ v, (univ.filter (fun j : Row V => j.1 = v ∧ IsActiveRow G lab F j)).card ≤ C)
    (hdeg : ∀ j : Row V, IsActiveRow G lab F j → Fintype.card V ≤ C * j.2.card)
    (hdel : ∀ A : Finset V, (A.card : ℝ) ≤ δ * Fintype.card V → DeletionHyp G lab F A)
    (hD1 : 1 ≤ D) (hD : 12 * C ^ 2 ≤ D + 1) :
    ∃ cells : List (Sym2 V → ℤ), (∀ b ∈ cells, IsLocalProfile G lab F b) ∧
      (∀ e, (cells.map (fun b => b e)).sum = x e) ∧
      (cells.length : ℤ) ≤ 2 * norm1 G x ∧
      (∀ b ∈ cells, norm1 G b ≤ 3 * D) ∧
      (cells.map (norm1 G)).sum ≤ 6 * D * norm1 G x ∧
      ∀ v, (cells.countP (fun b => decide (InSupp G v b)) : ℤ) <
        3 * dabs G x v + ⌈32 * D * (norm1 G x : ℝ) / (δ * Fintype.card V)⌉₊ + 2 * D := by
  set n := Fintype.card V with hn_def
  set m := ⌊δ * n / 8⌋₊ with hm
  set q := ⌈32 * D * (norm1 G x : ℝ) / (δ * n)⌉₊ with hq
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hδn : 0 < δ * n := mul_pos hδ hnR
  have hm_le : (m : ℝ) ≤ δ * n / 8 := Nat.floor_le (by positivity)
  have hm_lt : δ * n / 8 < (m : ℝ) + 1 := Nat.lt_floor_add_one _
  have hq_ge : 32 * D * (norm1 G x : ℝ) / (δ * n) ≤ q := Nat.le_ceil _
  have heR : (0 : ℝ) < norm1 G x := by exact_mod_cast he
  have hDR : (1 : ℝ) ≤ D := by exact_mod_cast hD1
  have hqpos : (0 : ℝ) < q := lt_of_lt_of_le (by positivity) hq_ge
  have hP : PreparedRouting G lab F C m D := by
    refine ⟨hn, hrows, hdeg, fun A hA => hdel A ?_, ?_, hD1, hD⟩
    · have : (A.card : ℝ) ≤ m := by exact_mod_cast hA
      nlinarith
    · have h1 : (2 * C * m : ℝ) ≤ n := by
        have hC0 : (0 : ℝ) ≤ C := by positivity
        calc (2 * C * m : ℝ) ≤ 2 * C * (δ * n / 8) := by
              exact mul_le_mul_of_nonneg_left hm_le (by positivity)
          _ = (C * δ) * n / 4 := by ring
          _ ≤ 4 * n / 4 := by gcongr
          _ = n := by ring
      exact_mod_cast h1
  have hcap : 4 * D * norm1 G x < q * (m + 1) := by
    have h1 : (4 * D * norm1 G x : ℝ) ≤ q * (δ * n / 8) := by
      have := mul_le_mul_of_nonneg_right hq_ge (le_of_lt (by positivity : (0 : ℝ) < δ * n / 8))
      calc (4 * D * norm1 G x : ℝ) = 32 * D * (norm1 G x : ℝ) / (δ * n) * (δ * n / 8) := by
            field_simp; ring
        _ ≤ q * (δ * n / 8) := this
    have h2 : (q : ℝ) * (δ * n / 8) < q * (m + 1) := mul_lt_mul_of_pos_left hm_lt hqpos
    have h3 : ((4 * D * norm1 G x : ℤ) : ℝ) < ((q * (m + 1) : ℤ) : ℝ) := by
      push_cast; linarith
    exact_mod_cast h3
  exact routing_budget x hx hP hcap

end TypedTriangle.ActiveCover
