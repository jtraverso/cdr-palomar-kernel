/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import RequestProject.TypedTriangle.IncidenceImage

@[expose] public section

/-!
# G1-Z, proveedor 1b — Sección ℤ-lineal de la incidencia con coste controlado por el diámetro

Sea `G` un grafo simple finito en el que dos vértices conectados están unidos por un
recorrido de longitud `≤ D` (diámetro de cada componente `≤ D`; los vértices aislados no
imponen nada). Se construye un homomorfismo `ℤ`-lineal

`secL : incLattice G →ₗ[ℤ] (Sym2 V → ℤ)`

con `bd (secL x) = x` (sección del operador de incidencia SOBRE SU IMAGEN ENTERA), soportado
en las aristas de `G` y con coste `‖secL x‖₁ ≤ (2D+1)‖x‖₁`.

Construcción (fijada ANTES de recibir `x`):
* una raíz por componente (`rep`) y un recorrido corto `sw v` de longitud `≤ D` de cada
  vértice a su raíz; la cadena alternada de un recorrido tiene borde
  `δ_v − (−1)^{long} δ_raíz`;
* en cada raíz con un recorrido cerrado impar (componente no bipartita) se fija un
  recorrido cerrado impar de longitud `≤ 2D+1` construido con una arista que viola la
  paridad de los recorridos cortos; su cadena alternada tiene borde `2 δ_raíz`.

La carga residual en una raíz bipartita es cero por el balance (`incLattice_necessary`) y en
una raíz no bipartita es par; la división por dos se aplica sólo a esas cargas pares, donde es
aditiva y homogénea (no se usa la división entera como si fuese lineal en general).
-/

open Finset

noncomputable section
open Classical

namespace TypedTriangle.Incidence

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V}

/-! ## Borde, normas y cadenas de recorridos -/

/-- Operador de incidencia (borde) sobre cadenas de aristas. -/
def bd (c : Sym2 V → ℤ) : V → ℤ := ∑ e, c e • incVec e

lemma bd_add (c d : Sym2 V → ℤ) : bd (c + d) = bd c + bd d := by
  simp [bd, add_smul, Finset.sum_add_distrib]

lemma bd_sub (c d : Sym2 V → ℤ) : bd (c - d) = bd c - bd d := by
  simp [bd, sub_smul, Finset.sum_sub_distrib]

lemma bd_smul (k : ℤ) (c : Sym2 V → ℤ) : bd (k • c) = k • bd c := by
  simp [bd, Finset.smul_sum, mul_smul]

lemma bd_zero : bd (0 : Sym2 V → ℤ) = 0 := by simp [bd]

lemma bd_sum {ι : Type*} (s : Finset ι) (c : ι → Sym2 V → ℤ) :
    bd (∑ i ∈ s, c i) = ∑ i ∈ s, bd (c i) := by
  induction s using Finset.induction_on with
  | empty => simp [bd_zero]
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, bd_add, ih]

lemma bd_single (e : Sym2 V) : bd (Pi.single e 1) = incVec e := by
  simp only [bd]
  rw [Finset.sum_eq_single e]
  · simp
  · intro b _ hb; simp [hb]
  · simp

/-- Norma `ℓ¹` de una carga sobre vértices. -/
def l1V (x : V → ℤ) : ℤ := ∑ v, |x v|

/-- Norma `ℓ¹` de una cadena de aristas. -/
def l1E (c : Sym2 V → ℤ) : ℤ := ∑ e, |c e|

omit [DecidableEq V] in
lemma l1E_nonneg (c : Sym2 V → ℤ) : 0 ≤ l1E c := Finset.sum_nonneg fun _ _ => abs_nonneg _

omit [DecidableEq V] in
lemma l1E_add_le (c d : Sym2 V → ℤ) : l1E (c + d) ≤ l1E c + l1E d := by
  simp only [l1E, Pi.add_apply, ← Finset.sum_add_distrib]
  exact Finset.sum_le_sum fun _ _ => abs_add_le _ _

omit [DecidableEq V] in
lemma l1E_sub_le (c d : Sym2 V → ℤ) : l1E (c - d) ≤ l1E c + l1E d := by
  simp only [l1E, Pi.sub_apply, ← Finset.sum_add_distrib]
  exact Finset.sum_le_sum fun _ _ => abs_sub _ _

omit [DecidableEq V] in
lemma l1E_smul (k : ℤ) (c : Sym2 V → ℤ) : l1E (k • c) = |k| * l1E c := by
  simp [l1E, abs_mul, Finset.mul_sum]

omit [DecidableEq V] in
lemma l1E_zero : l1E (0 : Sym2 V → ℤ) = 0 := by simp [l1E]

omit [DecidableEq V] in
lemma l1E_sum_le {ι : Type*} (s : Finset ι) (c : ι → Sym2 V → ℤ) :
    l1E (∑ i ∈ s, c i) ≤ ∑ i ∈ s, l1E (c i) := by
  induction s using Finset.induction_on with
  | empty => simp [l1E_zero]
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha]
    exact (l1E_add_le _ _).trans (by linarith)

lemma l1E_single (e : Sym2 V) : l1E (Pi.single e (1 : ℤ)) = 1 := by
  simp only [l1E]
  rw [Finset.sum_eq_single e]
  · simp
  · intro b _ hb; simp [hb]
  · simp

/-- Cadena alternada de un recorrido: `+1, −1, +1, …` en sus aristas sucesivas. -/
def wchain : {u w : V} → G.Walk u w → Sym2 V → ℤ
  | _, _, .nil => 0
  | u, _, .cons (v := v) _ p => Pi.single s(u, v) 1 - wchain p

omit [Fintype V] in
@[simp] lemma wchain_nil {u : V} : wchain (SimpleGraph.Walk.nil : G.Walk u u) = 0 := rfl

omit [Fintype V] in
@[simp] lemma wchain_cons {u v w : V} (h : G.Adj u v) (p : G.Walk v w) :
    wchain (SimpleGraph.Walk.cons h p) = Pi.single s(u, v) 1 - wchain p := rfl

omit [Fintype V] in
lemma wchain_copy {u w u' w' : V} (p : G.Walk u w) (hu : u = u') (hw : w = w') :
    wchain (p.copy hu hw) = wchain p := by
  subst hu; subst hw; rfl

/-- Borde de la cadena alternada: `δ_u − (−1)^{long} δ_w`. -/
lemma bd_wchain {u w : V} (p : G.Walk u w) :
    bd (wchain p) = dlt u - ((-1 : ℤ) ^ p.length) • dlt w := by
  induction p with
  | nil => simp [bd_zero]
  | @cons a b c h p ih =>
    rw [wchain_cons, bd_sub, bd_single, ih, incVec_mk (G.ne_of_adj h),
      SimpleGraph.Walk.length_cons, pow_succ]
    simp only [mul_neg, mul_one, neg_smul]
    abel

omit [Fintype V] in
/-- La cadena alternada está soportada en las aristas de `G`. -/
lemma wchain_support {u w : V} (p : G.Walk u w) (e : Sym2 V) (he : wchain p e ≠ 0) :
    e ∈ G.edgeSet := by
  induction p with
  | nil => simp at he
  | @cons a b c h p ih =>
    rw [wchain_cons, Pi.sub_apply] at he
    by_cases hp : wchain p e = 0
    · rw [hp, sub_zero] at he
      by_cases hee : e = s(a, b)
      · rw [hee]; exact h
      · simp [hee] at he
    · exact ih hp

/-- Coste de la cadena alternada: a lo sumo la longitud. -/
lemma l1E_wchain_le {u w : V} (p : G.Walk u w) : l1E (wchain p) ≤ p.length := by
  induction p with
  | nil => simp [l1E_zero]
  | @cons a b c h p ih =>
    rw [wchain_cons, SimpleGraph.Walk.length_cons]
    refine (l1E_sub_le _ _).trans ?_
    rw [l1E_single]; push_cast; linarith

/-! ## Recorridos cortos fijados antes de la demanda -/

/-- Hipótesis de diámetro: dos vértices conectados se unen por un recorrido de longitud
`≤ D`. -/
def DiamLe (G : SimpleGraph V) (D : ℕ) : Prop :=
  ∀ u v, G.Reachable u v → ∃ p : G.Walk u v, p.length ≤ D

variable {D : ℕ}

/-- Recorrido corto de `v` a la raíz de su componente. -/
def sw (hD : DiamLe G D) (v : V) : G.Walk v (rep G v) :=
  Classical.choose (hD v (rep G v) (rep_reach v))

omit [Fintype V] [DecidableEq V] in
lemma sw_length (hD : DiamLe G D) (v : V) : (sw hD v).length ≤ D :=
  Classical.choose_spec (hD v (rep G v) (rep_reach v))

/-- Signo del recorrido corto. -/
def seps (hD : DiamLe G D) (v : V) : ℤ := (-1) ^ (sw hD v).length

omit [Fintype V] [DecidableEq V] in
lemma seps_cases (hD : DiamLe G D) (v : V) : seps hD v = 1 ∨ seps hD v = -1 := by
  unfold seps
  rcases Nat.even_or_odd (sw hD v).length with h | h
  · exact Or.inl h.neg_one_pow
  · exact Or.inr h.neg_one_pow

/-- `a` es una raíz con un recorrido cerrado impar (componente no bipartita). -/
def OddAt (G : SimpleGraph V) (a : V) : Prop := ∃ p : G.Walk a a, Odd p.length

omit [Fintype V] [DecidableEq V] in
/-- Si las aristas de una componente alternan el signo `ε`, todo recorrido en ella tiene
signo `ε_x ε_y`. -/
lemma walk_sign_of_alternating (ε : V → ℤ) (hε : ∀ v, ε v = 1 ∨ ε v = -1)
    (halt : ∀ u w, G.Adj u w → ε u = -ε w) {x y : V} (p : G.Walk x y) :
    ((-1 : ℤ) ^ p.length) = ε x * ε y := by
  induction p with
  | nil => rcases hε _ with h | h <;> rw [h] <;> simp
  | @cons a b c h p ih =>
    rw [SimpleGraph.Walk.length_cons, pow_succ, ih, halt a b h]
    ring

omit [Fintype V] in
/-- **Recorrido cerrado impar corto.** En una raíz `a` con un recorrido cerrado impar existe
uno de longitud `≤ 2D+1`. -/
lemma exists_short_odd (hD : DiamLe G D) {a : V} (ha : OddAt G a) (hra : rep G a = a) :
    ∃ q : G.Walk a a, Odd q.length ∧ q.length ≤ 2 * D + 1 := by
  by_contra hno
  push_neg at hno
  -- todas las aristas de la componente de `a` alternan el signo corto
  have halt : ∀ u w, G.Adj u w → rep G u = a → seps hD u = -seps hD w := by
    intro u w huw hu
    have hw : rep G w = a := (rep_eq_of_reach (G := G) huw.reachable).symm.trans hu
    by_contra hne
    have hsame : seps hD u = seps hD w := by
      rcases seps_cases hD u with h1 | h1 <;> rcases seps_cases hD w with h2 | h2 <;>
        simp_all
    -- recorrido cerrado en `a`
    let q : G.Walk a a :=
      ((sw hD u).reverse.append (SimpleGraph.Walk.cons huw (sw hD w))).copy hu hw
    have hql : q.length = (sw hD u).length + 1 + (sw hD w).length := by
      simp only [q, SimpleGraph.Walk.length_copy, SimpleGraph.Walk.length_append,
        SimpleGraph.Walk.length_reverse, SimpleGraph.Walk.length_cons]
      ring
    have hodd : Odd q.length := by
      rw [hql]
      unfold seps at hsame
      rcases Nat.even_or_odd (sw hD u).length with h1 | h1 <;>
        rcases Nat.even_or_odd (sw hD w).length with h2 | h2
      · exact (h1.add_one).add_even h2
      · rw [h1.neg_one_pow, h2.neg_one_pow] at hsame; norm_num at hsame
      · rw [h1.neg_one_pow, h2.neg_one_pow] at hsame; norm_num at hsame
      · exact (h1.add_one).add_odd h2 |>.add_one |> fun h => by
          rw [show (sw hD u).length + 1 + (sw hD w).length =
            ((sw hD u).length + (sw hD w).length) + 1 by ring]
          exact (h1.add_odd h2).add_one
    have := hno q hodd
    have h1 := sw_length hD u
    have h2 := sw_length hD w
    omega
  obtain ⟨p, hp⟩ := ha
  -- signo extendido: `seps` en la componente, `1` fuera
  let ε : V → ℤ := fun v => if rep G v = a then seps hD v else 1
  have hε : ∀ v, ε v = 1 ∨ ε v = -1 := by
    intro v; simp only [ε]; split_ifs
    · exact seps_cases hD v
    · exact Or.inl rfl
  -- el recorrido `p` vive en la componente de `a`
  have hcomp : ∀ {x y : V} (r : G.Walk x y), rep G x = a →
      ((-1 : ℤ) ^ r.length) = ε x * ε y := by
    intro x y r
    induction r with
    | nil => intro _; rcases hε _ with h | h <;> rw [h] <;> simp
    | @cons x' y' z' h r ih =>
      intro hx
      have hy : rep G y' = a := (rep_eq_of_reach (G := G) h.reachable).symm.trans hx
      rw [SimpleGraph.Walk.length_cons, pow_succ, ih hy]
      simp only [ε, if_pos hx, if_pos hy, halt x' y' h hx]
      ring
  have := hcomp p hra
  rw [hp.neg_one_pow] at this
  rcases hε a with h | h <;> rw [h] at this <;> norm_num at this

/-- Recorrido cerrado impar corto elegido en cada raíz no bipartita (o el trivial). -/
def oddWalk (hD : DiamLe G D) (a : V) : G.Walk a a :=
  if h : OddAt G a ∧ rep G a = a then Classical.choose (exists_short_odd hD h.1 h.2)
  else SimpleGraph.Walk.nil

/-- Cadena de corrección en la raíz `a` (cero si `a` no es una raíz no bipartita). -/
def oddChain (hD : DiamLe G D) (a : V) : Sym2 V → ℤ :=
  if OddAt G a ∧ rep G a = a then wchain (oddWalk hD a) else 0

lemma bd_oddChain (hD : DiamLe G D) {a : V} (h : OddAt G a ∧ rep G a = a) :
    bd (oddChain hD a) = (2 : ℤ) • dlt a := by
  have hs := Classical.choose_spec (exists_short_odd hD h.1 h.2)
  simp only [oddChain, if_pos h, oddWalk, dif_pos h, bd_wchain]
  rw [hs.1.neg_one_pow, neg_one_smul, sub_neg_eq_add, two_smul]

lemma l1E_oddChain_le (hD : DiamLe G D) (a : V) : l1E (oddChain hD a) ≤ 2 * D + 1 := by
  unfold oddChain
  split_ifs with h
  · have hs := Classical.choose_spec (exists_short_odd hD h.1 h.2)
    refine (l1E_wchain_le _).trans ?_
    simp only [oddWalk, dif_pos h]
    exact_mod_cast hs.2
  · rw [l1E_zero]; positivity

omit [Fintype V] in
lemma oddChain_support (hD : DiamLe G D) (a : V) (e : Sym2 V) (he : oddChain hD a e ≠ 0) :
    e ∈ G.edgeSet := by
  unfold oddChain at he
  split_ifs at he
  · exact wchain_support _ e he
  · simp at he

/-! ## Cargas residuales en las raíces -/

/-- Carga transportada a la raíz `a` por los recorridos cortos. -/
def rcharge (hD : DiamLe G D) (x : V → ℤ) (a : V) : ℤ :=
  ∑ v ∈ univ.filter (fun v => rep G v = a), x v * seps hD v

lemma rcharge_add (hD : DiamLe G D) (x y : V → ℤ) (a : V) :
    rcharge hD (x + y) a = rcharge hD x a + rcharge hD y a := by
  simp only [rcharge, Pi.add_apply, add_mul, Finset.sum_add_distrib]

lemma rcharge_smul (hD : DiamLe G D) (k : ℤ) (x : V → ℤ) (a : V) :
    rcharge hD (k • x) a = k * rcharge hD x a := by
  simp only [rcharge, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun _ _ => by ring

/-- En la imagen entera, la carga de una raíz sin recorrido cerrado impar es cero
(balance de la componente bipartita). -/
lemma rcharge_eq_zero (hD : DiamLe G D) {x : V → ℤ} (hx : x ∈ incLattice G) {a : V}
    (ha : ¬ OddAt G a) : rcharge hD x a = 0 := by
  have hno : ∀ p : G.Walk a a, ¬ Odd p.length := fun p hp => ha ⟨p, hp⟩
  set σ : V → ℤ := fun u => if rep G u = a then seps hD u else 0
  have hσadm : ∀ u v, G.Adj u v → σ u + σ v = 0 := by
    intro u v huv
    have hr : rep G u = rep G v := rep_eq_of_reach (G := G) huv.reachable
    simp only [σ]
    by_cases hu : rep G u = a
    · have hv : rep G v = a := hr ▸ hu
      rw [if_pos hu, if_pos hv]
      have e2 := parity_unique hno ((sw hD u).copy rfl hu)
        ((SimpleGraph.Walk.cons huv (sw hD v)).copy rfl hv)
      simp only [SimpleGraph.Walk.length_copy, SimpleGraph.Walk.length_cons, pow_succ] at e2
      simp only [seps, e2]; ring
    · have hv : ¬ rep G v = a := fun h => hu (hr ▸ h)
      rw [if_neg hu, if_neg hv, add_zero]
  have hzero := (incLattice_necessary hx).1 σ hσadm
  rw [← hzero]
  simp only [rcharge, σ, Finset.sum_filter]
  exact Finset.sum_congr rfl fun v _ => by split_ifs <;> ring

/-- En la imagen entera, la carga de toda raíz es par. -/
lemma rcharge_even (hD : DiamLe G D) {x : V → ℤ} (hx : x ∈ incLattice G) (a : V) :
    2 ∣ rcharge hD x a := by
  have hclosed : ∀ u v, G.Adj u v → (u ∈ univ.filter (fun v => rep G v = a) ↔
      v ∈ univ.filter (fun v => rep G v = a)) := by
    intro u v huv
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    rw [rep_eq_of_reach (G := G) huv.reachable]
  have hev := (incLattice_necessary hx).2 _ hclosed
  have e : rcharge hD x a = ∑ v ∈ univ.filter (fun v => rep G v = a), x v +
      ∑ v ∈ univ.filter (fun v => rep G v = a), x v * (seps hD v - 1) := by
    simp only [rcharge, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun v _ => by ring
  rw [e]
  refine even_iff_two_dvd.1 (hev.add (Finset.even_sum _ fun v _ => ?_))
  rcases seps_cases hD v with h | h
  · rw [h]; simp
  · rw [h]; exact ⟨-x v, by ring⟩

/-! ## La sección -/

/-- Fórmula de la sección (definida para todo `x`; es lineal en la imagen entera). -/
def secF (hD : DiamLe G D) (x : V → ℤ) : Sym2 V → ℤ :=
  ∑ v, x v • wchain (sw hD v) + ∑ a, (rcharge hD x a / 2) • oddChain hD a

lemma secF_add (hD : DiamLe G D) (x : V → ℤ) {y : V → ℤ}
    (hy : y ∈ incLattice G) : secF hD (x + y) = secF hD x + secF hD y := by
  have h2 : ∀ a, (rcharge hD (x + y) a / 2) • oddChain hD a =
      (rcharge hD x a / 2) • oddChain hD a + (rcharge hD y a / 2) • oddChain hD a := by
    intro a
    rw [rcharge_add, Int.add_ediv_of_dvd_right (rcharge_even hD hy a), add_smul]
  simp only [secF, Pi.add_apply, add_smul, Finset.sum_add_distrib, h2]
  abel

lemma secF_smul (hD : DiamLe G D) (k : ℤ) {x : V → ℤ} (hx : x ∈ incLattice G) :
    secF hD (k • x) = k • secF hD x := by
  have h2 : ∀ a, (rcharge hD (k • x) a / 2) • oddChain hD a =
      k • ((rcharge hD x a / 2) • oddChain hD a) := by
    intro a
    rw [rcharge_smul, Int.mul_ediv_assoc _ (rcharge_even hD hx a), mul_smul]
  simp only [secF, Pi.smul_apply, smul_eq_mul, mul_smul, h2, smul_add, Finset.smul_sum]

/-- **Sección ℤ-lineal** del operador de incidencia sobre su imagen entera. La división por
dos sólo actúa sobre las cargas de raíz, que son pares en `incLattice G`. -/
def secL (hD : DiamLe G D) : incLattice G →ₗ[ℤ] (Sym2 V → ℤ) where
  toFun x := secF hD x.1
  map_add' x y := secF_add hD x.1 y.2
  map_smul' k x := secF_smul hD k x.2

lemma secL_apply (hD : DiamLe G D) (x : incLattice G) : secL hD x = secF hD x.1 := rfl

/-- La sección es realmente una sección: `bd (secL x) = x`. -/
theorem bd_secL (hD : DiamLe G D) (x : incLattice G) : bd (secL hD x) = x.1 := by
  obtain ⟨x, hx⟩ := x
  rw [secL_apply]
  simp only [secF, bd_add, bd_sum, bd_smul, bd_wchain]
  -- primera parte: `x − Σ_a rcharge_a δ_a`
  have hx' : ∑ v, x v • dlt v = x := by funext w; simp [dlt, Pi.single_apply]
  have h1 : ∑ v, x v • (dlt v - ((-1 : ℤ) ^ (sw hD v).length) • dlt (rep G v)) =
      x - ∑ a, rcharge hD x a • dlt a := by
    have e : ∑ v, (x v * seps hD v) • dlt (rep G v) = ∑ a, rcharge hD x a • dlt a := by
      rw [← Finset.sum_fiberwise_of_maps_to (g := rep G) (t := univ)
        (fun v _ => Finset.mem_univ _)]
      refine Finset.sum_congr rfl fun a _ => ?_
      simp only [rcharge, Finset.sum_smul]
      exact Finset.sum_congr rfl fun v hv => by rw [(Finset.mem_filter.1 hv).2]
    rw [← e]
    simp only [smul_sub, Finset.sum_sub_distrib, mul_smul, seps, hx']
  -- segunda parte: corrige exactamente las cargas de raíz
  have h2 : ∀ a, (rcharge hD x a / 2) • bd (oddChain hD a) = rcharge hD x a • dlt a := by
    intro a
    by_cases h : OddAt G a ∧ rep G a = a
    · rw [bd_oddChain hD h, smul_smul, Int.ediv_mul_cancel (rcharge_even hD hx a)]
    · have hz : rcharge hD x a = 0 := by
        by_cases hodd : OddAt G a
        · -- `a` no es raíz: ningún vértice la tiene como representante
          have hra : rep G a ≠ a := fun h' => h ⟨hodd, h'⟩
          simp only [rcharge]
          refine Finset.sum_eq_zero fun v hv => ?_
          have hv' : rep G v = a := (Finset.mem_filter.1 hv).2
          exfalso; apply hra
          have : G.Reachable a v := (hv' ▸ rep_reach v).symm
          rw [rep_eq_of_reach this, hv']
        · exact rcharge_eq_zero hD hx hodd
      have hb : oddChain hD a = 0 := by simp [oddChain, h]
      rw [hz, hb, bd_zero]; simp
  rw [h1, Finset.sum_congr rfl fun a _ => h2 a]
  abel

/-- La sección está soportada en las aristas de `G`. -/
theorem secL_support (hD : DiamLe G D) (x : incLattice G) (e : Sym2 V)
    (he : secL hD x e ≠ 0) : e ∈ G.edgeSet := by
  rw [secL_apply] at he
  simp only [secF, Pi.add_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul] at he
  by_contra hne
  apply he
  have h1 : ∀ v, wchain (sw hD v) e = 0 := fun v => by
    by_contra h; exact hne (wchain_support _ e h)
  have h2 : ∀ a, oddChain hD a e = 0 := fun a => by
    by_contra h; exact hne (oddChain_support hD a e h)
  simp [h1, h2]

/-- **Coste controlado por el diámetro:** `‖secL x‖₁ ≤ (2D+1)‖x‖₁`. -/
theorem l1E_secL_le (hD : DiamLe G D) (x : incLattice G) :
    l1E (secL hD x) ≤ (2 * D + 1) * l1V x.1 := by
  obtain ⟨x, hx⟩ := x
  rw [secL_apply]
  have hA : l1E (∑ v, x v • wchain (sw hD v)) ≤ D * l1V x := by
    refine (l1E_sum_le _ _).trans ?_
    simp only [l1E_smul, l1V, Finset.mul_sum]
    refine Finset.sum_le_sum fun v _ => ?_
    have := (l1E_wchain_le (sw hD v)).trans (by exact_mod_cast sw_length hD v :
      ((sw hD v).length : ℤ) ≤ D)
    nlinarith [abs_nonneg (x v)]
  -- `Σ_a |rcharge_a| ≤ ‖x‖₁`
  have hR : ∑ a, |rcharge hD x a| ≤ l1V x := by
    calc ∑ a, |rcharge hD x a|
        ≤ ∑ a, ∑ v ∈ univ.filter (fun v => rep G v = a), |x v| := by
          refine Finset.sum_le_sum fun a _ => (Finset.abs_sum_le_sum_abs _ _).trans ?_
          refine Finset.sum_le_sum fun v _ => ?_
          rcases seps_cases hD v with h | h <;> rw [h] <;> simp
      _ = l1V x := by
          rw [l1V]
          exact Finset.sum_fiberwise_of_maps_to (s := univ) (g := rep G) (t := univ)
            (f := fun v => |x v|) (fun v _ => Finset.mem_univ _)
  have hB : 2 * l1E (∑ a, (rcharge hD x a / 2) • oddChain hD a) ≤
      (2 * D + 1) * l1V x := by
    have : ∀ a, 2 * l1E ((rcharge hD x a / 2) • oddChain hD a) ≤
        (2 * D + 1) * |rcharge hD x a| := by
      intro a
      rw [l1E_smul]
      obtain ⟨k, hk⟩ := rcharge_even hD hx a
      rw [hk, Int.mul_ediv_cancel_left _ (by norm_num : (2 : ℤ) ≠ 0), abs_mul]
      have := l1E_oddChain_le hD a
      have := abs_nonneg k
      norm_num
      nlinarith
    calc 2 * l1E (∑ a, (rcharge hD x a / 2) • oddChain hD a)
        ≤ 2 * ∑ a, l1E ((rcharge hD x a / 2) • oddChain hD a) := by
          linarith [l1E_sum_le univ (fun a => (rcharge hD x a / 2) • oddChain hD a)]
      _ = ∑ a, 2 * l1E ((rcharge hD x a / 2) • oddChain hD a) := by rw [Finset.mul_sum]
      _ ≤ ∑ a, (2 * D + 1) * |rcharge hD x a| := Finset.sum_le_sum fun a _ => this a
      _ = (2 * D + 1) * ∑ a, |rcharge hD x a| := by rw [Finset.mul_sum]
      _ ≤ (2 * D + 1) * l1V x := by
          exact mul_le_mul_of_nonneg_left hR (by positivity)
  have hl1 : 0 ≤ l1V x := Finset.sum_nonneg fun _ _ => abs_nonneg _
  have := l1E_add_le (∑ v, x v • wchain (sw hD v))
    (∑ a, (rcharge hD x a / 2) • oddChain hD a)
  simp only [secF]
  nlinarith

/-- **Proveedor de sección (G1-Z, §2 de la guía V5).** Si cada componente tiene diámetro
`≤ D`, existe un homomorfismo `ℤ`-lineal `s` de la imagen entera de la incidencia en las
cadenas de aristas de `G`, con `bd (s x) = x` y `‖s x‖₁ ≤ (2D+1)‖x‖₁`. -/
theorem exists_linear_section (hD : DiamLe G D) :
    ∃ s : incLattice G →ₗ[ℤ] (Sym2 V → ℤ), ∀ x : incLattice G,
      bd (s x) = x.1 ∧ (∀ e, s x e ≠ 0 → e ∈ G.edgeSet) ∧
      l1E (s x) ≤ (2 * D + 1) * l1V x.1 :=
  ⟨secL hD, fun x => ⟨bd_secL hD x, secL_support hD x, l1E_secL_le hD x⟩⟩

end TypedTriangle.Incidence
