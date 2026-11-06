/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import Mathlib

@[expose] public section

/-!
# G1-Z, proveedor 1 — Imagen entera de la incidencia no orientada

Para un grafo simple finito `G` sobre `V`, la incidencia no orientada envía la arista `uv` a
`δ_u + δ_v ∈ ℤ^V`. Se caracteriza su imagen entera `L = span_ℤ {δ_u + δ_v : uv ∈ E}`:

`x ∈ L` si y sólo si
1. (balance) `Σ_v σ_v x_v = 0` para todo `σ : V → ℤ` con `σ_u + σ_v = 0` en cada arista, y
2. (paridad) `Σ_{v ∈ S} x_v` es par para todo `S` cerrado por adyacencia.

En una componente bipartita con lados `X, Y`, (1) con `σ = 1_X − 1_Y` es el balance
`Σ_X x = Σ_Y x`; en una componente no bipartita (1) es vacía y queda la paridad (2). La
suficiencia se demuestra con recorridos: `δ_u ≡ ±δ_r (mod L)` a lo largo de un recorrido a un
representante `r` de la componente; si existe un recorrido cerrado impar en `r`, `2 δ_r ∈ L`;
si no existe, la paridad de los recorridos define un `σ` admisible que fuerza la carga en `r`
a anularse. No se supone que las componentes sean no bipartitas.
-/

open Finset

noncomputable section
open Classical

namespace TypedTriangle.Incidence

variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)

/-- Vector de incidencia de una arista (como `Sym2`). -/
def incVec (e : Sym2 V) : V → ℤ := fun w => if w ∈ e then 1 else 0

/-- Imagen entera de la incidencia no orientada. -/
def incLattice : Submodule ℤ (V → ℤ) :=
  Submodule.span ℤ (Set.range (fun e : G.edgeSet => incVec (e : Sym2 V)))

/-- Delta de Kronecker. -/
abbrev dlt (u : V) : V → ℤ := Pi.single u 1

variable {G}

omit [Fintype V] in
lemma incVec_mk {u v : V} (h : u ≠ v) : incVec s(u, v) = dlt u + dlt v := by
  funext w
  simp only [incVec, Sym2.mem_iff, Pi.add_apply, dlt, Pi.single_apply]
  by_cases hu : w = u
  · subst hu; simp [h]
  · by_cases hv : w = v
    · subst hv; simp [hu]
    · simp [hu, hv]

omit [Fintype V] in
lemma gen_mem {u v : V} (h : G.Adj u v) : dlt u + dlt v ∈ incLattice G := by
  rw [← incVec_mk (G.ne_of_adj h)]
  exact Submodule.subset_span ⟨⟨s(u, v), h⟩, rfl⟩

omit [Fintype V] in
lemma walk_mem {u w : V} (p : G.Walk u w) :
    dlt u - ((-1 : ℤ) ^ p.length) • dlt w ∈ incLattice G := by
  induction p with
  | nil => simp
  | @cons a b c h p ih =>
    have e : dlt a - ((-1 : ℤ) ^ (p.cons h).length) • dlt c =
        (dlt a + dlt b) - (dlt b - ((-1 : ℤ) ^ p.length) • dlt c) := by
      rw [SimpleGraph.Walk.length_cons, pow_succ]; simp only [mul_neg, mul_one, neg_smul]
      abel
    rw [e]
    exact Submodule.sub_mem _ (gen_mem h) ih

omit [Fintype V] [DecidableEq V] in
lemma parity_unique {a v : V} (hno : ∀ p : G.Walk a a, ¬ Odd p.length) (p q : G.Walk v a) :
    ((-1 : ℤ) ^ p.length) = (-1) ^ q.length := by
  have h := hno (p.reverse.append q)
  rw [SimpleGraph.Walk.length_append, SimpleGraph.Walk.length_reverse,
    Nat.not_odd_iff_even, Nat.even_add] at h
  rcases Nat.even_or_odd p.length with hp | hp
  · rw [hp.neg_one_pow, (h.1 hp).neg_one_pow]
  · have hq : Odd q.length := Nat.not_even_iff_odd.1 fun hq => (Nat.not_even_iff_odd.2 hp) (h.2 hq)
    rw [hp.neg_one_pow, hq.neg_one_pow]

/-- Representante de la componente conexa. -/
def rep (G : SimpleGraph V) (v : V) : V := Quot.out (G.connectedComponentMk v)

omit [Fintype V] [DecidableEq V] in
lemma rep_reach (v : V) : G.Reachable v (rep G v) := by
  have : G.connectedComponentMk (rep G v) = G.connectedComponentMk v := Quot.out_eq _
  exact (SimpleGraph.ConnectedComponent.eq.1 this).symm

omit [Fintype V] [DecidableEq V] in
lemma rep_eq_of_reach {u v : V} (h : G.Reachable u v) : rep G u = rep G v := by
  unfold rep; rw [SimpleGraph.ConnectedComponent.eq.2 h]

/-- Recorrido elegido al representante. -/
def wk (G : SimpleGraph V) (v : V) : G.Walk v (rep G v) := (rep_reach v).some

/-- Signo del recorrido elegido. -/
def eps (G : SimpleGraph V) (v : V) : ℤ := (-1) ^ (wk G v).length

omit [Fintype V] [DecidableEq V] in
lemma eps_sq (v : V) : eps G v = 1 ∨ eps G v = -1 := by
  unfold eps
  rcases Nat.even_or_odd (wk G v).length with h | h
  · exact Or.inl h.neg_one_pow
  · exact Or.inr h.neg_one_pow

/-- **Necesidad.** -/
theorem incLattice_necessary {x : V → ℤ} (hx : x ∈ incLattice G) :
    (∀ σ : V → ℤ, (∀ u v, G.Adj u v → σ u + σ v = 0) → ∑ v, σ v * x v = 0) ∧
    (∀ S : Finset V, (∀ u v, G.Adj u v → (u ∈ S ↔ v ∈ S)) → Even (∑ v ∈ S, x v)) := by
  induction hx using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨⟨e, he⟩, rfl⟩ := hy
    induction e using Sym2.ind with
    | _ u v =>
    have huv : G.Adj u v := he
    have e : (fun e : G.edgeSet => incVec (e : Sym2 V)) ⟨s(u, v), he⟩ = dlt u + dlt v :=
      incVec_mk (G.ne_of_adj huv)
    rw [e]
    refine ⟨fun σ hσ => ?_, fun S hS => ?_⟩
    · simp only [Pi.add_apply, mul_add, Finset.sum_add_distrib, dlt, Pi.single_apply,
        mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]
      exact hσ u v huv
    · simp only [Pi.add_apply, Finset.sum_add_distrib, dlt, Pi.single_apply,
        Finset.sum_ite_eq']
      by_cases hu : u ∈ S
      · rw [if_pos hu, if_pos ((hS u v huv).1 hu)]; exact ⟨1, rfl⟩
      · rw [if_neg hu, if_neg (fun h => hu ((hS u v huv).2 h))]; exact ⟨0, rfl⟩
  | zero => exact ⟨fun _ _ => by simp, fun _ _ => by simp⟩
  | add y z _ _ hy hz =>
    refine ⟨fun σ hσ => ?_, fun S hS => ?_⟩
    · simp only [Pi.add_apply, mul_add, Finset.sum_add_distrib, hy.1 σ hσ, hz.1 σ hσ, add_zero]
    · simp only [Pi.add_apply, Finset.sum_add_distrib]; exact (hy.2 S hS).add (hz.2 S hS)
  | smul a y _ hy =>
    refine ⟨fun σ hσ => ?_, fun S hS => ?_⟩
    · simp only [Pi.smul_apply, smul_eq_mul]
      have := hy.1 σ hσ
      calc ∑ v, σ v * (a * y v) = a * ∑ v, σ v * y v := by
            rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun v _ => by ring
        _ = 0 := by rw [this, mul_zero]
    · simp only [Pi.smul_apply, smul_eq_mul, ← Finset.mul_sum]
      exact (hy.2 S hS).mul_left a

/-- **Suficiencia.** -/
theorem incLattice_sufficient {x : V → ℤ}
    (hσ : ∀ σ : V → ℤ, (∀ u v, G.Adj u v → σ u + σ v = 0) → ∑ v, σ v * x v = 0)
    (hpar : ∀ S : Finset V, (∀ u v, G.Adj u v → (u ∈ S ↔ v ∈ S)) → Even (∑ v ∈ S, x v)) :
    x ∈ incLattice G := by
  set L := incLattice G
  set r := rep G
  set m : V → ℤ := fun w => ∑ v ∈ univ.filter (fun v => r v = w), x v * eps G v
  -- paso 1
  have h1 : x - ∑ v, (x v * eps G v) • dlt (r v) ∈ L := by
    have hx : ∑ v, x v • dlt v = x := by
      funext w; simp [dlt, Pi.single_apply]
    have e : x - ∑ v, (x v * eps G v) • dlt (r v) =
        ∑ v, x v • (dlt v - eps G v • dlt (r v)) := by
      nth_rewrite 1 [← hx]
      rw [← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun v _ => by rw [smul_sub, mul_smul]
    rw [e]
    exact Submodule.sum_mem _ fun v _ => Submodule.smul_mem _ _ (walk_mem (wk G v))
  -- paso 2
  have h2 : ∑ v, (x v * eps G v) • dlt (r v) = ∑ w ∈ univ.image r, m w • dlt w := by
    rw [← Finset.sum_fiberwise_of_maps_to (g := r) (t := univ.image r)
      (fun v _ => Finset.mem_image_of_mem r (Finset.mem_univ v))]
    refine Finset.sum_congr rfl fun w _ => ?_
    simp only [m, Finset.sum_smul]
    exact Finset.sum_congr rfl fun v hv => by rw [(Finset.mem_filter.1 hv).2]
  -- paso 3
  have h3 : ∀ w ∈ univ.image r, m w • dlt w ∈ L := by
    intro w hw
    obtain ⟨v0, -, rfl⟩ := Finset.mem_image.1 hw
    set a := r v0
    have hclosed : ∀ u v, G.Adj u v → (u ∈ univ.filter (fun v => r v = a) ↔
        v ∈ univ.filter (fun v => r v = a)) := by
      intro u v huv
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      have := rep_eq_of_reach (G := G) huv.reachable
      change r u = r v at this
      rw [this]
    by_cases hodd : ∃ p : G.Walk a a, Odd p.length
    · obtain ⟨p, hp⟩ := hodd
      have h2a : (2 : ℤ) • dlt a ∈ L := by
        have := walk_mem p
        rw [hp.neg_one_pow, neg_one_smul, sub_neg_eq_add, ← two_smul ℤ] at this
        exact this
      have hev := hpar _ hclosed
      have hm : Even (m a) := by
        have e : m a = ∑ v ∈ univ.filter (fun v => r v = a), x v +
            ∑ v ∈ univ.filter (fun v => r v = a), x v * (eps G v - 1) := by
          simp only [m, ← Finset.sum_add_distrib]
          exact Finset.sum_congr rfl fun v _ => by ring
        rw [e]
        refine hev.add (Finset.even_sum _ fun v _ => ?_)
        rcases eps_sq (G := G) v with h | h
        · rw [h]; simp
        · rw [h]; exact ⟨-x v, by ring⟩
      obtain ⟨k, hk⟩ := hm
      rw [hk, show k + k = k * 2 by ring, mul_smul]
      exact Submodule.smul_mem _ _ h2a
    · push_neg at hodd
      have hno : ∀ p : G.Walk a a, ¬ Odd p.length := hodd
      set σ : V → ℤ := fun u => if r u = a then eps G u else 0
      have hσadm : ∀ u v, G.Adj u v → σ u + σ v = 0 := by
        intro u v huv
        have hr : r u = r v := rep_eq_of_reach (G := G) huv.reachable
        simp only [σ]
        by_cases hu : r u = a
        · have hv : r v = a := hr ▸ hu
          rw [if_pos hu, if_pos hv]
          have q1 : G.Walk u a := (wk G u).copy rfl hu
          have q2 : G.Walk u a := (SimpleGraph.Walk.cons huv (wk G v)).copy rfl hv
          have e1 : eps G u = (-1) ^ ((wk G u).copy rfl hu).length := by
            simp [eps]
          have e2 := parity_unique hno ((wk G u).copy rfl hu)
            ((SimpleGraph.Walk.cons huv (wk G v)).copy rfl hv)
          rw [e1, e2]
          simp only [SimpleGraph.Walk.length_copy, SimpleGraph.Walk.length_cons, pow_succ, eps]
          ring
        · have hv : ¬ r v = a := fun h => hu (hr ▸ h)
          rw [if_neg hu, if_neg hv, add_zero]
      have hzero := hσ σ hσadm
      have hma : m a = 0 := by
        rw [← hzero]
        simp only [m, σ, Finset.sum_filter]
        exact Finset.sum_congr rfl fun v _ => by split_ifs <;> ring
      rw [hma, zero_smul]; exact Submodule.zero_mem _
  have key := Submodule.add_mem _ h1 (h2 ▸ Submodule.sum_mem _ h3)
  rwa [sub_add_cancel] at key

/-- **Imagen entera de la incidencia no orientada (G1-Z, proveedor 1).** -/
theorem mem_incLattice_iff (x : V → ℤ) :
    x ∈ incLattice G ↔
      (∀ σ : V → ℤ, (∀ u v, G.Adj u v → σ u + σ v = 0) → ∑ v, σ v * x v = 0) ∧
      (∀ S : Finset V, (∀ u v, G.Adj u v → (u ∈ S ↔ v ∈ S)) → Even (∑ v ∈ S, x v)) :=
  ⟨incLattice_necessary, fun h => incLattice_sufficient h.1 h.2⟩

/-- Forma con coeficientes explícitos por arista. -/
theorem exists_coeffs_iff (x : V → ℤ) :
    (∃ c : G.edgeSet → ℤ, ∑ e, c e • incVec (e : Sym2 V) = x) ↔
      (∀ σ : V → ℤ, (∀ u v, G.Adj u v → σ u + σ v = 0) → ∑ v, σ v * x v = 0) ∧
      (∀ S : Finset V, (∀ u v, G.Adj u v → (u ∈ S ↔ v ∈ S)) → Even (∑ v ∈ S, x v)) := by
  rw [← mem_incLattice_iff, incLattice, Submodule.mem_span_range_iff_exists_fun]

end TypedTriangle.Incidence
