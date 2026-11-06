/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import RequestProject.TypedTriangle.ActiveStateGraph

@[expose] public section

/-!
# Caracterización de la adyacencia de la cubierta y producto de signos (V12, S26 §3)

Descripción explícita de los arcos de la cubierta del sistema de componentes en términos de
estados `((v, K), s)`:

* `nbrSt X u` — el estado alcanzado desde `X = ((a, K), s)` por la arista física `au`:
  `((u, comp u a), s ⊕ φ(a, u))`, con `φ(a, u) = (σ_{(a, comp a u)}(u) == σ_{(u, comp u a)}(a))`,
  simétrico en `a, u` (`phi_comm`);
* `flipSt` — cambio de signo; es un automorfismo de la adyacencia (`cadj_flip`);
* `cadj_nbr`, `cadj_vert`, `cadj_cases` — los arcos son exactamente los físicos hacia
  `nbrSt X u` (`G.Adj a u`, `K = comp a u`) y los verticales hacia `flipSt X` en filas no
  bipartitas;
* `cadj_active` — la adyacencia preserva la actividad;
* `nbr_nbr_triangle` — **producto de signos en un triángulo permitido** `{a, u, w}`: ir
  `a → u → w` llega al mismo estado que `a → w` si el número de filas bipartitas entre
  `(a, ·), (u, ·), (w, ·)` es impar, y a su opuesto si es par.
-/

open Finset Classical

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace TypedTriangle.ActiveCover

open TypedTriangle.ComponentRows TypedTriangle.SignedCover TypedTriangle.Circulation

variable {V I : Type*} [Fintype V] {G : SimpleGraph V} {lab : V → I} {F : Set (Multiset I)}

variable (G lab F) in
/-- Adyacencia dirigida de la cubierta entre estados. -/
def CAdj (X Y : Row V × Bool) : Prop := ∃ α : Arc (rowSys G lab F), src _ α = X ∧ tgt _ α = Y

/-- Cambio de signo de un estado. -/
def flipSt (X : Row V × Bool) : Row V × Bool := (X.1, !X.2)

variable (G lab F) in
/-- Bit de cambio de signo de la arista `au`. -/
def phi (a u : V) : Bool :=
  sigma G lab F (a, comp G lab F a u) u == sigma G lab F (u, comp G lab F u a) a

variable (G lab F) in
/-- Vecino físico de `X` por la arista `X.root — u`. -/
def nbrSt (X : Row V × Bool) (u : V) : Row V × Bool :=
  ((u, comp G lab F u X.1.1), xor X.2 (phi G lab F X.1.1 u))

lemma beq_comm' (x y : Bool) : (x == y) = (y == x) := by cases x <;> cases y <;> rfl

lemma phi_comm (a u : V) : phi G lab F a u = phi G lab F u a := beq_comm' _ _

omit [Fintype V] in
@[simp] lemma flipSt_flipSt (X : Row V × Bool) : flipSt (flipSt X) = X := by
  simp [flipSt]

omit [Fintype V] in
lemma flipSt_ne (X : Row V × Bool) : flipSt X ≠ X := by
  intro h; have := congrArg Prod.snd h; simp [flipSt] at this

lemma nbrSt_flipSt (X : Row V × Bool) (u : V) :
    nbrSt G lab F (flipSt X) u = flipSt (nbrSt G lab F X u) := by
  simp only [nbrSt, flipSt, Prod.mk.injEq, true_and]
  cases X.2 <;> cases phi G lab F X.1.1 u <;> rfl

/-! ### Hechos sobre enlaces y componentes -/

omit [Fintype V] in
lemma allowed_perm {a u w : V} {T : Finset V} (hT : T = {a, u, w} ∨ T = {a, w, u} ∨
    T = {u, a, w} ∨ T = {u, w, a} ∨ T = {w, a, u} ∨ T = {w, u, a})
    (h : SparseEdge.IsAllowed G lab F {a, u, w}) : SparseEdge.IsAllowed G lab F T := by
  have : T = {a, u, w} := by
    rcases hT with rfl | rfl | rfl | rfl | rfl | rfl <;> ext <;> simp <;> tauto
  rw [this]; exact h

omit [Fintype V] in
/-- Un triángulo del enlace de `a` da adyacencias en los enlaces de `u` y `w`. -/
lemma link_adj_rot {a u w : V} (h : (link G lab F a).Adj u w) :
    (link G lab F u).Adj a w ∧ (link G lab F w).Adj u a := by
  obtain ⟨hvu, hvw, huw⟩ := allowed_ne h.2
  exact ⟨⟨hvw, allowed_perm (by tauto) h.2⟩, ⟨Ne.symm hvu, allowed_perm (by tauto) h.2⟩⟩

omit [Fintype V] in
lemma link_adj_G {a u w : V} (h : (link G lab F a).Adj u w) : G.Adj a u := by
  obtain ⟨hvu, -, -⟩ := allowed_ne h.2
  exact h.2.2.1 a (by simp) u (by simp) hvu

lemma mem_comp_self (v u : V) : u ∈ comp G lab F v u := by simp [comp]

lemma mem_comp_of_adj {v u w : V} (h : (link G lab F v).Adj u w) : w ∈ comp G lab F v u := by
  simp only [comp, Finset.mem_filter, Finset.mem_univ, true_and]; exact h.reachable

lemma comp_eq_of_adj {v u w : V} (h : (link G lab F v).Adj u w) :
    comp G lab F v w = comp G lab F v u := comp_eq_of_mem (mem_comp_of_adj h)

omit [Fintype V] in
/-- En una fila, dos vecinos adyacentes en el enlace tienen signos distintos exactamente si
la fila es bipartita. -/
lemma sigma_xor {R : Row V} {p q : V} (h : (link G lab F R.1).Adj p q) (hp : p ∈ R.2)
    (hq : q ∈ R.2) : xor (sigma G lab F R p) (sigma G lab F R q) = decide (IsBip G lab F R) := by
  unfold sigma
  by_cases hB : IsBip G lab F R
  · rw [if_pos hB, if_pos hB, decide_eq_true hB]
    have hc : col G lab F R p ≠ col G lab F R q := by
      unfold col; rw [dif_pos hB]; exact Classical.choose_spec hB p hp q hq h
    revert hc; cases col G lab F R p <;> cases col G lab F R q <;> simp
  · rw [if_neg hB, if_neg hB, decide_eq_false hB]; rfl

/-! ### Caracterización de la adyacencia -/

lemma cadj_nbr {X : Row V × Bool} {u : V} (hadj : G.Adj X.1.1 u)
    (hX : X.1.2 = comp G lab F X.1.1 u) : CAdj G lab F X (nbrSt G lab F X u) := by
  obtain ⟨⟨a, K⟩, s⟩ := X
  simp only at hadj hX
  subst hX
  let e : Col G := ⟨s(a, u), hadj⟩
  rcases ends_cases G e (v := a) (u := u) rfl with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · refine ⟨Sum.inl (e, true, s), ?_, ?_⟩
    · simp [src, rowSys, row1, h1, h2]
    · simp only [tgt, if_true, rowSys, row2, tsign, row1, h1, h2, nbrSt, phi]
  · refine ⟨Sum.inl (e, false, s), ?_, ?_⟩
    · simp [src, rowSys, row2, h1, h2]
    · simp only [tgt, Bool.false_eq_true, if_false, rowSys, row2, tsign, row1, h1, h2, nbrSt,
        phi, beq_comm']

lemma cadj_vert {X : Row V × Bool} (hB : ¬ IsBip G lab F X.1) : CAdj G lab F X (flipSt X) := by
  have hnb : (rowSys G lab F).nb X.1 = true := by simp [rowSys, hB]
  exact ⟨Sum.inr (⟨X.1, hnb⟩, X.2), rfl, rfl⟩

lemma cadj_cases {X Y : Row V × Bool} (h : CAdj G lab F X Y) :
    (Y.1.1 ≠ X.1.1 ∧ G.Adj X.1.1 Y.1.1 ∧ X.1.2 = comp G lab F X.1.1 Y.1.1 ∧
      Y = nbrSt G lab F X Y.1.1) ∨ (Y = flipSt X ∧ ¬ IsBip G lab F X.1) := by
  obtain ⟨α, rfl, rfl⟩ := h
  rcases α with ⟨p, d, s⟩ | ⟨j, s⟩
  · left
    have hne := ends_ne G p
    have hp := p.2
    rw [← ends_spec G p, SimpleGraph.mem_edgeSet] at hp
    cases d
    · simp only [src, tgt, Bool.false_eq_true, if_false, rowSys, row1, row2]
      refine ⟨hne, hp.symm, trivial, ?_⟩
      simp only [nbrSt, phi, tsign, beq_comm']
    · simp only [src, tgt, if_true, rowSys, row1, row2]
      refine ⟨hne.symm, hp, trivial, ?_⟩
      simp only [nbrSt, phi, tsign]
  · right
    have hj := j.2
    simp only [rowSys, Bool.not_eq_eq_eq_not, Bool.not_true, decide_eq_false_iff_not] at hj
    exact ⟨rfl, hj⟩

lemma cadj_flip {X Y : Row V × Bool} (h : CAdj G lab F X Y) :
    CAdj G lab F (flipSt X) (flipSt Y) := by
  rcases cadj_cases h with ⟨-, hadj, hX, hY⟩ | ⟨hY, hB⟩
  · rw [hY, ← nbrSt_flipSt]
    exact cadj_nbr hadj hX
  · rw [hY]
    exact (flipSt_flipSt X).symm ▸ cadj_vert (X := flipSt X) hB

lemma cadj_symm {X Y : Row V × Bool} (h : CAdj G lab F X Y) : CAdj G lab F Y X := by
  obtain ⟨α, h1, h2⟩ := h
  exact ⟨revArc _ α, by rw [src_revArc, h2], by rw [tgt_revArc, h1]⟩

lemma cadj_ne {X Y : Row V × Bool} (h : CAdj G lab F X Y) : X ≠ Y := by
  obtain ⟨α, rfl, rfl⟩ := h
  exact src_ne_tgt G lab F α

/-- Una fila activa contiene sólo vértices no aislados del enlace. -/
lemma linkActive_of_activeRow {a : V} {K : Finset V} (hK : IsActiveRow G lab F (a, K)) {u : V}
    (hu : u ∈ K) : LinkActive G lab F a u := by
  obtain ⟨u₀, h₀, hK⟩ := hK
  simp only at h₀ hK
  exact linkActive_of_mem_comp h₀ (hK ▸ hu)

/-- El estado vecino por una arista `au` con `u` no aislado en `L_a` es activo. -/
lemma nbrSt_active {X : Row V × Bool} {u : V} (hu : LinkActive G lab F X.1.1 u) :
    IsActiveRow G lab F (nbrSt G lab F X u).1 := by
  obtain ⟨w, -, hT⟩ := hu
  obtain ⟨-, hvw, -⟩ := allowed_ne hT
  exact ⟨X.1.1, ⟨w, hvw, allowed_perm (by tauto) hT⟩, rfl⟩

lemma cadj_active {X Y : Row V × Bool} (hX : IsActiveRow G lab F X.1) (h : CAdj G lab F X Y) :
    IsActiveRow G lab F Y.1 := by
  rcases cadj_cases h with ⟨-, -, hK, hY⟩ | ⟨hY, -⟩
  · rw [hY]
    apply nbrSt_active
    obtain ⟨⟨a, K⟩, s⟩ := X
    simp only at hK ⊢
    exact linkActive_of_activeRow hX (hK ▸ mem_comp_self a Y.1.1)
  · rw [hY]; exact hX

/-! ### Producto de signos en un triángulo -/

lemma bool_triangle (s x1 x2 y1 y2 z1 z2 : Bool) :
    xor (xor s (x1 == y1)) (y2 == z1) =
      if xor (xor (xor x1 x2) (xor y1 y2)) (xor z1 z2) then xor s (x2 == z2)
      else !(xor s (x2 == z2)) := by
  revert s x1 x2 y1 y2 z1 z2; decide

/-- **Producto de signos.** Si `u ~ w` en el enlace de `a` y `X` está sobre `(a, comp a u)`,
ir `a → u → w` lleva a la misma fila que `a → w`, con el mismo signo si el número de filas
bipartitas entre `(a, comp a u)`, `(u, comp u a)`, `(w, comp w a)` es impar, y con el signo
opuesto si es par. -/
theorem nbr_nbr_triangle {X : Row V × Bool} {u w : V} (h : (link G lab F X.1.1).Adj u w)
    (hX : X.1.2 = comp G lab F X.1.1 u) :
    nbrSt G lab F (nbrSt G lab F X u) w =
      if xor (xor (decide (IsBip G lab F X.1)) (decide (IsBip G lab F (u, comp G lab F u X.1.1))))
          (decide (IsBip G lab F (w, comp G lab F w X.1.1)))
      then nbrSt G lab F X w else flipSt (nbrSt G lab F X w) := by
  obtain ⟨⟨a, K⟩, s⟩ := X
  simp only at h hX ⊢
  subst hX
  obtain ⟨hu, hw⟩ := link_adj_rot h
  have e1 : comp G lab F u w = comp G lab F u a := comp_eq_of_adj hu
  have e2 : comp G lab F w u = comp G lab F w a := comp_eq_of_adj hw.symm
  have e3 : comp G lab F a w = comp G lab F a u := comp_eq_of_adj h
  have x := sigma_xor (R := (a, comp G lab F a u)) h (mem_comp_self a u) (mem_comp_of_adj h)
  have y := sigma_xor (R := (u, comp G lab F u a)) hu (mem_comp_self u a) (mem_comp_of_adj hu)
  have z := sigma_xor (R := (w, comp G lab F w a)) hw (by rw [← e2]; exact mem_comp_self w u)
    (by rw [← e2]; exact mem_comp_of_adj hw)
  rw [← x, ← y, ← z]
  simp only [nbrSt, phi, e1, e2, e3]
  rw [bool_triangle s _ (sigma G lab F (a, comp G lab F a u) w) _
    (sigma G lab F (u, comp G lab F u a) w) _ (sigma G lab F (w, comp G lab F w a) a)]
  split_ifs <;> simp [flipSt]

end TypedTriangle.ActiveCover
