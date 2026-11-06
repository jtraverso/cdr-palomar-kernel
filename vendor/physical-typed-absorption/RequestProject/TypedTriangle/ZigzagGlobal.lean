/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import RequestProject.TypedTriangle.ZigzagInput

@[expose] public section

/-!
# Celdas con signo de un perfil local (V13, S26 §5, parte B, global)

* `cells_assembly` — para cualquier elección de caminos diagonales de longitud `≤ D`
  (`D ≥ 1`) sobre los ciclos de entrada, las celdas `b_i` (todas las caras de todos los
  ciclos): son perfiles locales (con signo, en `M_H`); suman `x`; su número es `≤ 2‖x‖₁`;
  `‖b_i‖₁ ≤ 3D`; `Σ ‖b_i‖₁ ≤ 6D‖x‖₁`; y para cada vértice físico `v`,
  `#{i : v ∈ supp b_i} ≤ 3·d_abs(x)(v) + 2·#{diagonales cargadas en v}`.
* `zigzag_signed_cells` — la parte B con la hipótesis de que dos estados activos conectados
  están a distancia `≤ D` en la cubierta activa (se eligen geodésicas).
* `zigzag_signed_cells_prepared` — instancia de la hipótesis anterior con `D = 12C²` mediante
  `surv_dist_lt` de V12 con `A = ∅` (hipótesis de preparación: `≤ C` filas activas por raíz
  y componentes activas de tamaño `≥ n/C`).
-/

open Finset Classical

noncomputable section

namespace TypedTriangle.ActiveCover

open TypedTriangle.ComponentRows TypedTriangle.SignedCover TypedTriangle.Circulation
open TypedTriangle.Zigzag

variable {V I : Type*} [Fintype V] {G : SimpleGraph V} {lab : V → I} {F : Set (Multiset I)}

/-! ### Caminos de grafos sobre estados como caminos de estados -/

/-- Un camino en un grafo sobre un subtipo de estados cuya adyacencia es la de la cubierta
da un camino de estados con el mismo número de aristas. -/
lemma walk_isStPath {P : St V → Prop} {H : SimpleGraph {X // P X}}
    (hH : ∀ a b, H.Adj a b → CAdj G lab F a.1 b.1) {X Y : {X // P X}} (w : H.Walk X Y) :
    IsStPath G lab F X.1 Y.1 (w.support.map Subtype.val) ∧
      (w.support.map Subtype.val).length = w.length + 1 := by
  refine ⟨⟨?_, ?_, ?_⟩, by simp⟩
  · cases w <;> simp
  · rw [List.getLast?_map, List.getLast?_eq_some_getLast (by simp), w.getLast_support]; rfl
  · induction w with
    | nil => simp
    | @cons a b c h w ih =>
      rw [SimpleGraph.Walk.support_cons, List.map_cons]
      cases w with
      | nil => simpa using hH _ _ h
      | cons h' w' =>
        rw [SimpleGraph.Walk.support_cons, List.map_cons, List.isChain_cons_cons]
        refine ⟨hH _ _ h, ?_⟩
        rw [SimpleGraph.Walk.support_cons, List.map_cons] at ih
        exact ih

/-- Dos estados de un mismo ciclo ordenado están conectados en la cubierta activa. -/
lemma OrdCycle.reachable (c : OrdCycle G lab F) (hact : ∀ i, IsActiveRow G lab F (c.st i).1)
    (p q : ℕ) : (stateGraph G lab F).Reachable ⟨c.st p, hact p⟩ ⟨c.st q, hact q⟩ := by
  have step : ∀ i, (stateGraph G lab F).Reachable ⟨c.st i, hact i⟩ ⟨c.st (i + 1), hact (i + 1)⟩ := by
    intro i
    have hi : i % c.arcs.length < c.arcs.length := Nat.mod_lt _ c.len_pos
    have h := c.st_adj hi
    have e1 : c.st (i % c.arcs.length) = c.st i := by simp [OrdCycle.st]
    have e2 : c.st (i % c.arcs.length + 1) = c.st (i + 1) := by
      simp [OrdCycle.st, Nat.add_mod]
    rw [e1, e2] at h
    exact SimpleGraph.Adj.reachable h
  have h0 : ∀ i, (stateGraph G lab F).Reachable ⟨c.st 0, hact 0⟩ ⟨c.st i, hact i⟩ := by
    intro i
    induction i with
    | zero => rfl
    | succ i ih => exact ih.trans (step i)
  have hp : (stateGraph G lab F).Reachable ⟨c.st p, hact p⟩ ⟨c.st (p % c.arcs.length), hact _⟩ := by
    have : c.st (p % c.arcs.length) = c.st p := by simp [OrdCycle.st]
    simp only [this]; rfl
  exact (h0 p).symm.trans (h0 q)

/-! ### Ensamblaje de las celdas -/

/-- Celdas (físicas) de un ciclo con sus caminos diagonales. -/
def cellsOf (p : OrdCycle G lab F × (ℕ → List (St V))) : List (Sym2 V → ℤ) :=
  (List.range (p.1.arcs.length - 2)).map (fun k => extE G (p.1.cell p.2 k).1)

/-- `v` está en el soporte de `b`. -/
def InSupp (G : SimpleGraph V) (v : V) (b : Sym2 V → ℤ) : Prop :=
  ∃ e : Col G, v ∈ e.1 ∧ b e.1 ≠ 0

/-- Número de diagonales de un ciclo cargadas en `v`. -/
def chargedCount (p : OrdCycle G lab F × (ℕ → List (St V))) (v : V) : ℕ :=
  ((Icc 1 (p.1.arcs.length - 3)).filter (fun i => (∃ X ∈ p.2 i, X.1.1 = v) ∧
    (p.1.st (lo i)).1.1 ≠ v ∧ (p.1.st (hi p.1.arcs.length i)).1.1 ≠ v)).card

/-- Ocurrencias de la raíz `v` en un ciclo. -/
def occCount (c : OrdCycle G lab F) (v : V) : ℕ :=
  ((range c.arcs.length).filter (fun p => (c.st p).1.1 = v)).card

lemma countP_range_eq_card (n : ℕ) (P : ℕ → Prop) [DecidablePred P] :
    (List.range n).countP (fun k => decide (P k)) = ((range n).filter P).card := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [List.range_succ, List.countP_append, ih, Finset.range_add_one, Finset.filter_insert]
    by_cases h : P n
    · rw [if_pos h, card_insert_of_notMem (by simp)]; simp [h]
    · rw [if_neg h]; simp [h]

lemma norm1_extE (y : Col G → ℤ) : norm1 G (extE G y) = ∑ q, |y q| := by
  unfold norm1; simp [extE_col]

lemma sum_map_flatMap {α β : Type*} (l : List α) (f : α → List β) (g : β → ℤ) :
    ((l.flatMap f).map g).sum = (l.map (fun a => ((f a).map g).sum)).sum := by
  induction l with
  | nil => simp
  | cons a l ih => simp [List.flatMap_cons, ih]

omit [Fintype V] in
lemma sum_range_extE (n : ℕ) (y : ℕ → Col G → ℤ) (e : Sym2 V) :
    ((List.range n).map (fun k => extE G (y k) e)).sum = extE G (∑ k ∈ range n, y k) e := by
  induction n with
  | zero => simp [extE]
  | succ n ih =>
    rw [List.range_succ, List.map_append, List.sum_append, ih, Finset.sum_range_succ]
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]
    unfold extE
    split_ifs <;> simp

/-- **Ensamblaje (parte B, para caminos diagonales dados).** -/
theorem cells_assembly (x : Sym2 V → ℤ) (hx : IsLocalProfile G lab F x) (D : ℕ) (hD : 1 ≤ D)
    (cd : List (OrdCycle G lab F × (ℕ → List (St V))))
    (hsum : ∀ e : Col G,
      (cd.map (fun p => flowP _ (Circulation.ind p.1.arcs.toFinset) e)).sum = x e.1)
    (hlen : (((cd.map (fun p => p.1.arcs.length)).sum : ℕ) : ℤ) ≤ 2 * norm1 G x)
    (hspec : ∀ p ∈ cd, p.1.DiagSpec p.2 D) :
    (∀ b ∈ cd.flatMap cellsOf, IsLocalProfile G lab F b) ∧
      (∀ e, ((cd.flatMap cellsOf).map (fun b => b e)).sum = x e) ∧
      ((cd.flatMap cellsOf).length : ℤ) ≤ 2 * norm1 G x ∧
      (∀ b ∈ cd.flatMap cellsOf, norm1 G b ≤ 3 * D) ∧
      ((cd.flatMap cellsOf).map (norm1 G)).sum ≤ 6 * D * norm1 G x ∧
      ∀ v, (cd.flatMap cellsOf).countP (fun b => decide (InSupp G v b)) ≤
        (cd.map (fun p => 3 * occCount p.1 v + 2 * chargedCount p v)).sum := by
  have hmem : ∀ b ∈ cd.flatMap cellsOf, ∃ p ∈ cd, ∃ k < p.1.arcs.length - 2,
      b = extE G (p.1.cell p.2 k).1 := by
    intro b hb
    obtain ⟨p, hp, hb⟩ := List.mem_flatMap.mp hb
    obtain ⟨k, hk, rfl⟩ := List.mem_map.mp hb
    exact ⟨p, hp, k, List.mem_range.mp hk, rfl⟩
  have hnorm : ∀ b ∈ cd.flatMap cellsOf, norm1 G b ≤ 3 * D := by
    intro b hb
    obtain ⟨p, hp, k, hk, rfl⟩ := hmem b hb
    rw [norm1_extE]
    exact p.1.norm_cell_le p.2 hD (hspec p hp) hk
  have hlen' : (cd.flatMap cellsOf).length ≤ (cd.map (fun p => p.1.arcs.length)).sum := by
    rw [List.length_flatMap]
    refine List.sum_le_sum fun p _ => ?_
    simp [cellsOf]
  refine ⟨fun b hb => ?_, fun e => ?_, ?_, hnorm, ?_, fun v => ?_⟩
  · obtain ⟨p, hp, k, hk, rfl⟩ := hmem b hb
    exact p.1.cellP_isLocalProfile p.2 hD (hspec p hp) hk
  · have hcyc : ∀ p ∈ cd, ((cellsOf p).map (fun b => b e)).sum =
        extE G (fun q => flowP _ (Circulation.ind p.1.arcs.toFinset) q) e := by
      intro p _
      have h := congrArg Prod.fst (p.1.sum_cells p.2)
      simp only [Prod.fst_sum] at h
      unfold cellsOf
      rw [List.map_map, ← h]
      exact sum_range_extE _ _ e
    rw [sum_map_flatMap, List.map_congr_left (fun p hp => hcyc p hp)]
    by_cases he : e ∈ G.edgeSet
    · rw [← hsum ⟨e, he⟩]
      congr 1
      refine List.map_congr_left fun p _ => ?_
      simp [extE, he]
    · have hx0 : x e = 0 := hx.1 e (by rwa [SparseEdge.mem_edges])
      rw [hx0]
      refine List.sum_eq_zero fun y hy => ?_
      obtain ⟨p, -, rfl⟩ := List.mem_map.mp hy
      simp [extE, he]
  · exact (Nat.cast_le.mpr hlen').trans hlen
  · calc ((cd.flatMap cellsOf).map (norm1 G)).sum
        ≤ ((cd.flatMap cellsOf).map (fun _ => (3 * D : ℤ))).sum :=
          List.sum_le_sum fun b hb => hnorm b hb
      _ = 3 * D * (cd.flatMap cellsOf).length := by simp [mul_comm]
      _ ≤ 3 * D * (2 * norm1 G x) := by
          refine mul_le_mul_of_nonneg_left ((Nat.cast_le.mpr hlen').trans hlen) ?_
          positivity
      _ = 6 * D * norm1 G x := by ring
  · rw [List.countP_flatMap]
    refine List.sum_le_sum fun p hp => ?_
    have h := p.1.card_support_le p.2 v
    simp only [Function.comp, cellsOf, List.countP_map]
    have : (List.range (p.1.arcs.length - 2)).countP
        ((fun b => decide (InSupp G v b)) ∘ fun k => extE G (p.1.cell p.2 k).1) =
        ((range (p.1.arcs.length - 2)).filter
          (fun k => ∃ q : Col G, v ∈ q.1 ∧ (p.1.cell p.2 k).1 q ≠ 0)).card := by
      rw [← countP_range_eq_card]
      congr 1
      funext k
      simp only [Function.comp, InSupp, extE_col]
    rw [this]
    exact h

/-! ### Parte B con geodésicas -/

/-- Caminos diagonales geodésicos de un ciclo (si sus estados son activos). -/
def geoDiag (c : OrdCycle G lab F) (i : ℕ) : List (St V) :=
  if hact : ∀ i, IsActiveRow G lab F (c.st i).1 then
    (Classical.choose (c.reachable hact (lo i) (hi c.arcs.length i)).exists_walk_length_eq_dist
      ).support.map Subtype.val
  else []

lemma geoDiag_spec (c : OrdCycle G lab F) (hact : ∀ i, IsActiveRow G lab F (c.st i).1) (D : ℕ)
    (hshort : ∀ X Y : AState G lab F, (stateGraph G lab F).Reachable X Y →
      (stateGraph G lab F).dist X Y ≤ D) : c.DiagSpec (geoDiag c) D := by
  intro i _ _
  have hr := c.reachable hact (lo i) (hi c.arcs.length i)
  have hw := Classical.choose_spec hr.exists_walk_length_eq_dist
  have h := walk_isStPath (G := G) (lab := lab) (F := F) (H := stateGraph G lab F)
    (fun a b hab => hab) (Classical.choose hr.exists_walk_length_eq_dist)
  unfold geoDiag
  rw [dif_pos hact]
  refine ⟨h.1, ?_⟩
  rw [h.2, hw]
  exact Nat.add_le_add_right (hshort _ _ hr) 1

/-- **S26 §5, parte B.** Sea `x` un perfil local y supongamos que dos estados activos
conectados están a distancia `≤ D` (`D ≥ 1`) en la cubierta activa. Reemplazando cada diagonal
del zigzag por una geodésica (y la misma invertida en la cara adyacente) se obtienen celdas
`b_i` con signo tales que:
* cada `b_i` es un perfil local (en `M_H`; no necesariamente en `Λ_H` ni positivo);
* `Σ_i b_i = x`;
* el número de celdas es `≤ 2‖x‖₁`;
* `‖b_i‖₁ ≤ 3D` y `Σ_i ‖b_i‖₁ ≤ 6D‖x‖₁`. -/
theorem zigzag_signed_cells (x : Sym2 V → ℤ) (hx : IsLocalProfile G lab F x) (D : ℕ)
    (hD : 1 ≤ D)
    (hshort : ∀ X Y : AState G lab F, (stateGraph G lab F).Reachable X Y →
      (stateGraph G lab F).dist X Y ≤ D) :
    ∃ cells : List (Sym2 V → ℤ), (∀ b ∈ cells, IsLocalProfile G lab F b) ∧
      (∀ e, (cells.map (fun b => b e)).sum = x e) ∧
      (cells.length : ℤ) ≤ 2 * norm1 G x ∧
      (∀ b ∈ cells, norm1 G b ≤ 3 * D) ∧
      (cells.map (norm1 G)).sum ≤ 6 * D * norm1 G x := by
  obtain ⟨cs, hs1, hs2, hs3, -⟩ := exists_ordCycles x hx
  obtain ⟨h1, h2, h3, h4, h5, -⟩ := cells_assembly x hx D hD (cs.map (fun c => (c, geoDiag c)))
    (fun e => by rw [List.map_map]; exact hs1 e) (by rw [List.map_map]; exact hs2)
    (fun p hp => by
      obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hp
      exact geoDiag_spec c (hs3 c hc) D hshort)
  exact ⟨_, h1, h2, h3, h4, h5⟩

/-- La cubierta sin borrar (`A = ∅`) y la cubierta activa tienen la misma distancia (cota). -/
lemma dist_le_surv_empty {X Y : AState G lab F}
    (h : (survGraph G lab F ∅).Reachable ⟨X.1, X.2, Finset.notMem_empty _⟩
      ⟨Y.1, Y.2, Finset.notMem_empty _⟩) :
    (stateGraph G lab F).dist X Y ≤
      (survGraph G lab F ∅).dist ⟨X.1, X.2, Finset.notMem_empty _⟩
        ⟨Y.1, Y.2, Finset.notMem_empty _⟩ := by
  obtain ⟨w, hw⟩ := h.exists_walk_length_eq_dist
  let f : survGraph G lab F ∅ →g stateGraph G lab F :=
    ⟨fun z => ⟨z.1, z.2.1⟩, fun {a b} hab => hab⟩
  have := SimpleGraph.dist_le (w.map f)
  rw [SimpleGraph.Walk.length_map, hw] at this
  exact this

lemma deletionHyp_empty : DeletionHyp G lab F ∅ :=
  ⟨fun a ha => absurd ha (Finset.notMem_empty a), fun a ha => absurd ha (Finset.notMem_empty a),
    fun a ha => absurd ha (Finset.notMem_empty a), fun a ha => absurd ha (Finset.notMem_empty a)⟩

/-- **Parte B bajo las hipótesis de preparación** (`≤ C` filas activas por raíz, componentes
activas de tamaño `≥ n/C`, `n > 0`): las celdas existen con `D = max 1 (12C²)`, usando
`surv_dist_lt` de V12 con `A = ∅`. -/
theorem zigzag_signed_cells_prepared (x : Sym2 V → ℤ) (hx : IsLocalProfile G lab F x) (C : ℕ)
    (hn : 0 < Fintype.card V)
    (hrows : ∀ v, (univ.filter (fun j : Row V => j.1 = v ∧ IsActiveRow G lab F j)).card ≤ C)
    (hdeg : ∀ j : Row V, IsActiveRow G lab F j → Fintype.card V ≤ C * j.2.card) :
    ∃ cells : List (Sym2 V → ℤ), (∀ b ∈ cells, IsLocalProfile G lab F b) ∧
      (∀ e, (cells.map (fun b => b e)).sum = x e) ∧
      (cells.length : ℤ) ≤ 2 * norm1 G x ∧
      (∀ b ∈ cells, norm1 G b ≤ 3 * (max 1 (12 * C ^ 2) : ℕ)) ∧
      (cells.map (norm1 G)).sum ≤ 6 * (max 1 (12 * C ^ 2) : ℕ) * norm1 G x := by
  refine zigzag_signed_cells x hx _ (le_max_left _ _) fun X Y hXY => ?_
  obtain ⟨hr, hd⟩ := surv_dist_lt (A := ∅) deletionHyp_empty C hn hrows hdeg (by simp)
    (X := X) (Y := Y) (Finset.notMem_empty _) (Finset.notMem_empty _) hXY
  exact (dist_le_surv_empty hr).trans ((Nat.le_of_lt hd).trans (le_max_right _ _))

end TypedTriangle.ActiveCover
