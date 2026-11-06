/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import RequestProject.TypedTriangle.StatePaths
public import RequestProject.TypedTriangle.ZigzagPolygon

@[expose] public section

/-!
# Celdas con signo de un ciclo ordenado (V13, S26 §5, parte B, un ciclo)

Sea `c` un ciclo ordenado de la cubierta (`OrdCycle`: lista de arcos sin repeticiones,
longitud `L ≥ 3`, `tgt l[i] = src l[(i+1) mod L]`), con estados de vértice `c.st i`.
Sobre el zigzag de `ZigzagPolygon` se reemplaza cada diagonal `i` (`1 ≤ i ≤ L-3`) por un
camino de estados `dw i` de la cubierta activa entre `c.st (lo i)` y `c.st (hi i)`; en la
cara adyacente se usa EL MISMO camino invertido (`seg`), de modo que las proyecciones física y
virtual se cancelan exactamente. Los lados son los arcos originales.

* `cell_baug` — cada celda (proyección de un camino cerrado de tres segmentos) está en el
  núcleo aumentado; `cellP_isLocalProfile` — su parte física es un perfil local (grupo
  local `M_H`), por `kernel_isLocalProfile`. NO se supone que cada cara sea un triángulo
  permitido; la celda es un vector CON SIGNO, no necesariamente en `Λ_H` ni positivo.
* `sum_cells` — la suma de las `L-2` celdas es la proyección del ciclo (física y virtual).
* `norm_cell_le` — `‖b_k‖₁ ≤ 3D` si cada camino diagonal tiene longitud `≤ D` (`D ≥ 1`).
* `cell_support` — si `v` está en el soporte de la celda `k`, o bien `v` es la raíz física de
  un vértice de la cara `k`, o bien `v` es la raíz de un estado del camino de una diagonal
  `i` con `k ∈ {i-1, i}`, distinta de las raíces de los dos extremos de esa diagonal.
-/

open Finset Classical

noncomputable section

namespace TypedTriangle.ActiveCover

open TypedTriangle.ComponentRows TypedTriangle.SignedCover TypedTriangle.Circulation
open TypedTriangle.Zigzag

variable {V I : Type*} [Fintype V] {G : SimpleGraph V} {lab : V → I} {F : Set (Multiset I)}

/-! ### Caminos de estados con extremos -/

variable (G lab F) in
/-- `w` es un camino de estados de `X` a `Y` en la cubierta. -/
def IsStPath (X Y : St V) (w : List (St V)) : Prop :=
  w.head? = some X ∧ w.getLast? = some Y ∧ List.IsChain (CAdj G lab F) w

lemma isStPath_single (X : St V) : IsStPath G lab F X X [X] := by
  simp [IsStPath]

lemma isStPath_pair {X Y : St V} (h : CAdj G lab F X Y) : IsStPath G lab F X Y [X, Y] := by
  simp [IsStPath, h]

lemma IsStPath.reverse {X Y : St V} {w : List (St V)} (h : IsStPath G lab F X Y w) :
    IsStPath G lab F Y X w.reverse := by
  obtain ⟨h1, h2, h3⟩ := h
  refine ⟨by rw [List.head?_reverse, h2], by rw [List.getLast?_reverse, h1], ?_⟩
  rw [List.isChain_reverse]
  exact h3.imp fun a b hab => cadj_symm hab

lemma IsStPath.eq_cons {X Y : St V} {w : List (St V)} (h : IsStPath G lab F X Y w) :
    ∃ t, w = X :: t := by
  obtain ⟨h1, -, -⟩ := h
  cases w with
  | nil => simp at h1
  | cons a t => simp at h1; exact ⟨t, by rw [h1]⟩

lemma IsStPath.baug {X Y : St V} {w : List (St V)} (h : IsStPath G lab F X Y w) (j : Row V) :
    baug (rowSys G lab F) (pathP G lab F w) (pathV G lab F w) j = stBd X j - stBd Y j := by
  obtain ⟨t, rfl⟩ := h.eq_cons
  rw [baug_path X t h.2.2 j]
  have h2 := h.2.1
  rw [List.getLast?_eq_some_getLast (by simp)] at h2
  simp only [Option.some.injEq] at h2
  rw [h2]

/-- **La proyección de todo camino CERRADO de la cubierta está en el núcleo aumentado.** -/
theorem IsStPath.baug_closed {X : St V} {w : List (St V)} (h : IsStPath G lab F X X w)
    (j : Row V) :
    SignedCover.baug (rowSys G lab F) (pathP G lab F w) (pathV G lab F w) j = 0 := by
  rw [IsStPath.baug h, sub_self]

/-- **La parte física de la proyección de todo camino cerrado es un perfil local**
(`kernel_isLocalProfile`); es un vector con signo de `M_H`. -/
theorem IsStPath.closed_isLocalProfile {X : St V} {w : List (St V)}
    (h : IsStPath G lab F X X w) : IsLocalProfile G lab F (extE G (pathP G lab F w)) :=
  kernel_isLocalProfile G lab F _ (pathV G lab F w) (fun _ hj => pathV_bip w hj) (IsStPath.baug_closed h)

lemma IsStPath.norm_le {X Y : St V} {w : List (St V)} (h : IsStPath G lab F X Y w) :
    ∑ q, |pathP G lab F w q| + ∑ j, |pathV G lab F w j| ≤ (w.length : ℤ) - 1 := by
  obtain ⟨t, rfl⟩ := h.eq_cons
  have := norm_path_le (G := G) (lab := lab) (F := F) X t
  simp only [List.length_cons, Nat.cast_add, Nat.cast_one]
  linarith

lemma normP_le_of_isStPath {X Y : St V} {w : List (St V)} (h : IsStPath G lab F X Y w) :
    ∑ q, |pathP G lab F w q| ≤ (w.length : ℤ) - 1 := by
  have h1 := h.norm_le
  have h2 : 0 ≤ ∑ j, |pathV G lab F w j| := Finset.sum_nonneg fun j _ => abs_nonneg _
  linarith

/-! ### Ciclos ordenados -/

variable (G lab F) in
/-- Ciclo ordenado de la cubierta de longitud `≥ 3`. -/
structure OrdCycle where
  arcs : List (Arc (rowSys G lab F))
  nodup : arcs.Nodup
  src_nodup : (arcs.map (src _)).Nodup
  len3 : 3 ≤ arcs.length
  cyc : ∀ (i : ℕ) (hi : i < arcs.length),
    tgt _ arcs[i] = src _ (arcs[(i + 1) % arcs.length]'(Nat.mod_lt _ (by omega)))

namespace OrdCycle

variable (c : OrdCycle G lab F)

lemma len_pos : 0 < c.arcs.length := by have := c.len3; omega

/-- Estado del vértice `i` (índices módulo `L`). -/
def st (i : ℕ) : St V := src _ (c.arcs[i % c.arcs.length]'(Nat.mod_lt _ c.len_pos))

lemma st_of_lt {i : ℕ} (hi : i < c.arcs.length) : c.st i = src _ c.arcs[i] := by
  simp only [st, Nat.mod_eq_of_lt hi]

lemma tgt_eq_st {i : ℕ} (hi : i < c.arcs.length) : tgt _ c.arcs[i] = c.st (i + 1) := by
  rw [c.cyc i hi]; rfl

lemma st_adj {i : ℕ} (hi : i < c.arcs.length) : CAdj G lab F (c.st i) (c.st (i + 1)) :=
  ⟨c.arcs[i], (c.st_of_lt hi).symm, c.tgt_eq_st hi⟩

lemma st_adj_last : CAdj G lab F (c.st (c.arcs.length - 1)) (c.st 0) := by
  have h := c.st_adj (i := c.arcs.length - 1) (by have := c.len3; omega)
  rwa [show c.arcs.length - 1 + 1 = c.arcs.length by have := c.len3; omega,
    show c.st c.arcs.length = c.st 0 by simp [st]] at h

/-- Proyección física del ciclo como suma de aristas. -/
lemma flowP_eq (q : Col G) :
    flowP _ (Circulation.ind c.arcs.toFinset) q =
      ∑ i ∈ range c.arcs.length, edgeProjP G lab F (c.st i) (c.st ((i + 1) % c.arcs.length)) q := by
  rw [cycle_walk_proj G lab F c.nodup (fun α => List.mem_toFinset.symm) c.cyc q,
    ← Fin.sum_univ_eq_sum_range]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [c.st_of_lt i.2, c.st_of_lt (Nat.mod_lt _ c.len_pos)]

lemma flowV_eq (j : Row V) :
    flowV _ (Circulation.ind c.arcs.toFinset) j =
      ∑ i ∈ range c.arcs.length, edgeProjV G lab F (c.st i) (c.st ((i + 1) % c.arcs.length)) j := by
  rw [cycle_walk_projV G lab F c.nodup (fun α => List.mem_toFinset.symm) c.cyc j,
    ← Fin.sum_univ_eq_sum_range]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [c.st_of_lt i.2, c.st_of_lt (Nat.mod_lt _ c.len_pos)]

/-! ### Segmentos y celdas -/

variable (dw : ℕ → List (St V))

/-- Segmento de `p` a `q` con `p < q`: lado original, lado de cierre invertido o diagonal. -/
def segUp (p q : ℕ) : List (St V) :=
  if q = p + 1 then [c.st p, c.st q]
  else if p = 0 ∧ q = c.arcs.length - 1 then [c.st 0, c.st (c.arcs.length - 1)]
  else dw (c.arcs.length - 1 - (q - p))

/-- Segmento orientado de `p` a `q`: el de `q` a `p` invertido si `q < p`. -/
def seg (p q : ℕ) : List (St V) :=
  if p < q then c.segUp dw p q else if q < p then (c.segUp dw q p).reverse else [c.st p]

/-- Proyección (física, virtual) de un segmento. -/
def gP (p q : ℕ) : (Col G → ℤ) × (Row V → ℤ) :=
  (pathP G lab F (c.seg dw p q), pathV G lab F (c.seg dw p q))

lemma gP_antisymm (p q : ℕ) : c.gP dw q p = - c.gP dw p q := by
  unfold gP seg
  rcases lt_trichotomy p q with h | rfl | h
  · simp only [h, if_true, show ¬ q < p from by omega, if_false, pathP_reverse, pathV_reverse,
      Prod.neg_mk]
  · simp [pathP, pathV]
  · simp only [h, if_true, show ¬ p < q from by omega, if_false, pathP_reverse, pathV_reverse,
      Prod.neg_mk, neg_neg]

/-- **Celda `k`** (física y virtual): borde orientado de la cara `k` con los segmentos. -/
def cell (k : ℕ) : (Col G → ℤ) × (Row V → ℤ) := faceBd (c.gP dw) (face c.arcs.length k)

/-- Especificación de los caminos diagonales: de `st (lo i)` a `st (hi i)`, longitud `≤ D`. -/
def DiagSpec (D : ℕ) : Prop :=
  ∀ i, 1 ≤ i → i ≤ c.arcs.length - 3 →
    IsStPath G lab F (c.st (lo i)) (c.st (hi c.arcs.length i)) (dw i) ∧ (dw i).length ≤ D + 1

lemma segUp_diag {i : ℕ} (h1 : 1 ≤ i) (h2 : i ≤ c.arcs.length - 3) :
    c.segUp dw (lo i) (hi c.arcs.length i) = dw i := by
  unfold segUp
  rw [if_neg (by unfold lo hi; omega), if_neg (by unfold lo hi; omega)]
  congr 1; unfold lo hi; omega

lemma diag_lt {i : ℕ} (h2 : i ≤ c.arcs.length - 3) : lo i < hi c.arcs.length i := by
  have := c.len3; unfold lo hi; omega

/-- **Cada segmento de una cara es un camino de estados de longitud `≤ D`.** -/
theorem seg_isStPath {D : ℕ} (hD : 1 ≤ D) (hdw : c.DiagSpec dw D) {k : ℕ} (hk : k < c.arcs.length - 2)
    {e : ℕ × ℕ} (he : e ∈ oEdges (face c.arcs.length k)) :
    IsStPath G lab F (c.st e.1) (c.st e.2) (c.seg dw e.1 e.2) ∧
      (c.seg dw e.1 e.2).length ≤ D + 1 := by
  have hL := c.len3
  rcases edge_cases hL hk he with hs | ⟨i, hi1, hi2, rfl | rfl⟩
  · rcases hs with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · obtain ⟨p, q⟩ := e
      simp only at h1 h2
      subst h1
      unfold seg segUp
      simp only [show p < p + 1 from by omega, if_true]
      exact ⟨isStPath_pair (c.st_adj (by omega)), by simp; omega⟩
    · obtain ⟨p, q⟩ := e
      simp only at h1 h2
      subst h1 h2
      unfold seg segUp
      simp only [show ¬ c.arcs.length - 1 < 0 from by omega, if_false, show 0 < c.arcs.length - 1 from by omega,
        if_true, show ¬ c.arcs.length - 1 = 0 + 1 from by omega, true_and]
      refine ⟨?_, by simp; omega⟩
      exact (isStPath_pair (cadj_symm c.st_adj_last)).reverse
  · simp only [Zigzag.diag]
    unfold seg
    rw [if_pos (c.diag_lt hi2), c.segUp_diag dw hi1 hi2]
    exact hdw i hi1 hi2
  · simp only [Zigzag.diag]
    unfold seg
    rw [if_neg (by have := c.diag_lt hi2; omega), if_pos (c.diag_lt hi2),
      c.segUp_diag dw hi1 hi2, List.length_reverse]
    exact ⟨(hdw i hi1 hi2).1.reverse, (hdw i hi1 hi2).2⟩

lemma cell_eq (k : ℕ) : c.cell dw k =
    c.gP dw (lo k) (third c.arcs.length k) + c.gP dw (third c.arcs.length k) (hi c.arcs.length k) +
      c.gP dw (hi c.arcs.length k) (lo k) := rfl

lemma mem_oEdges_face (k : ℕ) :
    (lo k, third c.arcs.length k) ∈ oEdges (face c.arcs.length k) ∧
      (third c.arcs.length k, hi c.arcs.length k) ∈ oEdges (face c.arcs.length k) ∧
      (hi c.arcs.length k, lo k) ∈ oEdges (face c.arcs.length k) := by
  simp [oEdges_face]

/-- **Cada celda está en el núcleo aumentado** (proyección de un camino cerrado). -/
theorem cell_baug {D : ℕ} (hD : 1 ≤ D) (hdw : c.DiagSpec dw D) {k : ℕ} (hk : k < c.arcs.length - 2)
    (j : Row V) : baug (rowSys G lab F) (c.cell dw k).1 (c.cell dw k).2 j = 0 := by
  obtain ⟨m1, m2, m3⟩ := c.mem_oEdges_face k
  rw [c.cell_eq]
  simp only [Prod.fst_add, Prod.snd_add, baug_add]
  unfold gP
  rw [(c.seg_isStPath dw hD hdw hk m1).1.baug, (c.seg_isStPath dw hD hdw hk m2).1.baug,
    (c.seg_isStPath dw hD hdw hk m3).1.baug]
  ring

lemma cellV_bip (k : ℕ) {j : Row V} (hj : IsBip G lab F j) : (c.cell dw k).2 j = 0 := by
  rw [c.cell_eq]
  simp only [Prod.snd_add, Pi.add_apply, gP, pathV_bip _ hj, add_zero]

/-- **La parte física de cada celda es un perfil local** (está en `M_H`; con signo). -/
theorem cellP_isLocalProfile {D : ℕ} (hD : 1 ≤ D) (hdw : c.DiagSpec dw D) {k : ℕ}
    (hk : k < c.arcs.length - 2) : IsLocalProfile G lab F (extE G (c.cell dw k).1) :=
  kernel_isLocalProfile G lab F _ (c.cell dw k).2 (fun _ hj => c.cellV_bip dw k hj)
    (c.cell_baug dw hD hdw hk)

/-- **La suma de las `L - 2` celdas es la proyección del ciclo.** -/
theorem sum_cells :
    ∑ k ∈ range (c.arcs.length - 2), c.cell dw k =
      (flowP _ (Circulation.ind c.arcs.toFinset), flowV _ (Circulation.ind c.arcs.toFinset)) := by
  have hL := c.len3
  have h := polyFaces_sum (c.gP dw) (fun p q => c.gP_antisymm dw p q) hL
  rw [polyFaces_eq hL, List.map_map] at h
  have h' : ∑ k ∈ range (c.arcs.length - 2), c.cell dw k = ((List.range (c.arcs.length - 2)).map
      (faceBd (c.gP dw) ∘ face c.arcs.length)).sum := by
    rw [← List.sum_toFinset _ List.nodup_range, List.toFinset_range]
    rfl
  rw [h', h]
  have hs : ∀ i ∈ range c.arcs.length, c.gP dw i ((i + 1) % c.arcs.length) =
      (edgeProjP G lab F (c.st i) (c.st ((i + 1) % c.arcs.length)),
        edgeProjV G lab F (c.st i) (c.st ((i + 1) % c.arcs.length))) := by
    intro i hi
    rw [mem_range] at hi
    by_cases hlast : i = c.arcs.length - 1
    · subst hlast
      rw [show c.arcs.length - 1 + 1 = c.arcs.length by omega, Nat.mod_self, ← neg_neg (c.gP dw _ 0),
        ← c.gP_antisymm]
      unfold gP seg segUp
      simp only [show 0 < c.arcs.length - 1 from by omega, if_true, show ¬ c.arcs.length - 1 = 0 + 1 from by omega,
        if_false, true_and]
      simp only [pathP, pathV, chainSum_cons_cons, chainSum_single, add_zero, Prod.neg_mk]
      ext x
      · simp only [Pi.neg_apply]; rw [edgeProjP_swap, neg_neg]
      · simp only [Pi.neg_apply]; rw [edgeProjV_swap, neg_neg]
    · rw [Nat.mod_eq_of_lt (by omega)]
      unfold gP seg segUp
      simp only [show i < i + 1 from by omega, if_true]
      simp [pathP, pathV, chainSum_cons_cons]
  rw [Finset.sum_congr rfl hs]
  ext x
  · simp only [Prod.fst_sum, Finset.sum_apply]
    rw [c.flowP_eq]
  · simp only [Prod.snd_sum, Finset.sum_apply]
    rw [c.flowV_eq]

/-- **Norma de cada celda**: `‖b_k‖₁ ≤ 3D`. -/
theorem norm_cell_le {D : ℕ} (hD : 1 ≤ D) (hdw : c.DiagSpec dw D) {k : ℕ} (hk : k < c.arcs.length - 2) :
    ∑ q, |(c.cell dw k).1 q| ≤ 3 * D := by
  obtain ⟨m1, m2, m3⟩ := c.mem_oEdges_face k
  rw [c.cell_eq]
  simp only [Prod.fst_add, Pi.add_apply]
  have e1 := c.seg_isStPath dw hD hdw hk m1
  have e2 := c.seg_isStPath dw hD hdw hk m2
  have e3 := c.seg_isStPath dw hD hdw hk m3
  have n1 := normP_le_of_isStPath e1.1
  have n2 := normP_le_of_isStPath e2.1
  have n3 := normP_le_of_isStPath e3.1
  have l1 : ((c.seg dw (lo k) (third c.arcs.length k)).length : ℤ) ≤ D + 1 := by
    exact_mod_cast e1.2
  have l2 : ((c.seg dw (third c.arcs.length k) (hi c.arcs.length k)).length : ℤ) ≤ D + 1 := by
    exact_mod_cast e2.2
  have l3 : ((c.seg dw (hi c.arcs.length k) (lo k)).length : ℤ) ≤ D + 1 := by
    exact_mod_cast e3.2
  have key : ∀ q, |(c.gP dw (lo k) (third c.arcs.length k)).1 q +
      (c.gP dw (third c.arcs.length k) (hi c.arcs.length k)).1 q +
      (c.gP dw (hi c.arcs.length k) (lo k)).1 q| ≤
      |(c.gP dw (lo k) (third c.arcs.length k)).1 q| +
      |(c.gP dw (third c.arcs.length k) (hi c.arcs.length k)).1 q| +
      |(c.gP dw (hi c.arcs.length k) (lo k)).1 q| := fun q =>
    (abs_add_le _ _).trans (add_le_add (abs_add_le _ _) le_rfl)
  refine (Finset.sum_le_sum fun q _ => key q).trans ?_
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
  simp only [gP] at *
  linarith

/-! ### Soporte de las celdas -/

lemma seg_diag {i : ℕ} (h1 : 1 ≤ i) (h2 : i ≤ c.arcs.length - 3) :
    c.seg dw (lo i) (hi c.arcs.length i) = dw i ∧
      c.seg dw (hi c.arcs.length i) (lo i) = (dw i).reverse := by
  have hlt := c.diag_lt h2
  unfold seg
  rw [if_pos hlt, if_neg (by omega), if_pos hlt, c.segUp_diag dw h1 h2]
  exact ⟨rfl, rfl⟩

lemma mem_seg_side {e : ℕ × ℕ} (hs : IsSide c.arcs.length e) {X : St V}
    (hX : X ∈ c.seg dw e.1 e.2) : X = c.st e.1 ∨ X = c.st e.2 := by
  have hL := c.len3
  obtain ⟨p, q⟩ := e
  rcases hs with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · simp only at h1 h2 hX ⊢
    subst h1
    unfold seg segUp at hX
    simp only [show p < p + 1 from by omega, if_true, List.mem_cons,
      List.not_mem_nil, or_false] at hX
    exact hX
  · simp only at h1 h2 hX ⊢
    subst h1 h2
    unfold seg segUp at hX
    simp only [show ¬ c.arcs.length - 1 < 0 from by omega, if_false,
      show 0 < c.arcs.length - 1 from by omega, if_true,
      show ¬ c.arcs.length - 1 = 0 + 1 from by omega, true_and, List.reverse_cons,
      List.reverse_nil, List.nil_append, List.cons_append, List.mem_cons,
      List.not_mem_nil, or_false] at hX
    tauto

lemma mem_verts_of_mem_oEdges {f : ℕ × ℕ × ℕ} {e : ℕ × ℕ} (he : e ∈ oEdges f) :
    e.1 ∈ verts f ∧ e.2 ∈ verts f := by
  simp only [oEdges, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with rfl | rfl | rfl <;> simp [verts]

/-- **Soporte de una celda.** Si `v` está en el soporte de la celda `k` (una arista `e ∋ v`
con coeficiente no nulo), entonces o bien `v` es la raíz física de un vértice de la cara `k`,
o bien existe una diagonal `i` con `k ∈ {i-1, i}`, cuyo camino visita un estado de raíz `v`,
y `v` NO es la raíz de ninguno de sus dos extremos. -/
theorem cell_support {k : ℕ} (hk : k < c.arcs.length - 2) {q : Col G}
    (hq : (c.cell dw k).1 q ≠ 0) {v : V} (hv : v ∈ q.1) :
    (∃ p ∈ verts (face c.arcs.length k), (c.st p).1.1 = v) ∨
      ∃ i, 1 ≤ i ∧ i ≤ c.arcs.length - 3 ∧ (k = i - 1 ∨ k = i) ∧ (∃ X ∈ dw i, X.1.1 = v) ∧
        (c.st (lo i)).1.1 ≠ v ∧ (c.st (hi c.arcs.length i)).1.1 ≠ v := by
  have hL := c.len3
  obtain ⟨m1, m2, m3⟩ := c.mem_oEdges_face k
  have key : ∃ e ∈ oEdges (face c.arcs.length k), pathP G lab F (c.seg dw e.1 e.2) q ≠ 0 := by
    rw [c.cell_eq] at hq
    simp only [Prod.fst_add, Pi.add_apply, gP] at hq
    by_contra hcon
    push_neg at hcon
    rw [hcon _ m1, hcon _ m2, hcon _ m3] at hq
    simp at hq
  obtain ⟨e, he, hne⟩ := key
  obtain ⟨X, hX, hXv⟩ := pathP_ne_zero_root hne hv
  have hev := mem_verts_of_mem_oEdges he
  rcases edge_cases hL hk he with hs | ⟨i, hi1, hi2, hei | hei⟩
  · left
    rcases c.mem_seg_side dw hs hX with rfl | rfl
    · exact ⟨e.1, hev.1, hXv⟩
    · exact ⟨e.2, hev.2, hXv⟩
  · subst hei
    simp only [Zigzag.diag] at hev hX
    rw [(c.seg_diag dw hi1 hi2).1] at hX
    by_cases h1 : (c.st (lo i)).1.1 = v
    · exact Or.inl ⟨lo i, hev.1, h1⟩
    by_cases h2 : (c.st (hi c.arcs.length i)).1.1 = v
    · exact Or.inl ⟨hi c.arcs.length i, hev.2, h2⟩
    right
    refine ⟨i, hi1, hi2, Or.inl ?_, ⟨X, hX, hXv⟩, h1, h2⟩
    have := faces_with_diag hi1 hi2
    have hmem : k ∈ (range (c.arcs.length - 2)).filter
        (fun j => diag c.arcs.length i ∈ oEdges (face c.arcs.length j)) :=
      mem_filter.mpr ⟨mem_range.mpr hk, he⟩
    rw [this] at hmem
    exact mem_singleton.mp hmem
  · subst hei
    simp only [Zigzag.diag] at hev hX
    rw [(c.seg_diag dw hi1 hi2).2, List.mem_reverse] at hX
    by_cases h1 : (c.st (lo i)).1.1 = v
    · exact Or.inl ⟨lo i, hev.2, h1⟩
    by_cases h2 : (c.st (hi c.arcs.length i)).1.1 = v
    · exact Or.inl ⟨hi c.arcs.length i, hev.1, h2⟩
    right
    refine ⟨i, hi1, hi2, Or.inr ?_, ⟨X, hX, hXv⟩, h1, h2⟩
    have := faces_with_diag_rev hi1 hi2
    have hmem : k ∈ (range (c.arcs.length - 2)).filter
        (fun j => ((diag c.arcs.length i).2, (diag c.arcs.length i).1) ∈
          oEdges (face c.arcs.length j)) :=
      mem_filter.mpr ⟨mem_range.mpr hk, he⟩
    rw [this] at hmem
    exact mem_singleton.mp hmem

lemma verts_lt {k p : ℕ} (hk : k < c.arcs.length - 2) (hp : p ∈ verts (face c.arcs.length k)) :
    p < c.arcs.length := by
  simp only [verts, face, lo, hi, third, List.mem_cons, List.not_mem_nil, or_false] at hp
  by_cases h2 : k % 2 = 0 <;> simp only [h2, ↓reduceIte] at hp <;> omega

/-- **Cuenta de celdas por vértice físico (un ciclo).** El número de celdas cuyo soporte
contiene `v` es a lo sumo `3 · #{p : raíz(st p) = v} + 2 · #{diagonales cargadas en v}`, donde
una diagonal `i` está *cargada en `v`* si su camino visita un estado de raíz `v` y `v` no es
la raíz de ninguno de sus extremos. Las visitas a la raíz de un extremo se cargan a los
vértices del polígono (término `3·#`). -/
theorem card_support_le (v : V) :
    ((range (c.arcs.length - 2)).filter
        (fun k => ∃ q : Col G, v ∈ q.1 ∧ (c.cell dw k).1 q ≠ 0)).card ≤
      3 * ((range c.arcs.length).filter (fun p => (c.st p).1.1 = v)).card +
        2 * ((Icc 1 (c.arcs.length - 3)).filter (fun i => (∃ X ∈ dw i, X.1.1 = v) ∧
          (c.st (lo i)).1.1 ≠ v ∧ (c.st (hi c.arcs.length i)).1.1 ≠ v)).card := by
  set Pv := (range c.arcs.length).filter (fun p => (c.st p).1.1 = v)
  set Dv := (Icc 1 (c.arcs.length - 3)).filter (fun i => (∃ X ∈ dw i, X.1.1 = v) ∧
    (c.st (lo i)).1.1 ≠ v ∧ (c.st (hi c.arcs.length i)).1.1 ≠ v)
  have hsub : (range (c.arcs.length - 2)).filter
      (fun k => ∃ q : Col G, v ∈ q.1 ∧ (c.cell dw k).1 q ≠ 0) ⊆
      Pv.biUnion (fun p => (range (c.arcs.length - 2)).filter
        (fun k => p ∈ verts (face c.arcs.length k))) ∪ Dv.biUnion (fun i => {i - 1, i}) := by
    intro k hk
    obtain ⟨hk1, q, hvq, hq⟩ := mem_filter.mp hk
    have hk1' := mem_range.mp hk1
    rcases c.cell_support dw hk1' hq hvq with ⟨p, hp, hpv⟩ | ⟨i, hi1, hi2, hki, hX, h1, h2⟩
    · refine mem_union_left _ (mem_biUnion.mpr ⟨p, ?_, ?_⟩)
      · exact mem_filter.mpr ⟨mem_range.mpr (c.verts_lt hk1' hp), hpv⟩
      · exact mem_filter.mpr ⟨hk1, hp⟩
    · refine mem_union_right _ (mem_biUnion.mpr ⟨i, ?_, ?_⟩)
      · exact mem_filter.mpr ⟨mem_Icc.mpr ⟨hi1, hi2⟩, hX, h1, h2⟩
      · rcases hki with rfl | rfl <;> simp
  refine (card_le_card hsub).trans ((card_union_le _ _).trans (add_le_add ?_ ?_))
  · refine card_biUnion_le.trans ?_
    rw [mul_comm]
    exact Finset.sum_le_card_nsmul _ _ _ fun p _ => card_faces_at_le_three _ _
  · refine card_biUnion_le.trans ?_
    rw [mul_comm]
    exact Finset.sum_le_card_nsmul _ _ _ fun i _ => card_le_two

end OrdCycle

end TypedTriangle.ActiveCover
