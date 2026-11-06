/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import RequestProject.TypedTriangle.ComponentRows
public import RequestProject.TypedTriangle.OrderedCycle

@[expose] public section

/-!
# Portador activo de la cubierta de filas de componentes (V12, Prioridad 2)

`ComponentRows.Row V = V × Finset V` tiene exponencialmente muchas filas formales. Aquí se
define, SIN modificar `ComponentRows`, el portador activo:

* `LinkActive v u` — `u` no es aislado en el enlace `L_v` (la arista `vu` tiene un tercero
  permitido);
* `IsActiveRow (v, K)` — `K = comp v u` para un `u` no aislado de `L_v` (una componente
  real, no aislada, del enlace);
* `AState` — estados activos `((v, K), s)`.

Resultados (sin hipótesis de preparación):

* `linkActive_of_ne_zero` — un perfil local es nulo en toda arista sin tercero permitido;
* `arc_active_of_conformal` — todo arco conforme (proyección física/virtual compatible en
  signo con `(x, zLift x)`) tiene origen y destino activos;
* `local_profile_active_ordered_cycles` — la descomposición de `local_profile_cover_cycles`
  con, además, todos los estados de todos los ciclos activos y un orden cíclico explícito
  (lista) de cada ciclo, sin premisa de proveedor de orden;
* `stateGraph` — grafo simple no dirigido de estados activos, construido con los arcos
  `src/tgt` existentes; entre dos estados hay a lo sumo un arco en cada sentido
  (`arc_unique`), el inverso tiene proyección opuesta (`projP_rev`, `projV_rev`), y la
  proyección firmada de una arista del grafo coincide con la del arco (`edgeProjP_arc`);
  todo ciclo ordenado es un camino cerrado del grafo con la misma proyección
  (`cycle_walk_adj`, `cycle_walk_proj`).
* cotas (hipótesis geométricas auxiliares del núcleo preparado, no premisas de T):
  `card_AState_le` (`≤ 2 C n` si hay `≤ C` filas activas por raíz) y `card_le_degree`
  (grado `≥ |K|`, luego `n ≤ C · grado` si las componentes activas tienen tamaño `≥ n/C`).
-/

open Finset Classical

noncomputable section

namespace TypedTriangle.ActiveCover

open TypedTriangle.ComponentRows TypedTriangle.SignedCover TypedTriangle.Circulation

variable {V I : Type*} [Fintype V] (G : SimpleGraph V) (lab : V → I) (F : Set (Multiset I))

/-- `u` no es aislado en el enlace de `v`. -/
def LinkActive (v u : V) : Prop := ∃ w, (link G lab F v).Adj u w

/-- Fila activa: una componente real no aislada del enlace de su raíz. -/
def IsActiveRow (j : Row V) : Prop := ∃ u, LinkActive G lab F j.1 u ∧ comp G lab F j.1 u = j.2

/-- Estados activos de la cubierta. -/
abbrev AState := {st : Row V × Bool // IsActiveRow G lab F st.1}

/-! ### Perfiles locales: soporte en aristas con tercero permitido -/

variable {G lab F}

omit [Fintype V] in
lemma linkActive_of_allowed {v u w : V} (hT : SparseEdge.IsAllowed G lab F {v, u, w})
    (huw : u ≠ w) : LinkActive G lab F v u := ⟨w, huw, hT⟩

omit [Fintype V] in
lemma allowed_eq_triple {T : Finset V} (hT : T.card = 3) {v u : V} (hv : v ∈ T) (hu : u ∈ T)
    (hvu : v ≠ u) : ∃ w, w ≠ v ∧ w ≠ u ∧ T = {v, u, w} := by
  have h1 : ((T.erase v).erase u).card = 1 := by
    rw [Finset.card_erase_of_mem (Finset.mem_erase.mpr ⟨hvu.symm, hu⟩),
      Finset.card_erase_of_mem hv, hT]
  obtain ⟨w, hw⟩ := Finset.card_eq_one.mp h1
  have hwm : w ∈ (T.erase v).erase u := hw ▸ Finset.mem_singleton_self w
  simp only [Finset.mem_erase] at hwm
  obtain ⟨hwu, hwv, hwT⟩ := hwm
  refine ⟨w, hwv, hwu, ?_⟩
  symm
  apply Finset.eq_of_subset_of_card_le
  · intro y hy
    simp only [Finset.mem_insert, Finset.mem_singleton] at hy
    rcases hy with rfl | rfl | rfl <;> assumption
  · rw [hT, Finset.card_insert_of_notMem (by simp [hvu, hwv.symm]),
      Finset.card_pair (Ne.symm hwu)]

/-- **Un perfil local es nulo en toda arista sin tercero permitido**: si `x_{vu} ≠ 0`,
entonces `u` no es aislado en el enlace de `v`. -/
lemma linkActive_of_ne_zero {x : Sym2 V → ℤ} (hx : IsLocalProfile G lab F x) {v u : V}
    (hvu : v ≠ u) (h : x s(v, u) ≠ 0) : LinkActive G lab F v u := by
  obtain ⟨c, hc⟩ := hx.2 v
  rw [hc u (Ne.symm hvu)] at h
  obtain ⟨T, hT, -⟩ := Finset.exists_ne_zero_of_sum_ne_zero h
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hT
  obtain ⟨⟨hA, hv⟩, hu⟩ := hT
  obtain ⟨w, -, hwu, rfl⟩ := allowed_eq_triple hA.1 hv hu hvu
  exact linkActive_of_allowed hA (Ne.symm hwu)

lemma row1_active {x : Sym2 V → ℤ} (hx : IsLocalProfile G lab F x) (e : Col G)
    (h : x e.1 ≠ 0) : IsActiveRow G lab F (row1 G lab F e) := by
  refine ⟨(ends G e).2, linkActive_of_ne_zero hx (ends_ne G e) ?_, rfl⟩
  show x s((ends G e).1, (ends G e).2) ≠ 0
  rwa [ends_spec]

lemma row2_active {x : Sym2 V → ℤ} (hx : IsLocalProfile G lab F x) (e : Col G)
    (h : x e.1 ≠ 0) : IsActiveRow G lab F (row2 G lab F e) := by
  refine ⟨(ends G e).1, linkActive_of_ne_zero hx (Ne.symm (ends_ne G e)) ?_, rfl⟩
  show x s((ends G e).2, (ends G e).1) ≠ 0
  rwa [Sym2.eq_swap, ends_spec]

/-- Una coordenada virtual no nula del lift sólo aparece en filas activas. -/
lemma zLift_active {x : Sym2 V → ℤ} (hx : IsLocalProfile G lab F x) (j : Row V)
    (h : zLift G lab F x j ≠ 0) : IsActiveRow G lab F j := by
  unfold zLift at h
  split_ifs at h with hB
  · exact absurd rfl h
  have hs : ∑ e : Col G, term G lab F x e j ≠ 0 := by
    intro h0; rw [h0] at h; exact h (by simp)
  rw [sum_term_eq G lab F x hx.1 j] at hs
  obtain ⟨u, -, hu⟩ := Finset.exists_ne_zero_of_sum_ne_zero hs
  split_ifs at hu with hK
  · have hxu : x s(j.1, u) ≠ 0 := fun h0 => hu (by rw [h0, mul_zero])
    have hne : j.1 ≠ u := by
      rintro rfl
      exact hxu (hx.1 _ (by rw [SparseEdge.mem_edges, SimpleGraph.mem_edgeSet]; exact G.irrefl))
    exact ⟨u, linkActive_of_ne_zero hx hne hxu, hK⟩
  · exact absurd rfl hu

lemma sgn_ne_zero (b : Bool) : sgn b ≠ 0 := by cases b <;> simp [sgn]

/-- **Los arcos conformes tienen origen y destino activos.** -/
theorem arc_active_of_conformal {x : Sym2 V → ℤ} (hx : IsLocalProfile G lab F x)
    (α : Arc (rowSys G lab F))
    (hP : ∀ e, projP _ α e = 0 ∨ 0 < projP _ α e * x e.1)
    (hV : ∀ j, projV _ α j = 0 ∨ 0 < projV _ α j * zLift G lab F x j) :
    IsActiveRow G lab F (src _ α).1 ∧ IsActiveRow G lab F (tgt _ α).1 := by
  rcases α with ⟨p, d, s⟩ | ⟨k, s⟩
  · have hxp : x p.1 ≠ 0 := by
      rcases hP p with h | h
      · exfalso
        simp only [projP, if_true] at h
        exact mul_ne_zero (sgn_ne_zero _) (sgn_ne_zero _) h
      · intro h0; rw [h0, mul_zero] at h; exact lt_irrefl 0 h
    cases d
    · exact ⟨row2_active hx p hxp, row1_active hx p hxp⟩
    · exact ⟨row1_active hx p hxp, row2_active hx p hxp⟩
  · have hz : zLift G lab F x k.1 ≠ 0 := by
      rcases hV k.1 with h | h
      · exfalso
        simp only [projV, if_true] at h
        exact sgn_ne_zero s (neg_eq_zero.mp h)
      · intro h0; rw [h0, mul_zero] at h; exact lt_irrefl 0 h
    exact ⟨zLift_active hx _ hz, zLift_active hx _ hz⟩

/-- **S26 §§2 y 4 sobre el portador activo, con orden cíclico.** La descomposición de
`local_profile_cover_cycles`, con el lift virtual explícito `z = zLift x`, y además: `z` es nulo
fuera de las filas activas, todo estado de todo ciclo está sobre una fila activa (componente
real no aislada), y cada ciclo viene con una lista cíclica sin repeticiones de sus arcos
(`tgt l[i] = src l[(i+1) mod |l|]`, orígenes distintos). No se supone ningún proveedor de
orden cíclico. -/
theorem local_profile_active_ordered_cycles (x : Sym2 V → ℤ) (hx : IsLocalProfile G lab F x) :
    (∀ j, IsBip G lab F j → zLift G lab F x j = 0) ∧
      (∀ j, ¬ IsActiveRow G lab F j → zLift G lab F x j = 0) ∧
      (∀ j, baug (rowSys G lab F) (fun e => x e.1) (zLift G lab F x) j = 0) ∧
      ∑ j, |zLift G lab F x j| ≤ ∑ e : Col G, |x e.1| ∧
      ∃ L : List (Finset (Arc (rowSys G lab F))),
        (∀ C ∈ L, IsSimpleCycle (src _) (tgt _) C) ∧
        (∀ C ∈ L, ∀ j, baug (rowSys G lab F) (flowP _ (Circulation.ind C))
          (flowV _ (Circulation.ind C)) j = 0) ∧
        (∀ e : Col G, (L.map (fun C => flowP _ (Circulation.ind C) e)).sum = x e.1) ∧
        (∀ j, (L.map (fun C => flowV _ (Circulation.ind C) j)).sum = zLift G lab F x j) ∧
        (((L.map Finset.card).sum : ℕ) : ℤ) = ∑ e : Col G, |x e.1| + ∑ j, |zLift G lab F x j| ∧
        (∀ v, ((∑ j ∈ univ.filter (fun j : Row V => j.1 = v),
            (L.countP (fun C => (j, true) ∈ C.image (src (rowSys G lab F))) +
              L.countP (fun C => (j, false) ∈ C.image (src (rowSys G lab F)))) : ℕ) : ℤ) ≤
          ∑ e : Col G, if v ∈ e.1 then |x e.1| else 0) ∧
        (∀ C ∈ L, ∀ α ∈ C, (∀ e, projP _ α e = 0 ∨ 0 < projP _ α e * x e.1) ∧
          (∀ j, projV _ α j = 0 ∨ 0 < projV _ α j * zLift G lab F x j)) ∧
        (∀ C ∈ L, ∀ α ∈ C,
          IsActiveRow G lab F (src _ α).1 ∧ IsActiveRow G lab F (tgt _ α).1) ∧
        ∀ C ∈ L, ∃ l : List (Arc (rowSys G lab F)), l.Nodup ∧ l.toFinset = C ∧
          l.length = C.card ∧ (l.map (src _)).Nodup ∧
          ∀ (i : ℕ) (hi : i < l.length),
            tgt _ l[i] = src _ (l[(i + 1) % l.length]'(Nat.mod_lt _ (by omega))) := by
  have hz : ∀ j, (rowSys G lab F).nb j = false → zLift G lab F x j = 0 := fun j h => by
    unfold zLift; rw [if_pos ((rowSys_nb G lab F j).mp h)]
  obtain ⟨L, h1, h2, h3, h4, h5, h6, h7, h8⟩ :=
    exists_cover_cycle_decomp_roots (rowSys G lab F) (fun e => x e.1) (zLift G lab F x)
      Prod.fst hz (baug_zLift G lab F x hx)
  refine ⟨fun j hj => by unfold zLift; rw [if_pos hj],
    fun j hj => by_contra fun h => hj (zLift_active hx j h),
    baug_zLift G lab F x hx, h6, L, h1, h2, h3, h4, h5, fun v => ?_, h8,
    fun C hC α hα => arc_active_of_conformal hx α (h8 C hC α hα).1 (h8 C hC α hα).2,
    fun C hC => ?_⟩
  · have h := (h7 v).trans_eq (Finset.sum_congr rfl fun e _ => root_count_eq G lab F e v _)
    convert h
  · obtain ⟨a, ha⟩ := (h1 C hC).nonempty
    obtain ⟨l, hl1, hl2, hl3, -, hl5, hl6⟩ := (h1 C hC).exists_cyclicList a ha
    exact ⟨l, hl1, by convert hl2, hl3, hl5, hl6⟩

end TypedTriangle.ActiveCover
