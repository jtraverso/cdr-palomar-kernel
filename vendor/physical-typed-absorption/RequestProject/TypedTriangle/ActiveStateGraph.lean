/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import RequestProject.TypedTriangle.ActiveCover

@[expose] public section

/-!
# Grafo simple de estados activos (V12, Prioridad 2)

A partir de los arcos `src/tgt` EXISTENTES de la cubierta aumentada del sistema de filas de
componentes se construye un grafo simple no dirigido sobre los estados activos `AState`:

* `revArc` — arco inverso (para todo sistema de filas): intercambia `src/tgt` y cambia el
  signo de las proyecciones;
* `src_ne_tgt` — en el sistema de componentes no hay lazos (los arcos físicos cambian de
  raíz, los verticales de signo);
* `arc_unique` — entre dos estados hay a lo sumo un arco en cada sentido;
* `stateGraph` — `a ~ b` si existe un arco `a → b` (equivalentemente `b → a`);
* `edgeProjP`/`edgeProjV` — proyección firmada de una arista orientada del grafo; coincide
  con la del (único) arco (`edgeProjP_arc`), y es antisimétrica;
* `cycle_walk_adj`, `cycle_walk_proj` — todo ciclo simple ordenado sobre estados activos es
  un camino cerrado del grafo cuya proyección firmada es exactamente la del ciclo.

Cotas (con hipótesis geométricas auxiliares, no premisas de T):

* `card_AState_le` — si cada raíz física tiene `≤ C` filas activas, hay `≤ 2 C n` estados;
* `card_le_degree` — un estado sobre la componente activa `K` tiene grado `≥ |K|`;
  `card_le_mul_degree` — si `n ≤ C·|K|` para toda componente activa, `n ≤ C · grado`.
-/

open Finset Classical

noncomputable section

namespace TypedTriangle.SignedCover

variable {R P : Type*} (S : RowSystem R P)

/-- Arco inverso. -/
def revArc : Arc S → Arc S
  | Sum.inl (p, d, s) => Sum.inl (p, !d, tsign S p s)
  | Sum.inr (j, s) => Sum.inr (j, !s)

lemma tsign_tsign (p : P) (s : Bool) : tsign S p (tsign S p s) = s := by
  unfold tsign; cases s <;> cases (S.a1 p == S.a2 p) <;> rfl

lemma src_revArc (α : Arc S) : src S (revArc S α) = tgt S α := by
  rcases α with ⟨p, d, s⟩ | ⟨j, s⟩
  · cases d <;> simp [revArc, src, tgt]
  · simp [revArc, src, tgt]

lemma tgt_revArc (α : Arc S) : tgt S (revArc S α) = src S α := by
  rcases α with ⟨p, d, s⟩ | ⟨j, s⟩
  · cases d <;> simp [revArc, src, tgt, tsign_tsign]
  · simp [revArc, src, tgt]

lemma projP_revArc (α : Arc S) (q : P) : projP S (revArc S α) q = - projP S α q := by
  rcases α with ⟨p, d, s⟩ | ⟨j, s⟩
  · simp only [revArc, projP]
    by_cases h : p = q
    · subst h
      cases d <;> cases s <;> cases h1 : S.a1 p <;> cases h2 : S.a2 p <;>
        simp [tsign, sgn, h1, h2]
    · simp [h]
  · simp only [revArc, projP, neg_zero]

lemma projV_revArc (α : Arc S) (j : R) : projV S (revArc S α) j = - projV S α j := by
  rcases α with ⟨p, d, s⟩ | ⟨k, s⟩
  · simp [revArc, projV]
  · simp only [revArc, projV]
    split_ifs <;> cases s <;> simp [sgn]

end TypedTriangle.SignedCover

namespace TypedTriangle.ActiveCover

open TypedTriangle.ComponentRows TypedTriangle.SignedCover TypedTriangle.Circulation

variable {V I : Type*} [Fintype V] (G : SimpleGraph V) (lab : V → I) (F : Set (Multiset I))

omit [Fintype V] in
lemma ends_cases (e : Col G) {v u : V} (h : e.1 = s(v, u)) :
    ((ends G e).1 = v ∧ (ends G e).2 = u) ∨ ((ends G e).1 = u ∧ (ends G e).2 = v) := by
  rw [← ends_spec G e, Sym2.eq_iff] at h
  exact h

/-- En el sistema de componentes ningún arco es un lazo. -/
lemma src_ne_tgt (α : Arc (rowSys G lab F)) : src _ α ≠ tgt _ α := by
  rcases α with ⟨p, d, s⟩ | ⟨j, s⟩
  · have hne := ends_ne G p
    cases d
    · simp only [src, tgt, Bool.false_eq_true, if_false]
      intro h
      exact hne (congrArg (fun st => st.1.1) h).symm
    · simp only [src, tgt, if_true]
      intro h
      exact hne (congrArg (fun st => st.1.1) h)
  · simp [src, tgt]

/-- **Unicidad del arco** entre dos estados. -/
lemma arc_unique {α β : Arc (rowSys G lab F)} (hs : src _ α = src _ β) (ht : tgt _ α = tgt _ β) :
    α = β := by
  rcases α with ⟨p, d, s⟩ | ⟨j, s⟩ <;> rcases β with ⟨p', d', s'⟩ | ⟨j', s'⟩
  · have hp := ends_ne G p
    have hp' := ends_ne G p'
    have hs1 := congrArg (fun st => st.1.1) hs
    have hs2 := congrArg (fun st => st.2) hs
    have ht1 := congrArg (fun st => st.1.1) ht
    cases d <;> cases d' <;>
      simp only [src, tgt, Bool.false_eq_true, if_false, if_true, rowSys, row1, row2]
        at hs1 hs2 ht1
    · have : p = p' := Subtype.ext (by rw [← ends_spec G p, ← ends_spec G p', hs1, ht1])
      subst this; subst hs2; rfl
    · exfalso
      have : p = p' := Subtype.ext (by
        rw [← ends_spec G p, ← ends_spec G p', ht1, hs1, Sym2.eq_swap])
      subst this
      exact hp hs1.symm
    · exfalso
      have : p = p' := Subtype.ext (by
        rw [← ends_spec G p, ← ends_spec G p', hs1, ht1, Sym2.eq_swap])
      subst this
      exact hp hs1
    · have : p = p' := Subtype.ext (by rw [← ends_spec G p, ← ends_spec G p', hs1, ht1])
      subst this; subst hs2; rfl
  · exfalso
    have hs1 := congrArg (fun st => st.1.1) hs
    have ht1 := congrArg (fun st => st.1.1) ht
    have hp := ends_ne G p
    cases d <;> simp only [src, tgt, Bool.false_eq_true, if_false, if_true, rowSys, row1, row2]
      at hs1 ht1
    all_goals first | exact hp (hs1.symm.trans ht1) | exact hp (ht1.symm.trans hs1) |
      exact hp (hs1.trans ht1.symm) | exact hp (ht1.trans hs1.symm)
  · exfalso
    have hs1 := congrArg (fun st => st.1.1) hs
    have ht1 := congrArg (fun st => st.1.1) ht
    have hp := ends_ne G p'
    cases d' <;> simp only [src, tgt, Bool.false_eq_true, if_false, if_true, rowSys, row1, row2]
      at hs1 ht1
    all_goals first | exact hp (hs1.symm.trans ht1) | exact hp (ht1.symm.trans hs1)
  · simp only [src, Prod.mk.injEq] at hs
    have : j = j' := Subtype.ext hs.1
    subst this; rw [hs.2]

/-- **Grafo simple de estados activos**: `a ~ b` si hay un arco de la cubierta `a → b`. -/
def stateGraph : SimpleGraph (AState G lab F) where
  Adj a b := ∃ α : Arc (rowSys G lab F), src _ α = a.1 ∧ tgt _ α = b.1
  symm := ⟨fun a b ⟨α, h1, h2⟩ =>
    ⟨revArc _ α, by rw [src_revArc, h2], by rw [tgt_revArc, h1]⟩⟩
  loopless := ⟨fun a ⟨α, h1, h2⟩ => src_ne_tgt G lab F α (h1.trans h2.symm)⟩

/-- Proyección física firmada de una arista orientada `a → b` del grafo de estados. -/
def edgeProjP (a b : Row V × Bool) (q : Col G) : ℤ :=
  if h : ∃ α : Arc (rowSys G lab F), src _ α = a ∧ tgt _ α = b then projP _ (Classical.choose h) q
  else 0

/-- Proyección virtual firmada de una arista orientada `a → b` del grafo de estados. -/
def edgeProjV (a b : Row V × Bool) (j : Row V) : ℤ :=
  if h : ∃ α : Arc (rowSys G lab F), src _ α = a ∧ tgt _ α = b then projV _ (Classical.choose h) j
  else 0

lemma choose_arc_eq (α : Arc (rowSys G lab F))
    (h : ∃ β : Arc (rowSys G lab F), src _ β = src _ α ∧ tgt _ β = tgt _ α) :
    Classical.choose h = α :=
  arc_unique G lab F (Classical.choose_spec h).1 (Classical.choose_spec h).2

/-- La proyección de una arista del grafo es la del arco. -/
lemma edgeProjP_arc (α : Arc (rowSys G lab F)) (q : Col G) :
    edgeProjP G lab F (src _ α) (tgt _ α) q = projP _ α q := by
  unfold edgeProjP
  rw [dif_pos ⟨α, rfl, rfl⟩, choose_arc_eq]

lemma edgeProjV_arc (α : Arc (rowSys G lab F)) (j : Row V) :
    edgeProjV G lab F (src _ α) (tgt _ α) j = projV _ α j := by
  unfold edgeProjV
  rw [dif_pos ⟨α, rfl, rfl⟩, choose_arc_eq]

/-- Antisimetría de la proyección de las aristas del grafo. -/
lemma edgeProjP_swap (a b : Row V × Bool) (q : Col G) :
    edgeProjP G lab F b a q = - edgeProjP G lab F a b q := by
  by_cases h : ∃ α : Arc (rowSys G lab F), src _ α = a ∧ tgt _ α = b
  · obtain ⟨α, rfl, rfl⟩ := h
    have h1 := edgeProjP_arc G lab F (revArc _ α) q
    rw [src_revArc, tgt_revArc, projP_revArc] at h1
    rw [h1, edgeProjP_arc]
  · have h' : ¬ ∃ α : Arc (rowSys G lab F), src _ α = b ∧ tgt _ α = a := by
      rintro ⟨α, h1, h2⟩
      exact h ⟨revArc _ α, by rw [src_revArc, h2], by rw [tgt_revArc, h1]⟩
    simp [edgeProjP, h, h']

lemma edgeProjV_swap (a b : Row V × Bool) (j : Row V) :
    edgeProjV G lab F b a j = - edgeProjV G lab F a b j := by
  by_cases h : ∃ α : Arc (rowSys G lab F), src _ α = a ∧ tgt _ α = b
  · obtain ⟨α, rfl, rfl⟩ := h
    have h1 := edgeProjV_arc G lab F (revArc _ α) j
    rw [src_revArc, tgt_revArc, projV_revArc] at h1
    rw [h1, edgeProjV_arc]
  · have h' : ¬ ∃ α : Arc (rowSys G lab F), src _ α = b ∧ tgt _ α = a := by
      rintro ⟨α, h1, h2⟩
      exact h ⟨revArc _ α, by rw [src_revArc, h2], by rw [tgt_revArc, h1]⟩
    simp [edgeProjV, h, h']

/-! ### Ciclos ordenados como caminos cerrados del grafo -/

section Walk

variable {C : Finset (Arc (rowSys G lab F))} {l : List (Arc (rowSys G lab F))}

/-- Pasos consecutivos de un ciclo ordenado sobre estados activos son aristas del grafo. -/
theorem cycle_walk_adj
    (hact : ∀ α ∈ l, IsActiveRow G lab F (src _ α).1 ∧ IsActiveRow G lab F (tgt _ α).1)
    (hcyc : ∀ (i : ℕ) (hi : i < l.length),
      tgt _ l[i] = src _ (l[(i + 1) % l.length]'(Nat.mod_lt _ (by omega))))
    (i : ℕ) (hi : i < l.length) :
    (stateGraph G lab F).Adj ⟨src _ l[i], (hact _ (List.getElem_mem hi)).1⟩
      ⟨src _ (l[(i + 1) % l.length]'(Nat.mod_lt _ (by omega))),
        (hact _ (List.getElem_mem (Nat.mod_lt _ (by omega)))).1⟩ :=
  ⟨l[i], rfl, hcyc i hi⟩

/-- **Misma proyección firmada**: la proyección física de un ciclo simple con orden cíclico
`l` es la suma de las proyecciones de las aristas del camino cerrado de estados. -/
theorem cycle_walk_proj (hl : l.Nodup) (hlC : ∀ α, α ∈ l ↔ α ∈ C)
    (hcyc : ∀ (i : ℕ) (hi : i < l.length),
      tgt _ l[i] = src _ (l[(i + 1) % l.length]'(Nat.mod_lt _ (by omega)))) (q : Col G) :
    flowP _ (Circulation.ind C) q =
      ∑ i : Fin l.length, edgeProjP G lab F (src _ l[i.1])
        (src _ (l[(i.1 + 1) % l.length]'(Nat.mod_lt _ i.pos))) q := by
  have : ∀ i : Fin l.length, edgeProjP G lab F (src _ l[i.1])
      (src _ (l[(i.1 + 1) % l.length]'(Nat.mod_lt _ i.pos))) q = projP _ l[i.1] q := by
    intro i
    rw [← hcyc i.1 i.2, edgeProjP_arc]
  rw [Finset.sum_congr rfl fun i _ => this i, Fin.sum_univ_fun_getElem l (fun α => projP _ α q),
    ← List.sum_toFinset _ hl]
  unfold flowP Circulation.ind
  simp only [Nat.cast_ite, Nat.cast_one, Nat.cast_zero, ite_mul, one_mul, zero_mul]
  rw [show l.toFinset = C from by ext; simp [hlC]]
  simp

theorem cycle_walk_projV (hl : l.Nodup) (hlC : ∀ α, α ∈ l ↔ α ∈ C)
    (hcyc : ∀ (i : ℕ) (hi : i < l.length),
      tgt _ l[i] = src _ (l[(i + 1) % l.length]'(Nat.mod_lt _ (by omega)))) (j : Row V) :
    flowV _ (Circulation.ind C) j =
      ∑ i : Fin l.length, edgeProjV G lab F (src _ l[i.1])
        (src _ (l[(i.1 + 1) % l.length]'(Nat.mod_lt _ i.pos))) j := by
  have : ∀ i : Fin l.length, edgeProjV G lab F (src _ l[i.1])
      (src _ (l[(i.1 + 1) % l.length]'(Nat.mod_lt _ i.pos))) j = projV _ l[i.1] j := by
    intro i
    rw [← hcyc i.1 i.2, edgeProjV_arc]
  rw [Finset.sum_congr rfl fun i _ => this i, Fin.sum_univ_fun_getElem l (fun α => projV _ α j),
    ← List.sum_toFinset _ hl]
  unfold flowV Circulation.ind
  simp only [Nat.cast_ite, Nat.cast_one, Nat.cast_zero, ite_mul, one_mul, zero_mul]
  rw [show l.toFinset = C from by ext; simp [hlC]]
  simp

end Walk

/-! ### Cotas de estados y de grado -/

/-- **Número de estados activos**: si cada raíz física tiene a lo sumo `C` filas activas,
hay a lo sumo `2 C n` estados activos. -/
theorem card_AState_le (C : ℕ)
    (hC : ∀ v, (univ.filter (fun j : Row V => j.1 = v ∧ IsActiveRow G lab F j)).card ≤ C) :
    Fintype.card (AState G lab F) ≤ 2 * C * Fintype.card V := by
  rw [Fintype.card_subtype]
  have h1 : (univ.filter (fun st : Row V × Bool => IsActiveRow G lab F st.1)) =
      (univ.filter (fun j : Row V => IsActiveRow G lab F j)) ×ˢ (univ : Finset Bool) := by
    ext st; simp
  have h2 : (univ.filter (fun j : Row V => IsActiveRow G lab F j)) =
      (univ : Finset V).biUnion
        (fun v => univ.filter (fun j : Row V => j.1 = v ∧ IsActiveRow G lab F j)) := by
    ext j; simp
  rw [h1, Finset.card_product, Finset.card_univ, Fintype.card_bool, h2]
  calc _ ≤ (∑ v : V, (univ.filter (fun j : Row V => j.1 = v ∧ IsActiveRow G lab F j)).card) * 2 :=
        Nat.mul_le_mul_right _ Finset.card_biUnion_le
    _ ≤ (∑ _v : V, C) * 2 := Nat.mul_le_mul_right _ (Finset.sum_le_sum fun v _ => hC v)
    _ = 2 * C * Fintype.card V := by rw [Finset.sum_const, Finset.card_univ]; ring

variable {G lab F}

omit [Fintype V] in
lemma allowed_ne {v u w : V} (hT : SparseEdge.IsAllowed G lab F {v, u, w}) :
    v ≠ u ∧ v ≠ w ∧ u ≠ w := by
  have h3 := hT.1
  refine ⟨?_, ?_, ?_⟩ <;> rintro rfl
  · have : ({v, v, w} : Finset V).card ≤ 2 := by
      rw [Finset.insert_eq_of_mem (by simp)]; exact Finset.card_le_two
    omega
  · have : ({v, u, v} : Finset V).card ≤ 2 := by
      rw [Finset.insert_eq_of_mem (by simp)]; exact Finset.card_le_two
    omega
  · have : ({v, u, u} : Finset V).card ≤ 2 := by
      rw [Finset.pair_eq_singleton]; exact Finset.card_le_two
    omega

/-- Todo vértice de una componente no aislada del enlace es no aislado. -/
lemma linkActive_of_mem_comp {v u₀ u : V} (h₀ : LinkActive G lab F v u₀)
    (hu : u ∈ comp G lab F v u₀) : LinkActive G lab F v u := by
  simp only [comp, Finset.mem_filter, Finset.mem_univ, true_and] at hu
  by_cases he : u₀ = u
  · exact he ▸ h₀
  · obtain ⟨p⟩ := hu.symm
    cases p with
    | nil => exact absurd rfl he
    | cons h _ => exact ⟨_, h⟩

lemma comp_eq_of_mem {v u₀ u : V} (hu : u ∈ comp G lab F v u₀) :
    comp G lab F v u = comp G lab F v u₀ := by
  simp only [comp, Finset.mem_filter, Finset.mem_univ, true_and] at hu
  ext w
  simp only [comp, Finset.mem_filter, Finset.mem_univ, true_and]
  exact ⟨fun h => hu.trans h, fun h => hu.symm.trans h⟩

/-- Desde un estado sobre una componente activa `(v, K)`, cada `u ∈ K` da un vecino del grafo
de estados cuya raíz es `u`. -/
lemma exists_neighbor_over (a : AState G lab F) {u : V} (hu : u ∈ a.1.1.2) :
    ∃ b : AState G lab F, (stateGraph G lab F).Adj a b ∧ b.1.1.1 = u := by
  obtain ⟨⟨⟨v, K⟩, s⟩, u₀, h₀, hK⟩ := a
  simp only at hu hK h₀ ⊢
  subst hK
  have hua : LinkActive G lab F v u := linkActive_of_mem_comp h₀ hu
  have hcomp : comp G lab F v u = comp G lab F v u₀ := comp_eq_of_mem hu
  obtain ⟨w, -, hT⟩ := hua
  obtain ⟨hvu, hvw, huw⟩ := allowed_ne hT
  have hadj : G.Adj v u := hT.2.1 v (by simp) u (by simp) hvu
  have hT' : SparseEdge.IsAllowed G lab F {u, v, w} := by rw [Finset.insert_comm]; exact hT
  have huv : LinkActive G lab F u v := ⟨w, hvw, hT'⟩
  let e : Col G := ⟨s(v, u), hadj⟩
  rcases ends_cases G e (v := v) (u := u) rfl with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · refine ⟨⟨(row2 G lab F e, tsign _ e s), ?_⟩, ⟨Sum.inl (e, true, s), ?_, rfl⟩, ?_⟩
    · exact ⟨(ends G e).1, by show LinkActive G lab F (ends G e).2 (ends G e).1; rw [h1, h2]; exact huv, rfl⟩
    · simp only [src, if_true, rowSys, row1, h1, h2, hcomp]
    · simp [row2, h2]
  · refine ⟨⟨(row1 G lab F e, tsign _ e s), ?_⟩, ⟨Sum.inl (e, false, s), ?_, rfl⟩, ?_⟩
    · exact ⟨(ends G e).2, by show LinkActive G lab F (ends G e).1 (ends G e).2; rw [h1, h2]; exact huv, rfl⟩
    · simp only [src, Bool.false_eq_true, if_false, rowSys, row2, h1, h2, hcomp]
    · simp [row1, h1]

/-- **Grado**: un estado sobre la componente activa `(v, K)` tiene al menos `|K|` vecinos
(uno por cada `u ∈ K`, con raíces distintas). -/
theorem card_le_degree (a : AState G lab F) :
    a.1.1.2.card ≤ (stateGraph G lab F).degree a := by
  rw [← SimpleGraph.card_neighborFinset_eq_degree]
  have hsub : a.1.1.2 ⊆ ((stateGraph G lab F).neighborFinset a).image (fun b => b.1.1.1) := by
    intro u hu
    obtain ⟨b, hb, rfl⟩ := exists_neighbor_over a hu
    exact Finset.mem_image_of_mem _ ((SimpleGraph.mem_neighborFinset _ _ _).mpr hb)
  exact (Finset.card_le_card hsub).trans Finset.card_image_le

/-- **Grado mínimo** (hipótesis geométrica auxiliar del núcleo preparado): si toda componente
activa tiene tamaño `≥ n/C`, todo estado activo tiene grado `≥ n/C`. -/
theorem card_le_mul_degree (C : ℕ)
    (hdeg : ∀ j : Row V, IsActiveRow G lab F j → Fintype.card V ≤ C * j.2.card)
    (a : AState G lab F) : Fintype.card V ≤ C * (stateGraph G lab F).degree a :=
  (hdeg _ a.2).trans (Nat.mul_le_mul_left _ (card_le_degree a))

end TypedTriangle.ActiveCover
