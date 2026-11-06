/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import RequestProject.TypedTriangle.CutExpansion

@[expose] public section

/-!
# G1-Z, §3 de la guía V6 — Componentes activas, doble cubierta y conexión robusta

* `dcover J`: doble cubierta bipartita sobre `Ω × Bool` (`(x,σ) ~ (y,τ)` si `x ~ y`, `σ ≠ τ`).
  Levantamiento de recorridos (`dcover_reach_lift`), paridad de los recorridos de la cubierta
  (`dcover_walk_parity`) y proyección (`dcoverHom`). Si `x` tiene un recorrido cerrado impar y
  `x, y` están conectados, todas las copias de `x` e `y` están conectadas en la cubierta.
* `compOf J a`: componente de `a`, cerrada para la adyacencia.
* Para el enlace `L_v`, con H3 y H4:
  - `link_minDeg`: grado `≥ αn` en los vértices activos;
  - `link_robustConn`: conexión robusta de una componente (vía `link_reach_robust`);
  - `cover_robustConn`: conexión robusta de la doble cubierta de una componente no bipartita
    (con ambiente `2n`); se proyectan los borrados a la base, se usa la conservación de
    conexión y de recorridos impares, y se levanta el camino. Un vértice cuya otra copia fue
    borrada se conecta primero a un vecino libre (grado mínimo).
-/

open Finset

noncomputable section
open Classical

namespace TypedTriangle

open Incidence

variable {Ω : Type*}

/-! ## Doble cubierta -/

/-- Doble cubierta bipartita. -/
def dcover (J : SimpleGraph Ω) : SimpleGraph (Ω × Bool) where
  Adj p q := J.Adj p.1 q.1 ∧ p.2 ≠ q.2
  symm := ⟨fun _ _ h => ⟨h.1.symm, h.2.symm⟩⟩
  loopless := ⟨fun _ h => h.2 rfl⟩

/-- Proyección de la cubierta a la base. -/
def dcoverHom (J : SimpleGraph Ω) : dcover J →g J := ⟨Prod.fst, fun h => h.1⟩

lemma dcover_mono {J J' : SimpleGraph Ω} (h : J ≤ J') : dcover J ≤ dcover J' :=
  fun _ _ hpq => ⟨h hpq.1, hpq.2⟩

/-- Levantamiento de recorridos. -/
lemma dcover_reach_lift {J : SimpleGraph Ω} {x y : Ω} (p : J.Walk x y) (σ : Bool) :
    (dcover J).Reachable (x, σ) (y, xor σ (Nat.bodd p.length)) := by
  induction p generalizing σ with
  | nil => simp
  | @cons a b c h p ih =>
    have h1 : (dcover J).Adj (a, σ) (b, !σ) := ⟨h, by cases σ <;> simp⟩
    have := h1.reachable.trans (ih (!σ))
    simp only [SimpleGraph.Walk.length_cons, Nat.bodd_succ]
    convert this using 2
    cases σ <;> cases Nat.bodd p.length <;> rfl

/-- Paridad de los recorridos de la cubierta. -/
lemma dcover_walk_parity {J : SimpleGraph Ω} {x y : Ω × Bool} (p : (dcover J).Walk x y) :
    y.2 = xor x.2 (Nat.bodd p.length) := by
  induction p with
  | nil => simp
  | @cons a b c h p ih =>
    simp only [SimpleGraph.Walk.length_cons, Nat.bodd_succ, ih]
    have : b.2 = !a.2 := by
      have := h.2
      cases ha : a.2 <;> cases hb : b.2 <;> simp_all
    rw [this]
    cases a.2 <;> cases Nat.bodd p.length <;> rfl

/-- Con un recorrido cerrado impar en `x`, todas las copias de dos vértices conectados están
conectadas en la cubierta. -/
lemma dcover_reach_all {J : SimpleGraph Ω} {x y : Ω} (hodd : OddAt J x) (hxy : J.Reachable x y)
    (σ τ : Bool) : (dcover J).Reachable (x, σ) (y, τ) := by
  obtain ⟨c, hc⟩ := hodd
  obtain ⟨p⟩ := hxy
  have hflip : (dcover J).Reachable (x, σ) (x, !σ) := by
    have := dcover_reach_lift c σ
    rw [Nat.bodd_eq_one_and_ne_zero] at this
    simpa [Nat.odd_iff.1 hc] using this
  by_cases hτ : τ = xor σ (Nat.bodd p.length)
  · rw [hτ]; exact dcover_reach_lift p σ
  · have := dcover_reach_lift p (!σ)
    have e : xor (!σ) (Nat.bodd p.length) = τ := by
      cases σ <;> cases τ <;> cases hb : Nat.bodd p.length <;> simp_all
    rw [e] at this
    exact hflip.trans this

/-- Proyección de un recorrido del inducido de la cubierta. -/
lemma dcover_induced_proj {J : SimpleGraph Ω} (A : Finset (Ω × Bool)) {x y : Ω × Bool}
    (p : (inducedOn (dcover J) A).Walk x y) :
    ∃ q : (inducedOn J (A.image Prod.fst)).Walk x.1 y.1, q.length = p.length := by
  let φ : inducedOn (dcover J) A →g inducedOn J (A.image Prod.fst) :=
    ⟨Prod.fst, fun h => ⟨h.1.1, Finset.mem_image_of_mem _ h.2.1,
      Finset.mem_image_of_mem _ h.2.2⟩⟩
  exact ⟨p.map φ, SimpleGraph.Walk.length_map _ _⟩

/-! ## Componentes -/

variable [Fintype Ω]

/-- Componente de `a`. -/
def compOf (J : SimpleGraph Ω) (a : Ω) : Finset Ω := univ.filter (J.Reachable a)

lemma mem_compOf {J : SimpleGraph Ω} {a x : Ω} : x ∈ compOf J a ↔ J.Reachable a x := by
  simp [compOf]

lemma compOf_closed (J : SimpleGraph Ω) (a : Ω) : NbrClosed J (compOf J a) := by
  intro x hx y hxy
  exact mem_compOf.2 ((mem_compOf.1 hx).trans hxy.reachable)

lemma compOf_reach {J : SimpleGraph Ω} {a x y : Ω} (hx : x ∈ compOf J a) (hy : y ∈ compOf J a) :
    J.Reachable x y :=
  (mem_compOf.1 hx).symm.trans (mem_compOf.1 hy)

lemma compOf_eq_of_mem {J : SimpleGraph Ω} {a b : Ω} (hb : b ∈ compOf J a) :
    compOf J b = compOf J a := by
  ext x
  simp only [mem_compOf]
  exact ⟨fun h => (mem_compOf.1 hb).trans h, fun h => (mem_compOf.1 hb).symm.trans h⟩

/-- Vértice con algún vecino. -/
def Active (J : SimpleGraph Ω) (a : Ω) : Prop := ∃ w, J.Adj a w

lemma active_of_mem_compOf {J : SimpleGraph Ω} {a x : Ω} (ha : Active J a)
    (hx : x ∈ compOf J a) : Active J x := by
  obtain ⟨p⟩ := (mem_compOf.1 hx).symm
  cases p with
  | nil => exact ha
  | cons h q => exact ⟨_, h⟩

omit [Fintype Ω] in
lemma delG_empty (J : SimpleGraph Ω) : delG J ∅ ∅ = J := by
  ext x y; simp [delG]

omit [Fintype Ω] in
lemma oddAt_mono {J J' : SimpleGraph Ω} (h : J ≤ J') {a : Ω} (ha : OddAt J a) : OddAt J' a := by
  obtain ⟨p, hp⟩ := ha
  exact ⟨p.map (SimpleGraph.Hom.ofLE h), by simpa using hp⟩

/-! ## El enlace -/

variable {V I : Type*} [Fintype V]

/-- **Grado mínimo del enlace (de H3).** -/
theorem link_minDeg {H : Host V I} {F : Set (Multiset I)} {α : ℝ} (hH3 : CommonNbrCond H F α)
    {v a w : V} (h : (linkGraph H F v).Adj a w) :
    α * Fintype.card V ≤ ((univ.filter ((linkGraph H F v).Adj a)).card : ℝ) := by
  have e := linkOn_goodEdges_eq H F v ∅ ∅
  rw [delG_empty] at e
  have hdeg0 : ∀ x, degIn (∅ : Finset (Sym2 V)) x ≤ 0 := fun x => by simp [degIn]
  have := linkOn_good_degree hH3 (z := v) ∅ ∅ hdeg0 (a := a) (w := w) (by rw [e]; exact h)
  rw [e] at this
  simpa using this

lemma link_minDegOn {H : Host V I} {F : Set (Multiset I)} {α : ℝ} (hH3 : CommonNbrCond H F α)
    {v a : V} (ha : Active (linkGraph H F v) a) :
    MinDegOn (linkGraph H F v) (compOf (linkGraph H F v) a) α := by
  intro x hx
  obtain ⟨w, hw⟩ := active_of_mem_compOf ha hx
  exact link_minDeg hH3 hw

omit [Fintype V] in
/-- Borrar la raíz no cambia el enlace. -/
lemma delG_erase_root_le (H : Host V I) (F : Set (Multiset I)) (v : V) (Z : Finset V)
    (B : Finset (Sym2 V)) : delG (linkGraph H F v) (Z.erase v) B ≤ delG (linkGraph H F v) Z B := by
  intro x y ⟨hxy, hx, hy, hB⟩
  have hne := linkGraph_adj_ne hxy
  refine ⟨hxy, fun h => hx (Finset.mem_erase.2 ⟨Ne.symm hne.1, h⟩),
    fun h => hy (Finset.mem_erase.2 ⟨Ne.symm hne.2.1, h⟩), hB⟩

/-- Conexión y recorridos impares del enlace tras borrar `Z` (`|Z| ≤ ζn`) y `B`
(grado `≤ ρn`), con las ventanas de `link_image_robust`. -/
theorem link_delG_robust {H : Host V I} {F : Set (Multiset I)} {α : ℝ} {h : ℕ}
    (hα : 0 < α) (hH3 : CommonNbrCond H F α) (hH4 : HingeCond H F α h) (v : V)
    {ζ ρ : ℝ} (hρ : 0 ≤ ρ)
    (hw1 : ζ * Fintype.card V + 2 + 4 * (ρ * Fintype.card V) < α * Fintype.card V)
    (hw2 : (ζ * Fintype.card V + h + 5 * (ρ * Fintype.card V)) * 2 ^ Nat.choose h 2 ≤
      α / 2 * Fintype.card V)
    (Z : Finset V) (B : Finset (Sym2 V)) (hZ : (Z.card : ℝ) ≤ ζ * Fintype.card V)
    (hB : ∀ x, (degIn B x : ℝ) ≤ ρ * Fintype.card V) :
    (∀ a b, a ∉ Z → b ∉ Z → (linkGraph H F v).Reachable a b →
      (delG (linkGraph H F v) Z B).Reachable a b) ∧
    (∀ a, a ∉ Z → OddAt (linkGraph H F v) a → OddAt (delG (linkGraph H F v) Z B) a) := by
  set d := ⌊ρ * Fintype.card V⌋₊
  have hd : (d : ℝ) ≤ ρ * Fintype.card V := Nat.floor_le (by positivity)
  have hdeg : ∀ x, degIn B x ≤ d := fun x => Nat.le_floor (hB x)
  have hZ' : ((Z.erase v).card : ℝ) ≤ Z.card := by exact_mod_cast Finset.card_erase_le
  have hv : v ∉ Z.erase v := Finset.notMem_erase v Z
  have w1 : ((Z.erase v).card : ℝ) + 2 + 4 * d < α * Fintype.card V := by linarith
  have w2 : (((Z.erase v).card : ℝ) + h + 5 * d) * 2 ^ Nat.choose h 2 ≤
      α / 2 * Fintype.card V := by
    refine le_trans ?_ hw2
    exact mul_le_mul_of_nonneg_right (by linarith) (by positivity)
  have hle := delG_erase_root_le H F v Z B
  refine ⟨fun a b ha hb hab => ?_, fun a ha hodd => ?_⟩
  · have ha' : a ∉ Z.erase v := fun h' => ha (Finset.mem_of_mem_erase h')
    have hb' : b ∉ Z.erase v := fun h' => hb (Finset.mem_of_mem_erase h')
    exact (link_reach_robust hα hH3 hH4 (Z.erase v) hv B d hdeg w1 w2 ha' hb' hab).mono hle
  · have ha' : a ∉ Z.erase v := fun h' => ha (Finset.mem_of_mem_erase h')
    exact oddAt_mono hle (link_oddAt_robust hα hH3 hH4 (Z.erase v) hv B d hdeg w1 w2 ha' hodd)

/-- **Conexión robusta de una componente del enlace.** -/
theorem link_robustConn {H : Host V I} {F : Set (Multiset I)} {α : ℝ} {h : ℕ}
    (hα : 0 < α) (hH3 : CommonNbrCond H F α) (hH4 : HingeCond H F α h) (v a : V)
    {ζ ρ : ℝ} (hρ : 0 ≤ ρ)
    (hw1 : ζ * Fintype.card V + 2 + 4 * (ρ * Fintype.card V) < α * Fintype.card V)
    (hw2 : (ζ * Fintype.card V + h + 5 * (ρ * Fintype.card V)) * 2 ^ Nat.choose h 2 ≤
      α / 2 * Fintype.card V) :
    RobustConn (linkGraph H F v) (compOf (linkGraph H F v) a) ζ ρ := by
  intro Z B hZ hB x hx y hy hxZ hyZ
  exact (link_delG_robust hα hH3 hH4 v hρ hw1 hw2 Z B hZ hB).1 x y hxZ hyZ (compOf_reach hx hy)

/-- Grado de la cubierta. -/
lemma dcover_degree (J : SimpleGraph Ω) (x : Ω) (σ : Bool) :
    (univ.filter ((dcover J).Adj (x, σ))).card = (univ.filter (J.Adj x)).card := by
  refine (Finset.card_bij (fun p _ => p.1) ?_ ?_ ?_).symm.symm
  · intro p hp; simpa using (Finset.mem_filter.1 hp).2.1
  · intro p hp q hq hpq
    have h1 := (Finset.mem_filter.1 hp).2.2
    have h2 := (Finset.mem_filter.1 hq).2.2
    ext
    · exact hpq
    · simp only at h1 h2
      cases σ <;> cases hp2 : p.2 <;> cases hq2 : q.2 <;> simp_all
  · intro y hy
    exact ⟨(y, !σ), Finset.mem_filter.2 ⟨Finset.mem_univ _, (Finset.mem_filter.1 hy).2,
      by cases σ <;> simp⟩, rfl⟩

lemma card_prod_bool : Fintype.card (V × Bool) = 2 * Fintype.card V := by
  rw [Fintype.card_prod, Fintype.card_bool, mul_comm]

lemma dcover_minDegOn {H : Host V I} {F : Set (Multiset I)} {α : ℝ} (hH3 : CommonNbrCond H F α)
    {v : V} {K : Finset V} (hKa : ∀ x ∈ K, Active (linkGraph H F v) x) :
    MinDegOn (dcover (linkGraph H F v)) (K ×ˢ (univ : Finset Bool)) (α / 2) := by
  intro p hp
  obtain ⟨w, hw⟩ := hKa p.1 (Finset.mem_product.1 hp).1
  rw [card_prod_bool, dcover_degree]
  have := link_minDeg hH3 hw
  push_cast
  linarith

omit [Fintype Ω] in
lemma dcover_closed (J : SimpleGraph Ω) {K : Finset Ω} (hK : NbrClosed J K) :
    NbrClosed (dcover J) (K ×ˢ (univ : Finset Bool)) := by
  intro p hp q hpq
  exact Finset.mem_product.2 ⟨hK _ (Finset.mem_product.1 hp).1 _ hpq.1, Finset.mem_univ _⟩

/-- Grado de la proyección de un conjunto de aristas de la cubierta. -/
lemma degIn_map_fst_le (B : Finset (Sym2 (Ω × Bool))) (x : Ω) :
    degIn (B.image (Sym2.map Prod.fst)) x ≤ degIn B (x, false) + degIn B (x, true) := by
  unfold degIn
  have hsub : (B.image (Sym2.map Prod.fst)).filter (fun e => x ∈ e) ⊆
      (B.filter (fun e => (x, false) ∈ e) ∪ B.filter (fun e => (x, true) ∈ e)).image
        (Sym2.map Prod.fst) := by
    intro e he
    obtain ⟨he1, hx⟩ := Finset.mem_filter.1 he
    obtain ⟨f, hf, rfl⟩ := Finset.mem_image.1 he1
    obtain ⟨p, hp, hpx⟩ := Sym2.mem_map.1 hx
    refine Finset.mem_image.2 ⟨f, ?_, rfl⟩
    have : p = (x, p.2) := by ext <;> simp [hpx]
    cases hb : p.2
    · exact Finset.mem_union_left _ (Finset.mem_filter.2 ⟨hf, by rw [← hb, ← this]; exact hp⟩)
    · exact Finset.mem_union_right _ (Finset.mem_filter.2 ⟨hf, by rw [← hb, ← this]; exact hp⟩)
  refine (Finset.card_le_card hsub).trans (Finset.card_image_le.trans ?_)
  convert Finset.card_union_le _ _

/-- **Conexión robusta de la doble cubierta de una componente no bipartita.** -/
theorem cover_robustConn {H : Host V I} {F : Set (Multiset I)} {α : ℝ} {h : ℕ}
    (hα : 0 < α) (hH3 : CommonNbrCond H F α) (hH4 : HingeCond H F α h) (v : V)
    {K : Finset V} (hK : NbrClosed (linkGraph H F v) K)
    (hKr : ∀ a ∈ K, ∀ b ∈ K, (linkGraph H F v).Reachable a b)
    (hKo : ∀ a ∈ K, OddAt (linkGraph H F v) a)
    {ζ ρ : ℝ} (hρ : 0 ≤ ρ)
    (hw1 : ζ * Fintype.card V + 2 + 4 * (ρ * Fintype.card V) < α * Fintype.card V)
    (hw2 : (ζ * Fintype.card V + h + 5 * (ρ * Fintype.card V)) * 2 ^ Nat.choose h 2 ≤
      α / 2 * Fintype.card V) :
    RobustConn (dcover (linkGraph H F v)) (K ×ˢ (univ : Finset Bool)) (ζ / 2) (ρ / 4) := by
  intro Zt Bt hZ hB p hp q hq hpZ hqZ
  set L := linkGraph H F v
  set n : ℝ := (Fintype.card V : ℝ)
  have hN : (Fintype.card (V × Bool) : ℝ) = 2 * n := by rw [card_prod_bool]; push_cast; ring
  rw [hN] at hZ hB
  set Z' := Zt.image Prod.fst
  set B' := Bt.image (Sym2.map Prod.fst)
  have hZ' : (Z'.card : ℝ) ≤ ζ * n := by
    have : (Z'.card : ℝ) ≤ Zt.card := by exact_mod_cast Finset.card_image_le
    linarith
  have hB' : ∀ x, (degIn B' x : ℝ) ≤ ρ * n := by
    intro x
    have h1 : (degIn B' x : ℝ) ≤ degIn Bt (x, false) + degIn Bt (x, true) := by
      exact_mod_cast degIn_map_fst_le Bt x
    have := hB (x, false); have := hB (x, true)
    linarith
  obtain ⟨hreach, hoddR⟩ := link_delG_robust hα hH3 hH4 v hρ hw1 hw2 Z' B' hZ' hB'
  -- la cubierta del grafo borrado está en el borrado de la cubierta
  have hle : dcover (delG L Z' B') ≤ delG (dcover L) Zt Bt := by
    intro a b ⟨⟨hab, ha, hb, hB⟩, hne⟩
    refine ⟨⟨hab, hne⟩, fun h' => ha (Finset.mem_image_of_mem _ h'),
      fun h' => hb (Finset.mem_image_of_mem _ h'), fun h' => hB ?_⟩
    exact Finset.mem_image.2 ⟨_, h', by simp⟩
  -- paso a un vecino libre
  have step : ∀ a ∈ K ×ˢ (univ : Finset Bool), a ∉ Zt →
      ∃ y ∈ K, y ∉ Z' ∧ ∃ τ, (delG (dcover L) Zt Bt).Reachable a (y, τ) := by
    intro a ha haZ
    have haK := (Finset.mem_product.1 ha).1
    by_cases ha' : a.1 ∈ Z'
    · obtain ⟨w, hw⟩ : Active L a.1 := by
        obtain ⟨c, hc⟩ := hKo a.1 haK
        cases c with
        | nil => simp at hc
        | cons h' _ => exact ⟨_, h'⟩
      have hdeg := link_minDeg hH3 hw
      by_contra hno
      push_neg at hno
      have hsub : univ.filter (L.Adj a.1) ⊆
          Z' ∪ univ.filter (fun y => s(a, (y, !a.2)) ∈ Bt) := by
        intro y hy
        have hy' := (Finset.mem_filter.1 hy).2
        by_contra hyn
        simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and, not_or] at hyn
        have hadj : (delG (dcover L) Zt Bt).Adj a (y, !a.2) :=
          ⟨⟨hy', by cases a.2 <;> simp⟩, haZ,
            fun h' => hyn.1 (Finset.mem_image.2 ⟨_, h', rfl⟩), hyn.2⟩
        exact hno y (hK _ haK _ hy') hyn.1 (!a.2) hadj.reachable
      have hmid : (univ.filter (fun y => s(a, (y, !a.2)) ∈ Bt)).card ≤ degIn Bt a := by
        unfold degIn
        refine Finset.card_le_card_of_injOn (fun y => s(a, (y, !a.2))) ?_ ?_
        · intro y hy
          simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq] at hy
          simp [hy]
        · intro y _ z _ hyz
          simp only [Sym2.eq_iff, Prod.mk.injEq] at hyz
          rcases hyz with ⟨-, h1, -⟩ | ⟨h1, -⟩
          · exact h1
          · have := congrArg Prod.snd h1
            simp at this
      have h1 := (Finset.card_le_card hsub).trans (Finset.card_union_le _ _)
      have h2 : ((univ.filter (L.Adj a.1)).card : ℝ) ≤ Z'.card + degIn Bt a := by
        exact_mod_cast h1.trans (by omega)
      have := hB a
      nlinarith
    · exact ⟨a.1, haK, ha', a.2, SimpleGraph.Reachable.refl _⟩
  obtain ⟨y1, hy1K, hy1Z, τ1, hr1⟩ := step p hp hpZ
  obtain ⟨y2, hy2K, hy2Z, τ2, hr2⟩ := step q hq hqZ
  have hbase := hreach y1 y2 hy1Z hy2Z (hKr y1 hy1K y2 hy2K)
  have hodd := hoddR y1 hy1Z (hKo y1 hy1K)
  have hmid := (dcover_reach_all hodd hbase τ1 τ2).mono hle
  exact hr1.trans (hmid.trans hr2.symm)

end TypedTriangle
