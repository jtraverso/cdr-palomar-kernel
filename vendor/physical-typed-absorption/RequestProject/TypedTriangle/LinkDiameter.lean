/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import RequestProject.TypedTriangle.LinkRobust

@[expose] public section

/-!
# G1-Z, §4.3 de la guía V5 — Diámetro uniforme de los enlaces restringidos

* `diamLe_of_minDeg` (combinatoria pura): si todo vértice no aislado tiene grado `≥ δ > 0`,
  dos vértices conectados se unen por un recorrido de longitud `≤ 3⌊n/δ⌋`. En una geodésica,
  los vértices de posiciones `0, 3, 6, …` tienen vecindarios disjuntos.
* `linkOn_good_degree`: en el enlace de `z` restringido a aristas base que evitan `Z` y `B`
  (grado de `B` `≤ d`), todo vértice ACTIVO tiene grado `≥ αn − |Z| − d` (de H3). Los vértices
  inactivos son aislados y no se cuentan.
* `linkOn_good_diamLe`: si `|Z| + d ≤ αn/2`, el enlace restringido tiene diámetro
  `≤ D₀ = 3⌊2/α⌋`, uniforme (no depende de `n`, del host ni de la demanda).
* `linkOn_good_section`: combinando con `IncidenceSection`, una sección `ℤ`-lineal de la
  incidencia del enlace restringido sobre su imagen entera, de coste `≤ (2D₀+1)‖·‖₁`.
No se usa teoría espectral.
-/

open Finset

noncomputable section
open Classical

namespace TypedTriangle

open Incidence

namespace Incidence

variable {V : Type*} [Fintype V]

omit [Fintype V] in
lemma exists_adj_getVert {G : SimpleGraph V} {u v : V} (p : G.Walk u v) {k : ℕ}
    (hk : k ≤ p.length) (hL : 0 < p.length) : ∃ w, G.Adj (p.getVert k) w := by
  rcases Nat.lt_or_ge k p.length with h | h
  · exact ⟨_, p.adj_getVert_succ h⟩
  · have hk' : k = p.length := le_antisymm hk h
    have h1 : k - 1 < p.length := by omega
    have := p.adj_getVert_succ h1
    rw [show k - 1 + 1 = k by omega] at this
    exact ⟨_, this.symm⟩

/-- **Diámetro desde el grado mínimo.** -/
theorem diamLe_of_minDeg {G : SimpleGraph V} {δ : ℕ} (hδ : 0 < δ)
    (hdeg : ∀ v w, G.Adj v w → δ ≤ (univ.filter (G.Adj v)).card) :
    DiamLe G (3 * (Fintype.card V / δ)) := by
  intro u v huv
  obtain ⟨p, hp⟩ := huv.exists_walk_length_eq_dist
  refine ⟨p, ?_⟩
  set L := p.length with hLdef
  rcases Nat.eq_zero_or_pos L with hL | hL
  · rw [hL]; exact Nat.zero_le _
  set m := L / 3
  set N : ℕ → Finset V := fun i => univ.filter (G.Adj (p.getVert (3 * i)))
  have hcard : ∀ i ∈ range (m + 1), δ ≤ (N i).card := by
    intro i hi
    have hi' : 3 * i ≤ L := by
      have := Finset.mem_range.1 hi
      have : i ≤ m := by omega
      have := Nat.mul_div_le L 3
      omega
    obtain ⟨w, hw⟩ := exists_adj_getVert p hi' hL
    exact hdeg _ _ hw
  have hdisj : ∀ i ∈ range (m + 1), ∀ j ∈ range (m + 1), i ≠ j → Disjoint (N i) (N j) := by
    -- basta el caso `i < j`
    have key : ∀ i j, i < j → j ≤ m → Disjoint (N i) (N j) := by
      intro i j hij hj
      rw [Finset.disjoint_left]
      intro y hyi hyj
      simp only [N, Finset.mem_filter, Finset.mem_univ, true_and] at hyi hyj
      have h3j : 3 * j ≤ L := by
        have := Nat.mul_div_le L 3
        omega
      let q : G.Walk u v := (p.take (3 * i)).append
        (SimpleGraph.Walk.cons hyi (SimpleGraph.Walk.cons hyj.symm (p.drop (3 * j))))
      have hq : q.length ≤ 3 * i + 2 + (L - 3 * j) := by
        simp only [q, SimpleGraph.Walk.length_append, SimpleGraph.Walk.length_cons,
          SimpleGraph.Walk.take_length, SimpleGraph.Walk.drop_length]
        have := min_le_left (3 * i) L
        omega
      have := SimpleGraph.dist_le q
      omega
    intro i hi j hj hij
    rcases Nat.lt_or_gt_of_ne hij with h | h
    · exact key i j h (by have := Finset.mem_range.1 hj; omega)
    · exact (key j i h (by have := Finset.mem_range.1 hi; omega)).symm
  have hsum : (m + 1) * δ ≤ Fintype.card V := by
    calc (m + 1) * δ = ∑ _i ∈ range (m + 1), δ := by simp
      _ ≤ ∑ i ∈ range (m + 1), (N i).card := Finset.sum_le_sum hcard
      _ = ((range (m + 1)).biUnion N).card :=
          (Finset.card_biUnion fun i hi j hj hij => hdisj i hi j hj hij).symm
      _ ≤ Fintype.card V := Finset.card_le_univ _
  have hm : m + 1 ≤ Fintype.card V / δ := (Nat.le_div_iff_mul_le hδ).2 hsum
  have := Nat.lt_mul_div_succ L (by norm_num : 0 < 3)
  omega

end Incidence

variable {V I : Type*} [Fintype V]

/-- **Grado de los vértices activos del enlace restringido (de H3).** -/
theorem linkOn_good_degree {H : Host V I} {F : Set (Multiset I)} {α : ℝ}
    (hH3 : CommonNbrCond H F α) {z : V} (Z : Finset V) (B : Finset (Sym2 V)) {d : ℕ}
    (hdeg : ∀ x, degIn B x ≤ d) {a w : V}
    (haw : (linkOn H F z (goodEdges H Z B)).Adj a w) :
    α * Fintype.card V ≤
      ((univ.filter ((linkOn H F z (goodEdges H Z B)).Adj a)).card : ℝ) + Z.card + d := by
  have hTw : IsAllowed H F {z, a, w} := haw.1.2
  obtain ⟨hza, hzw, haw'⟩ := distinct_of_card_three hTw.1
  have hc := hH3 z a hza (H.lab w) (by
    have := hTw.2.2
    rwa [Finset.insert_val_of_notMem (by simp [hza, hzw]),
      Finset.insert_val_of_notMem (by simp [haw'])] at this)
  have haZ : a ∉ Z := fun h => (Finset.mem_filter.1 (Finset.mem_filter.1 haw.2).1).2 a h (by simp)
  have hsub : commonNbrs H (H.lab w) z a ⊆
      univ.filter ((linkOn H F z (goodEdges H Z B)).Adj a) ∪ (Z ∪ nbrIn B a) := by
    intro t ht
    have hTt : IsAllowed H F {z, a, t} := allowed_of_commonNbr hTw ht
    obtain ⟨-, -, hat⟩ := distinct_of_card_three hTt.1
    by_cases htZ : t ∈ Z
    · exact Finset.mem_union_right _ (Finset.mem_union_left _ htZ)
    by_cases htB : s(a, t) ∈ B
    · exact Finset.mem_union_right _ (Finset.mem_union_right _
        (by simp [nbrIn, htB]))
    refine Finset.mem_union_left _ (Finset.mem_filter.2 ⟨Finset.mem_univ _, ⟨hat, hTt⟩, ?_⟩)
    simp only [goodEdges, avoidSet, Finset.mem_filter]
    refine ⟨⟨?_, fun y hy hyat => ?_⟩, htB⟩
    · have := hTt.2.1 a (by simp) t (by simp) hat
      simp [edges, this]
    · rcases Sym2.mem_iff.1 hyat with rfl | rfl
      · exact haZ hy
      · exact htZ hy
  have h1 := Finset.card_le_card hsub
  have h2 := Finset.card_union_le (univ.filter ((linkOn H F z (goodEdges H Z B)).Adj a))
    (Z ∪ nbrIn B a)
  have h3 := Finset.card_union_le Z (nbrIn B a)
  have h4 := (card_nbrIn_le B a).trans (hdeg a)
  have : ((commonNbrs H (H.lab w) z a).card : ℝ) ≤
      ((univ.filter ((linkOn H F z (goodEdges H Z B)).Adj a)).card : ℝ) + Z.card + d := by
    exact_mod_cast (h1.trans h2).trans (by omega)
  linarith

/-- **Diámetro uniforme del enlace restringido.** Si `|Z| + d ≤ αn/2`, el enlace de `z`
restringido a las aristas base buenas tiene diámetro `≤ 3⌊2/α⌋`. -/
theorem linkOn_good_diamLe {H : Host V I} {F : Set (Multiset I)} {α : ℝ} (hα : 0 < α)
    (hH3 : CommonNbrCond H F α) (z : V) (Z : Finset V) (B : Finset (Sym2 V)) {d : ℕ}
    (hdeg : ∀ x, degIn B x ≤ d) (hwin : (Z.card : ℝ) + d ≤ α * Fintype.card V / 2) :
    DiamLe (linkOn H F z (goodEdges H Z B)) (3 * ⌊2 / α⌋₊) := by
  have hn : (0 : ℝ) < Fintype.card V := by
    have : Nonempty V := ⟨z⟩
    exact_mod_cast Fintype.card_pos
  set δ := ⌈α * Fintype.card V / 2⌉₊ with hδdef
  have hδpos : 0 < δ := Nat.ceil_pos.2 (by positivity)
  have hdegδ : ∀ v w, (linkOn H F z (goodEdges H Z B)).Adj v w →
      δ ≤ (univ.filter ((linkOn H F z (goodEdges H Z B)).Adj v)).card := by
    intro v w hvw
    have := linkOn_good_degree hH3 Z B hdeg hvw
    exact Nat.ceil_le.2 (by linarith)
  have hD := diamLe_of_minDeg hδpos hdegδ
  have hle : Fintype.card V / δ ≤ ⌊2 / α⌋₊ := by
    apply Nat.le_floor
    have h1 : ((Fintype.card V / δ : ℕ) : ℝ) ≤ (Fintype.card V : ℝ) / δ := Nat.cast_div_le
    have h2 : α * Fintype.card V / 2 ≤ (δ : ℝ) := Nat.le_ceil _
    have h3 : (Fintype.card V : ℝ) / δ ≤ 2 / α := by
      rw [div_le_div_iff₀ (by positivity) hα]
      nlinarith
    linarith
  intro u v huv
  obtain ⟨p, hp⟩ := hD u v huv
  exact ⟨p, hp.trans (by omega)⟩

/-- **Sección uniforme sobre el enlace restringido.** Con `|Z| + d ≤ αn/2`, existe un
homomorfismo `ℤ`-lineal de la imagen entera de la incidencia del enlace restringido en sus
cadenas, que es una sección y cuesta `≤ (2·3⌊2/α⌋ + 1)‖·‖₁`. -/
theorem linkOn_good_section {H : Host V I} {F : Set (Multiset I)} {α : ℝ} (hα : 0 < α)
    (hH3 : CommonNbrCond H F α) (z : V) (Z : Finset V) (B : Finset (Sym2 V)) {d : ℕ}
    (hdeg : ∀ x, degIn B x ≤ d) (hwin : (Z.card : ℝ) + d ≤ α * Fintype.card V / 2) :
    ∃ s : incLattice (linkOn H F z (goodEdges H Z B)) →ₗ[ℤ] (Sym2 V → ℤ),
      ∀ x, bd (s x) = x.1 ∧ (∀ e, s x e ≠ 0 → e ∈ (linkOn H F z (goodEdges H Z B)).edgeSet) ∧
        l1E (s x) ≤ (2 * (3 * ⌊2 / α⌋₊ : ℕ) + 1) * l1V x.1 :=
  exists_linear_section (linkOn_good_diamLe hα hH3 z Z B hdeg hwin)

end TypedTriangle
