/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import RequestProject.TypedTriangle.Elimination

@[expose] public section

/-!
# G1-Z, §5 de la guía V5 — De la conservación combinatoria a la igualdad de imágenes

El lema muestral de `MUESTREO_ENLACES.md` produce una propiedad COMBINATORIA del inducido
`G[W]`: cada componente de `G` que corta a `W` lo hace en un conjunto conexo de `G[W]`, y una
componente no bipartita sigue siéndolo en `G[W]`. Este archivo traduce esa propiedad a la
igualdad de imágenes ENTERAS que usa la eliminación (campo `image` de `SampleOut`):

`incLattice_induced_of_preserve`: si `y` está soportado en `W` y `y ∈ im_ℤ B_G`, entonces
`y ∈ im_ℤ B_{G[W]}`.

La prueba usa la caracterización `mem_incLattice_iff` (balances en las componentes bipartitas
y paridades): cada función alternante `σ` de `G[W]` se extiende a una de `G` que coincide en
`W` (cero en las componentes no bipartitas, por la conservación del recorrido impar), y cada
conjunto cerrado de `G[W]` se extiende al conjunto cerrado de `G` de las componentes que lo
cortan (conexión conservada). No se usa saturación racional.

`sampleOut_of_goodRoots` construye la interfaz `SampleOut` desde `W`, un conjunto de raíces
malas `Z` y la conservación combinatoria en las raíces buenas.
-/

open Finset

noncomputable section
open Classical

namespace TypedTriangle

open Incidence

variable {V I : Type*} [Fintype V]

namespace Incidence

/-- Inducido de `G` sobre `W` (como grafo sobre todo `V`). -/
def inducedOn (G : SimpleGraph V) (W : Finset V) : SimpleGraph V where
  Adj a b := G.Adj a b ∧ a ∈ W ∧ b ∈ W
  symm := ⟨fun _ _ h => ⟨h.1.symm, h.2.2, h.2.1⟩⟩
  loopless := ⟨fun _ h => G.loopless.irrefl _ h.1⟩

omit [Fintype V] in
lemma inducedOn_le (G : SimpleGraph V) (W : Finset V) : inducedOn G W ≤ G := fun _ _ h => h.1

omit [Fintype V] in
/-- Una función alternante de `G'` alterna a lo largo de los recorridos de `G'`. -/
lemma alt_along_walk {G' : SimpleGraph V} {σ : V → ℤ} (hσ : ∀ u v, G'.Adj u v → σ u + σ v = 0)
    {a b : V} (q : G'.Walk a b) : σ a = (-1) ^ q.length * σ b := by
  induction q with
  | nil => simp
  | @cons x y z h q ih =>
    rw [SimpleGraph.Walk.length_cons, pow_succ, show σ x = -σ y by linarith [hσ x y h], ih]
    ring

omit [Fintype V] in
lemma oddAt_of_reach {G : SimpleGraph V} {a b : V} (hab : G.Reachable b a) (ha : OddAt G a) :
    OddAt G b := by
  obtain ⟨p⟩ := hab
  obtain ⟨c, hc⟩ := ha
  refine ⟨(p.append c).append p.reverse, ?_⟩
  simp only [SimpleGraph.Walk.length_append, SimpleGraph.Walk.length_reverse]
  rw [show p.length + c.length + p.length = c.length + 2 * p.length by ring]
  exact hc.add_even (even_two_mul _)

omit [Fintype V] in
/-- Un conjunto cerrado se conserva a lo largo de los recorridos. -/
lemma closed_along_walk {G : SimpleGraph V} {S : Finset V}
    (hS : ∀ u v, G.Adj u v → (u ∈ S ↔ v ∈ S)) {a b : V} (q : G.Walk a b) :
    a ∈ S ↔ b ∈ S := by
  induction q with
  | nil => rfl
  | cons h q ih => exact (hS _ _ h).trans ih

/-- **Transferencia de la imagen entera al inducido.** -/
theorem incLattice_induced_of_preserve (G : SimpleGraph V) (W : Finset V)
    (hconn : ∀ a ∈ W, ∀ b ∈ W, G.Reachable a b → (inducedOn G W).Reachable a b)
    (hodd : ∀ a ∈ W, OddAt G a → OddAt (inducedOn G W) a)
    {y : V → ℤ} (hy : ∀ v, v ∉ W → y v = 0) (hyG : y ∈ incLattice G) :
    y ∈ incLattice (inducedOn G W) := by
  set G' := inducedOn G W
  have hle : G' ≤ G := inducedOn_le G W
  have hG := incLattice_necessary hyG
  rw [mem_incLattice_iff]
  refine ⟨fun σ hσ => ?_, fun S hS => ?_⟩
  · -- extensión de `σ`
    let σ' : V → ℤ := fun v =>
      if h : ∃ a ∈ W, G.Reachable v a then
        (if OddAt G (Classical.choose h) then 0
          else (-1) ^ (Classical.choose_spec h).2.some.length *
            σ (Classical.choose h))
      else 0
    -- valor de `σ'` en un vértice con un representante `a` cualquiera
    have hval : ∀ v a (haW : a ∈ W) (p : G.Walk v a),
        σ' v = if OddAt G a then 0 else (-1) ^ p.length * σ a := by
      intro v a haW p
      have hex : ∃ a ∈ W, G.Reachable v a := ⟨a, haW, ⟨p⟩⟩
      simp only [σ', dif_pos hex]
      set a' := Classical.choose hex
      have ha'W : a' ∈ W := (Classical.choose_spec hex).1
      set p' := (Classical.choose_spec hex).2.some
      have hreach : G.Reachable a a' := ⟨p.reverse.append p'⟩
      have hodd_iff : OddAt G a ↔ OddAt G a' :=
        ⟨fun h => oddAt_of_reach hreach.symm h, fun h => oddAt_of_reach hreach h⟩
      by_cases hoa : OddAt G a
      · rw [if_pos (hodd_iff.1 hoa), if_pos hoa]
      · rw [if_neg (fun h => hoa (hodd_iff.2 h)), if_neg hoa]
        obtain ⟨q⟩ := hconn a haW a' ha'W hreach
        have hσq := alt_along_walk hσ q
        have hno : ∀ c : G.Walk a' a', ¬ Odd c.length :=
          fun c hc => hoa (hodd_iff.2 ⟨c, hc⟩)
        have hpar := parity_unique hno p' (p.append (q.map (SimpleGraph.Hom.ofLE hle)))
        rw [hpar, SimpleGraph.Walk.length_append, SimpleGraph.Walk.length_map, pow_add, hσq]
        ring
    -- `σ'` es alternante en `G`
    have hσ'adm : ∀ u v, G.Adj u v → σ' u + σ' v = 0 := by
      intro u v huv
      by_cases hex : ∃ a ∈ W, G.Reachable v a
      · obtain ⟨a, haW, ⟨p⟩⟩ := hex
        rw [hval u a haW (SimpleGraph.Walk.cons huv p), hval v a haW p]
        split_ifs
        · simp
        · simp only [SimpleGraph.Walk.length_cons, pow_succ]; ring
      · have hexu : ¬ ∃ a ∈ W, G.Reachable u a := by
          rintro ⟨a, haW, hr⟩
          exact hex ⟨a, haW, huv.reachable.symm.trans hr⟩
        simp [σ', hex, hexu]
    -- `σ'` coincide con `σ` en `W`
    have hagree : ∀ v ∈ W, σ' v = σ v := by
      intro v hvW
      rw [hval v v hvW SimpleGraph.Walk.nil]
      split_ifs with hov
      · obtain ⟨q, hq⟩ := hodd v hvW hov
        have := alt_along_walk hσ q
        rw [hq.neg_one_pow] at this
        linarith
      · simp
    have h0 := hG.1 σ' hσ'adm
    rw [← h0]
    refine Finset.sum_congr rfl fun v _ => ?_
    by_cases hvW : v ∈ W
    · rw [hagree v hvW]
    · rw [hy v hvW]; ring
  · -- extensión del conjunto cerrado
    set S' := univ.filter (fun v => ∃ u ∈ S, u ∈ W ∧ G.Reachable v u)
    have hS' : ∀ u v, G.Adj u v → (u ∈ S' ↔ v ∈ S') := by
      intro u v huv
      simp only [S', Finset.mem_filter, Finset.mem_univ, true_and]
      constructor
      · rintro ⟨w, hw, hwW, hr⟩; exact ⟨w, hw, hwW, huv.reachable.symm.trans hr⟩
      · rintro ⟨w, hw, hwW, hr⟩; exact ⟨w, hw, hwW, huv.reachable.trans hr⟩
    have hev := hG.2 S' hS'
    have hiff : ∀ v ∈ W, (v ∈ S' ↔ v ∈ S) := by
      intro v hvW
      simp only [S', Finset.mem_filter, Finset.mem_univ, true_and]
      constructor
      · rintro ⟨u, hu, huW, hr⟩
        obtain ⟨q⟩ := hconn v hvW u huW hr
        exact (closed_along_walk hS q).2 hu
      · intro hv; exact ⟨v, hv, hvW, SimpleGraph.Reachable.refl v⟩
    have heq : ∑ v ∈ S', y v = ∑ v ∈ S, y v := by
      rw [← Finset.sum_filter_add_sum_filter_not S' (· ∈ W),
        ← Finset.sum_filter_add_sum_filter_not S (· ∈ W)]
      have h1 : ∑ v ∈ S'.filter (· ∉ W), y v = 0 :=
        Finset.sum_eq_zero fun v hv => hy v (Finset.mem_filter.1 hv).2
      have h2 : ∑ v ∈ S.filter (· ∉ W), y v = 0 :=
        Finset.sum_eq_zero fun v hv => hy v (Finset.mem_filter.1 hv).2
      rw [h1, h2]
      congr 1
      refine Finset.sum_congr ?_ fun _ _ => rfl
      ext v
      simp only [Finset.mem_filter]
      constructor
      · rintro ⟨h1, h2⟩; exact ⟨(hiff v h2).1 h1, h2⟩
      · rintro ⟨h1, h2⟩; exact ⟨(hiff v h2).2 h1, h2⟩
    rw [← heq]; exact hev

end Incidence

omit [Fintype V] in
/-- El enlace sobre `W` es el inducido del enlace. -/
lemma linkOn_sym2_eq (H : Host V I) (F : Set (Multiset I)) (v : V) (W : Finset V) :
    linkOn H F v W.sym2 = inducedOn (linkGraph H F v) W := by
  ext a b
  simp only [linkOn, inducedOn, Finset.mem_sym2_iff]
  constructor
  · rintro ⟨h, hW⟩; exact ⟨h, hW a (by simp), hW b (by simp)⟩
  · rintro ⟨h, ha, hb⟩
    refine ⟨h, fun x hx => ?_⟩
    rcases Sym2.mem_iff.1 hx with rfl | rfl
    · exact ha
    · exact hb

/-- Raíz buena: el inducido de su enlace sobre `W` conserva conexión y recorridos impares. -/
def GoodRoot (H : Host V I) (F : Set (Multiset I)) (W : Finset V) (v : V) : Prop :=
  (∀ a ∈ W, ∀ b ∈ W, (linkGraph H F v).Reachable a b →
    (inducedOn (linkGraph H F v) W).Reachable a b) ∧
  (∀ a ∈ W, OddAt (linkGraph H F v) a → OddAt (inducedOn (linkGraph H F v) W) a)

/-- Aristas exteriores con triángulo y sin tercero en `W` (el grafo `B` de la guía). -/
def badEdges (H : Host V I) (F : Set (Multiset I)) (W Z : Finset V) : Finset (Sym2 V) :=
  univ.filter (fun e => HasTri H F e ∧ (∀ y ∈ e, y ∉ W ∧ y ∉ Z) ∧
    ¬ ∃ u v t, e = s(u, v) ∧ t ∈ W ∧ IsAllowed H F {u, v, t})

/-- **Construcción de la interfaz muestral desde raíces buenas.** Si `W ∩ Z = ∅`, toda raíz
fuera de `W ∪ Z` es buena y el grafo `B` de aristas exteriores sin tercero en `W` tiene grado
`≤ d`, se obtiene `SampleOut`. -/
def sampleOut_of_goodRoots (H : Host V I) (F : Set (Multiset I)) {s d : ℕ} (W Z : Finset V)
    (hW : W.card ≤ s) (hWZ : Disjoint W Z) (hgood : ∀ v, v ∉ W → v ∉ Z → GoodRoot H F W v)
    (hdeg : ∀ x, degIn (badEdges H F W Z) x ≤ d) : SampleOut H F s d where
  W := W
  Z := Z
  B := badEdges H F W Z
  card_W := hW
  disj := hWZ
  image v hvW hvZ y hy hyG := by
    rw [linkOn_sym2_eq]
    exact incLattice_induced_of_preserve _ W (hgood v hvW hvZ).1 (hgood v hvW hvZ).2 hy hyG
  B_out e he := (Finset.mem_filter.1 he).2.2.1
  B_full e hT hout heB := by
    by_contra h
    exact heB (Finset.mem_filter.2 ⟨Finset.mem_univ _, hT, hout, h⟩)
  B_deg := hdeg

/-- **G1-Z reducido a la conservación combinatoria en una muestra.** Hay `K = K(α, s)` tal
que, para todo host con H3 y H4, si existen `W` (`|W| ≤ s`) y `Z` disjuntos con todas las
raíces fuera de `W ∪ Z` buenas, el grafo `B` de grado `≤ d` y las ventanas sobre `|Z|` y `d`,
entonces todo `x ∈ Λ_H` tiene un certificado entero de norma `≤ K‖x‖₁`. -/
theorem uniformCert_of_goodRoots (α : ℝ) (s : ℕ) :
    ∃ K : ℕ, ∀ {V I : Type} [Fintype V] (H : Host V I) (F : Set (Multiset I)) {h d : ℕ},
      0 < α → CommonNbrCond H F α → HingeCond H F α h → ∀ W Z : Finset V, W.card ≤ s →
      Disjoint W Z → (∀ v, v ∉ W → v ∉ Z → GoodRoot H F W v) →
      (∀ x, degIn (badEdges H F W Z) x ≤ d) →
      (Z.card : ℝ) + 2 + 4 * d < α * Fintype.card V →
      ((Z.card : ℝ) + h + 5 * d) * 2 ^ Nat.choose h 2 ≤ α / 2 * Fintype.card V →
      (Z.card : ℝ) + d ≤ α * Fintype.card V / 2 → UniformCert H F K := by
  obtain ⟨K, hK⟩ := uniformCert_of_sample α s
  refine ⟨K, fun {V I} _ H F h d hα hH3 hH4 W Z hW hWZ hgood hdeg hw1 hw2 hw3 => ?_⟩
  exact hK H F hα hH3 hH4 (sampleOut_of_goodRoots H F W Z hW hWZ hgood hdeg) hw1 hw2 hw3

end TypedTriangle
