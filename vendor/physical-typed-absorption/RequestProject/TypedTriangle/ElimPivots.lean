/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import RequestProject.TypedTriangle.ElimTools

@[expose] public section

/-!
# G1-Z, §6 de la guía V5 — Interfaz muestral y pivotes de los eventos 1, 3, 4

* `SampleOut`: la salida de la muestra de §5 (`W`, `Z`, `B`), con `|W| ≤ s`, `W ∩ Z = ∅`, la
  igualdad de imágenes enteras de los enlaces `L_v[W]` para `v ∉ W ∪ Z`, `B` formado por
  aristas exteriores, toda arista exterior fuera de `B` con triángulo tiene un tercero en `W`,
  y grado de `B` `≤ d`. Es una INTERFAZ CONDICIONAL: la muestra no está construida aquí.
* Los sistemas de pivotes de los eventos 1 (aristas internas de `Z`), 3 (aristas de `B`) y
  4 (aristas exteriores con tercero en `W`), construidos desde H3 con las ventanas.
* `diamLe_of_adj_mem`: un grafo cuyas aristas tienen extremos en `W` tiene diámetro `≤ |W|`.
-/

open Finset

noncomputable section
open Classical

namespace TypedTriangle

open Incidence

variable {V I : Type*} [Fintype V] {H : Host V I} {F : Set (Multiset I)}

/-! ## Generalidades -/

/-- `e` es arista de algún triángulo permitido. -/
def HasTri (H : Host V I) (F : Set (Multiset I)) (e : Sym2 V) : Prop :=
  ∃ T, IsAllowed H F T ∧ e ∈ triEdges T

/-- En `M_H`, una arista sin triángulo permitido tiene coordenada nula. -/
lemma localGroup_zero_of_not_hasTri {x : Sym2 V → ℤ} (hx : x ∈ localGroup H F) {e : Sym2 V}
    (he : ¬ HasTri H F e) : x e = 0 := by
  by_cases hE : e ∈ edges H
  · induction e using Sym2.ind with
    | _ u v =>
    have huv : u ≠ v := by
      have : H.G.Adj u v := by simpa [edges] using hE
      exact H.G.ne_of_adj this
    refine localGroup_apply_eq_zero hx huv fun T hT huT hvT => he ⟨T, hT, ?_⟩
    exact mem_triEdges.2 ⟨huT, hvT, huv⟩
  · exact hx.1 e hE

lemma hasTri_of_mem {T : Finset V} (hT : T ∈ allowed H F) {e : Sym2 V}
    (he : e ∈ triEdges T) : HasTri H F e := ⟨T, (Finset.mem_filter.1 hT).2, he⟩

/-- Un `x ∈ M_H` sólo es no nulo en aristas con triángulo. -/
lemma hasTri_of_ne {x : Sym2 V → ℤ} (hx : x ∈ localGroup H F) {e : Sym2 V} (he : x e ≠ 0) :
    HasTri H F e := by
  by_contra h; exact he (localGroup_zero_of_not_hasTri hx h)

omit [Fintype V] in
/-- Dato de una arista con triángulo: `e = s(u,v)`, `u ≠ v`, y un tercero permitido. -/
lemma HasTri.exists_tri {e : Sym2 V} (he : HasTri H F e) :
    ∃ u v t, e = s(u, v) ∧ IsAllowed H F {u, v, t} := by
  obtain ⟨T, hT, heT⟩ := he
  induction e using Sym2.ind with
  | _ u v =>
  obtain ⟨hu, hv, huv⟩ := mem_triEdges.1 heT
  have h1 : ((T.erase u).erase v).card = 1 := by
    rw [Finset.card_erase_of_mem (by simp [hv, Ne.symm huv]), Finset.card_erase_of_mem hu, hT.1]
  obtain ⟨t, ht⟩ := Finset.card_eq_one.1 h1
  have htT : t ∈ (T.erase u).erase v := by rw [ht]; simp
  simp only [Finset.mem_erase] at htT
  have : T = {u, v, t} := by
    apply Finset.eq_of_subset_of_card_le
    · intro y hy
      by_cases hyu : y = u
      · simp [hyu]
      by_cases hyv : y = v
      · simp [hyv]
      have : y ∈ (T.erase u).erase v := by simp [hyu, hyv, hy]
      rw [ht] at this; simp at this; simp [this]
    · rw [hT.1]; exact Finset.card_le_three
  exact ⟨u, v, t, rfl, this ▸ hT⟩

omit [Fintype V] in
lemma mem_triEdges_tri {u v w : V} {e : Sym2 V} (he : e ∈ triEdges ({u, v, w} : Finset V)) :
    e = s(u, v) ∨ e = s(u, w) ∨ e = s(v, w) := by
  induction e using Sym2.ind with
  | _ a b =>
  obtain ⟨ha, hb, hab⟩ := mem_triEdges.1 he
  simp only [Finset.mem_insert, Finset.mem_singleton] at ha hb
  rcases ha with rfl | rfl | rfl <;> rcases hb with rfl | rfl | rfl <;>
    first | exact absurd rfl hab | simp [Sym2.eq_swap]

omit [Fintype V] in
lemma tri_mem_triEdges {u v w : V} (huv : u ≠ v) (huw : u ≠ w) (hvw : v ≠ w) :
    s(u, v) ∈ triEdges ({u, v, w} : Finset V) ∧ s(u, w) ∈ triEdges ({u, v, w} : Finset V) ∧
      s(v, w) ∈ triEdges ({u, v, w} : Finset V) :=
  ⟨mem_triEdges.2 ⟨by simp, by simp, huv⟩, mem_triEdges.2 ⟨by simp, by simp, huw⟩,
    mem_triEdges.2 ⟨by simp, by simp, hvw⟩⟩

lemma tri_mem_allowed {T : Finset V} (hT : IsAllowed H F T) : T ∈ allowed H F :=
  Finset.mem_filter.2 ⟨Finset.mem_univ _, hT⟩

/-- Construcción de un sistema de pivotes desde una especificación. -/
def mkPivotSys (S : Finset (Sym2 V)) (Good : Sym2 V → Finset V → Prop)
    (hex : ∀ e ∈ S, ∃ T ∈ allowed H F, e ∈ triEdges T ∧ Good e T)
    (huniq : ∀ e ∈ S, ∀ T ∈ allowed H F, e ∈ triEdges T → Good e T →
      ∀ e' ∈ S, e' ∈ triEdges T → e' = e) : PivotSys H F S where
  piv e := if h : e ∈ S then Classical.choose (hex e h) else ∅
  allowed e he := by
    rw [dif_pos he]; exact (Classical.choose_spec (hex e he)).1
  mem e he := by
    rw [dif_pos he]; exact (Classical.choose_spec (hex e he)).2.1
  uniq e he e' he' h := by
    rw [dif_pos he] at h
    have hs := Classical.choose_spec (hex e he)
    exact huniq e he _ hs.1 hs.2.1 hs.2.2 e' he' h

lemma mkPivotSys_good (S : Finset (Sym2 V)) (Good : Sym2 V → Finset V → Prop)
    (hex : ∀ e ∈ S, ∃ T ∈ allowed H F, e ∈ triEdges T ∧ Good e T) (huniq) {e : Sym2 V}
    (he : e ∈ S) : Good e ((mkPivotSys S Good hex huniq).piv e) := by
  change Good e (if h : e ∈ S then Classical.choose (hex e h) else ∅)
  rw [dif_pos he]; exact (Classical.choose_spec (hex e he)).2.2

omit [Fintype V] in
/-- Si todas las aristas de un grafo tienen extremos en `W`, su diámetro es `≤ |W|`. -/
lemma diamLe_of_adj_mem {G : SimpleGraph V} {W : Finset V} (hW : ∀ a b, G.Adj a b → a ∈ W) :
    DiamLe G W.card := by
  intro u v huv
  obtain ⟨p⟩ := huv
  refine ⟨p.bypass, ?_⟩
  set q := p.bypass
  have hq : q.IsPath := p.bypass_isPath
  rcases Nat.eq_zero_or_pos q.length with h0 | hpos
  · rw [h0]; exact Nat.zero_le _
  have hsupp : ∀ {a b : V} (r : G.Walk a b), 0 < r.length → ∀ y ∈ r.support, y ∈ W := by
    intro a b r
    induction r with
    | nil => intro h; simp at h
    | @cons a' b' c' hab r ih =>
      intro _ y hy
      rw [SimpleGraph.Walk.support_cons, List.mem_cons] at hy
      rcases hy with rfl | hy
      · exact hW _ _ hab
      · rcases Nat.eq_zero_or_pos r.length with h0 | hp
        · have : r.support = [b'] := by
            cases r with
            | nil => rfl
            | cons h _ => simp at h0
          rw [this, List.mem_singleton] at hy
          subst hy; exact hW _ _ hab.symm
        · exact ih hp y hy
  have h1 : q.support.toFinset ⊆ W := fun y hy => hsupp q hpos y (List.mem_toFinset.1 hy)
  have h2 := Finset.card_le_card h1
  rw [List.toFinset_card_of_nodup hq.support_nodup, SimpleGraph.Walk.length_support] at h2
  omega

/-! ## Interfaz muestral -/

/-- **Salida de la muestra (§5 de la guía; interfaz condicional).** -/
structure SampleOut (H : Host V I) (F : Set (Multiset I)) (s d : ℕ) where
  W : Finset V
  Z : Finset V
  B : Finset (Sym2 V)
  card_W : W.card ≤ s
  disj : Disjoint W Z
  image : ∀ v, v ∉ W → v ∉ Z → ∀ y : V → ℤ, (∀ w, w ∉ W → y w = 0) →
    y ∈ incLattice (linkGraph H F v) → y ∈ incLattice (linkOn H F v W.sym2)
  B_out : ∀ e ∈ B, ∀ y ∈ e, y ∉ W ∧ y ∉ Z
  B_full : ∀ e, HasTri H F e → (∀ y ∈ e, y ∉ W ∧ y ∉ Z) → e ∉ B →
    ∃ u v t, e = s(u, v) ∧ t ∈ W ∧ IsAllowed H F {u, v, t}
  B_deg : ∀ x, degIn B x ≤ d

/-! ## Pivotes de los eventos 1, 3 y 4 -/

/-- Evento 1: aristas internas de `Z` con triángulo; el tercero del pivote está fuera de `Z`. -/
def S1 (H : Host V I) (F : Set (Multiset I)) (Z : Finset V) : Finset (Sym2 V) :=
  univ.filter (fun e => e ∈ Z.sym2 ∧ HasTri H F e)

def Good1 (Z : Finset V) (e : Sym2 V) (T : Finset V) : Prop := ∀ y ∈ T, y ∉ e → y ∉ Z

/-- Pivotes del evento 1 (desde H3, con `|Z| < αn`). -/
def piv1 {α : ℝ} (hH3 : CommonNbrCond H F α) (Z : Finset V)
    (hZ : (Z.card : ℝ) < α * Fintype.card V) : PivotSys H F (S1 H F Z) :=
  mkPivotSys (S1 H F Z) (Good1 Z)
    (by
      intro e he
      obtain ⟨-, -, hT⟩ := Finset.mem_filter.1 he
      obtain ⟨u, v, t, rfl, hTa⟩ := hT.exists_tri
      obtain ⟨w, hTw, hwZ⟩ := exists_fresh_apex hH3 hTa Z hZ
      obtain ⟨huv, huw, hvw⟩ := distinct_of_card_three hTw.1
      refine ⟨{u, v, w}, tri_mem_allowed hTw, (tri_mem_triEdges huv huw hvw).1, ?_⟩
      intro y hy hye
      simp only [Finset.mem_insert, Finset.mem_singleton] at hy
      rcases hy with rfl | rfl | rfl
      · simp at hye
      · simp at hye
      · exact hwZ)
    (by
      intro e he T hT heT hG e' he' he'T
      obtain ⟨-, he'Z, -⟩ := Finset.mem_filter.1 he'
      rw [Finset.mem_sym2_iff] at he'Z
      have hsub : ∀ y ∈ e', y ∈ e := by
        intro y hy
        by_contra hye
        have hyT : y ∈ T := by
          induction e' using Sym2.ind with
          | _ a b =>
          obtain ⟨ha, hb, -⟩ := mem_triEdges.1 he'T
          rcases Sym2.mem_iff.1 hy with rfl | rfl
          · exact ha
          · exact hb
        exact hG y hyT hye (he'Z y hy)
      induction e using Sym2.ind with
      | _ a b =>
      induction e' using Sym2.ind with
      | _ c d =>
      obtain ⟨-, -, hcd⟩ := mem_triEdges.1 he'T
      have hc := hsub c (by simp)
      have hd := hsub d (by simp)
      rcases Sym2.mem_iff.1 hc with rfl | rfl <;> rcases Sym2.mem_iff.1 hd with rfl | rfl
      · exact absurd rfl hcd
      · rfl
      · exact Sym2.eq_swap
      · exact absurd rfl hcd)

/-- Evento 3: aristas de `B` con triángulo. -/
def S3 (H : Host V I) (F : Set (Multiset I)) (B : Finset (Sym2 V)) : Finset (Sym2 V) :=
  B.filter (HasTri H F)

def Good3 (Z : Finset V) (B : Finset (Sym2 V)) (e : Sym2 V) (T : Finset V) : Prop :=
  ∀ e' ∈ triEdges T, e' ≠ e → e' ∉ B ∧ ∀ y ∈ e', y ∉ Z

/-- Pivotes del evento 3 (desde H3, con `|Z| + 2d < αn`). -/
def piv3 {α : ℝ} (hH3 : CommonNbrCond H F α) (Z : Finset V) (B : Finset (Sym2 V)) {d : ℕ}
    (hBZ : ∀ e ∈ B, ∀ y ∈ e, y ∉ Z) (hdeg : ∀ x, degIn B x ≤ d)
    (hZ : (Z.card : ℝ) + 2 * d < α * Fintype.card V) : PivotSys H F (S3 H F B) :=
  mkPivotSys (S3 H F B) (Good3 Z B)
    (by
      intro e he
      obtain ⟨heB, hT⟩ := Finset.mem_filter.1 he
      obtain ⟨u, v, t, rfl, hTa⟩ := hT.exists_tri
      have hX : ((Z ∪ nbrIn B u ∪ nbrIn B v).card : ℝ) < α * Fintype.card V := by
        have h1 : (Z ∪ nbrIn B u ∪ nbrIn B v).card ≤ Z.card + d + d := by
          refine (Finset.card_union_le _ _).trans (Nat.add_le_add ((Finset.card_union_le _ _).trans
            (Nat.add_le_add_left ((card_nbrIn_le B u).trans (hdeg u)) _))
            ((card_nbrIn_le B v).trans (hdeg v)))
        have : ((Z ∪ nbrIn B u ∪ nbrIn B v).card : ℝ) ≤ Z.card + d + d := by exact_mod_cast h1
        linarith
      obtain ⟨w, hTw, hwX⟩ := exists_fresh_apex hH3 hTa _ hX
      obtain ⟨huv, huw, hvw⟩ := distinct_of_card_three hTw.1
      simp only [Finset.mem_union, not_or, nbrIn, Finset.mem_filter, Finset.mem_univ,
        true_and] at hwX
      obtain ⟨⟨hwZ, hBu⟩, hBv⟩ := hwX
      have huZ := hBZ _ heB u (by simp)
      have hvZ := hBZ _ heB v (by simp)
      refine ⟨{u, v, w}, tri_mem_allowed hTw, (tri_mem_triEdges huv huw hvw).1, ?_⟩
      intro e' he' hne
      rcases mem_triEdges_tri he' with rfl | rfl | rfl
      · exact absurd rfl hne
      · refine ⟨hBu, fun y hy => ?_⟩
        rcases Sym2.mem_iff.1 hy with rfl | rfl
        · exact huZ
        · exact hwZ
      · refine ⟨hBv, fun y hy => ?_⟩
        rcases Sym2.mem_iff.1 hy with rfl | rfl
        · exact hvZ
        · exact hwZ)
    (by
      intro e he T hT heT hG e' he' he'T
      by_contra hne
      exact (hG e' he'T hne).1 (Finset.mem_filter.1 he').1)

/-- Evento 4: aristas exteriores fuera de `B` con triángulo. -/
def S4 (H : Host V I) (F : Set (Multiset I)) (W Z : Finset V) (B : Finset (Sym2 V)) :
    Finset (Sym2 V) :=
  univ.filter (fun e => HasTri H F e ∧ e ∉ B ∧ ∀ y ∈ e, y ∉ W ∧ y ∉ Z)

def Good4 (W Z : Finset V) (e : Sym2 V) (T : Finset V) : Prop :=
  (∀ y ∈ T, y ∉ Z) ∧ ∀ e' ∈ triEdges T, e' ≠ e → ∃ y ∈ e', y ∈ W

/-- Pivotes del evento 4 (desde la definición de `B`). -/
def piv4 {s d : ℕ} (smp : SampleOut H F s d) : PivotSys H F (S4 H F smp.W smp.Z smp.B) :=
  mkPivotSys (S4 H F smp.W smp.Z smp.B) (Good4 smp.W smp.Z)
    (by
      intro e he
      obtain ⟨-, hT, heB, hout⟩ := Finset.mem_filter.1 he
      obtain ⟨u, v, t, rfl, htW, hTa⟩ := smp.B_full _ hT hout heB
      obtain ⟨huv, hut, hvt⟩ := distinct_of_card_three hTa.1
      refine ⟨{u, v, t}, tri_mem_allowed hTa, (tri_mem_triEdges huv hut hvt).1, ?_, ?_⟩
      · intro y hy
        simp only [Finset.mem_insert, Finset.mem_singleton] at hy
        rcases hy with rfl | rfl | rfl
        · exact (hout y (by simp)).2
        · exact (hout y (by simp)).2
        · exact Finset.disjoint_left.1 smp.disj htW
      · intro e' he' hne
        rcases mem_triEdges_tri he' with rfl | rfl | rfl
        · exact absurd rfl hne
        · exact ⟨t, by simp, htW⟩
        · exact ⟨t, by simp, htW⟩)
    (by
      intro e he T hT heT hG e' he' he'T
      by_contra hne
      obtain ⟨y, hy, hyW⟩ := hG.2 e' he'T hne
      exact ((Finset.mem_filter.1 he').2.2.2 y hy).1 hyW)

lemma piv3_good {α : ℝ} (hH3 : CommonNbrCond H F α) (Z : Finset V) (B : Finset (Sym2 V))
    {d : ℕ} (hBZ : ∀ e ∈ B, ∀ y ∈ e, y ∉ Z) (hdeg : ∀ x, degIn B x ≤ d)
    (hZ : (Z.card : ℝ) + 2 * d < α * Fintype.card V) {e : Sym2 V} (he : e ∈ S3 H F B) :
    Good3 Z B e ((piv3 hH3 Z B hBZ hdeg hZ).piv e) := by
  unfold piv3; exact mkPivotSys_good _ _ _ _ he

lemma piv4_good {s d : ℕ} (smp : SampleOut H F s d) {e : Sym2 V}
    (he : e ∈ S4 H F smp.W smp.Z smp.B) : Good4 smp.W smp.Z e ((piv4 smp).piv e) := by
  unfold piv4; exact mkPivotSys_good _ _ _ _ he

end TypedTriangle
