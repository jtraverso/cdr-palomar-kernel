/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import RequestProject.TypedTriangle.SampleParams

@[expose] public section

/-!
# G1-Z, §5 de la guía V6 — Raíces buenas desde los sucesos buenos por componente

Muestra firmada: un par `y = (x, s)` de una muestra base `x` (valores en `V`) y una muestra de
signos `s` (valores en `Bool`) con la misma forma. La muestra de la doble cubierta es
`zipS x s` (pares `(valor, signo)`), y `W = baseW x` son los valores BASE. No se añaden puntos
base al inducido: el marcado de la cubierta es la copia opuesta de un punto del prefijo, cuya
base ya está en `W`.

* `BadRoot H F v y`: alguna componente activa `K` del enlace de `v` falla el suceso bueno de
  la base, o es no bipartita y su doble cubierta falla el suceso bueno con el marcado.
* `goodRoot_of_not_badRoot`: si `v` no es mala, `GoodRoot H F (baseW x) v` (conexión y
  recorridos impares conservados en el inducido sobre `W`).
-/

open Finset

noncomputable section
open Classical

namespace TypedTriangle

open Incidence Sampler

/-- Forma de las muestras: prefijo de `L` bloques de `Q` valores y bloque final de `b`. -/
abbrev XS (L Q b : ℕ) (T : Type*) := (Fin L → Fin Q → T) × (Fin b → T)

/-- Muestra de pares. -/
def zipS {L Q b : ℕ} {T U : Type*} (x : XS L Q b T) (s : XS L Q b U) : XS L Q b (T × U) :=
  (fun j i => (x.1 j i, s.1 j i), fun i => (x.2 i, s.2 i))

/-- `zipS` es una biyección. -/
def zipE (L Q b : ℕ) (T U : Type*) : XS L Q b T × XS L Q b U ≃ XS L Q b (T × U) where
  toFun y := zipS y.1 y.2
  invFun z := ((fun j i => (z.1 j i).1, fun i => (z.2 i).1),
    (fun j i => (z.1 j i).2, fun i => (z.2 i).2))
  left_inv _ := rfl
  right_inv _ := rfl

/-- Valores de una muestra. -/
def baseW {L Q b : ℕ} {T : Type*} [Fintype T] [DecidableEq T] (x : XS L Q b T) : Finset T := pvals x.1 ∪ fvals x.2

lemma image_fst_baseW_zip {L Q b : ℕ} {T U : Type*} [Fintype T] [Fintype U] [DecidableEq T]
    [DecidableEq U] (x : XS L Q b T) (s : XS L Q b U) :
    (baseW (zipS x s)).image Prod.fst = baseW x := by
  ext t
  simp only [baseW, zipS, pvals, fvals, Finset.mem_image, Finset.mem_union, Finset.mem_univ,
    true_and, Prod.exists]
  constructor
  · rintro ⟨a, b', h, rfl⟩
    rcases h with ⟨j, i, h⟩ | ⟨i, h⟩
    · left; exact ⟨j, i, congrArg Prod.fst h⟩
    · right; exact ⟨i, congrArg Prod.fst h⟩
  · rintro (⟨j, i, rfl⟩ | ⟨i, rfl⟩)
    · exact ⟨x.1 j i, s.1 j i, Or.inl ⟨j, i, rfl⟩, rfl⟩
    · exact ⟨x.2 i, s.2 i, Or.inr ⟨i, rfl⟩, rfl⟩

lemma card_baseW_le {L Q b : ℕ} {T : Type*} [Fintype T] (x : XS L Q b T) : (baseW x).card ≤ L * Q + b := by
  refine (Finset.card_union_le _ _).trans (Nat.add_le_add (card_pvals_le x.1) ?_)
  exact Finset.card_image_le.trans (by simp)

/-- Copia opuesta. -/
def flipB {T : Type*} (z : T × Bool) : T × Bool := (z.1, !z.2)

/-- Marcado de la cubierta: la copia opuesta de un punto del prefijo en `Kt`. -/
def markC {L Q : ℕ} {T : Type*} [Fintype T] (Kt : Finset (T × Bool)) (p : Fin L → Fin Q → T × Bool) :
    Finset (T × Bool) :=
  if h : ∃ z ∈ pvals p, z ∈ Kt then {flipB h.choose} else ∅

lemma card_markC_le {L Q : ℕ} {T : Type*} [Fintype T] (Kt : Finset (T × Bool))
    (p : Fin L → Fin Q → T × Bool) : (markC Kt p).card ≤ 1 := by
  unfold markC; split_ifs <;> simp

variable {V I : Type*} [Fintype V]

/-- Componentes activas del enlace de `v`. -/
def comps (H : Host V I) (F : Set (Multiset I)) (v : V) : Finset (Finset V) :=
  (univ.filter (Active (linkGraph H F v))).image (compOf (linkGraph H F v))

/-- Raíz mala para la muestra firmada `y`. -/
def BadRoot {L Q b : ℕ} (H : Host V I) (F : Set (Multiset I)) (v : V)
    (y : XS L Q b V × XS L Q b Bool) : Prop :=
  ∃ K ∈ comps H F v,
    ¬ SampleGood (linkGraph H F v) K ∅ (pvals y.1.1) (baseW y.1) ∨
    ((∀ a ∈ K, OddAt (linkGraph H F v) a) ∧
      ¬ SampleGood (dcover (linkGraph H F v)) (K ×ˢ (univ : Finset Bool))
        (markC (K ×ˢ (univ : Finset Bool)) (zipS y.1 y.2).1) (pvals (zipS y.1 y.2).1)
        (baseW (zipS y.1 y.2)))

lemma odd_of_bodd {n : ℕ} (h : Nat.bodd n = true) : Odd n := by
  have := Nat.bodd_add_div2 n
  rw [h] at this
  exact ⟨Nat.div2 n, by simp at this; omega⟩

omit [Fintype V] in
lemma active_of_reach_ne {G : SimpleGraph V} {a b : V} (h : G.Reachable a b) (hab : a ≠ b) :
    Active G a := by
  obtain ⟨p⟩ := h
  cases p with
  | nil => exact absurd rfl hab
  | cons h' _ => exact ⟨_, h'⟩

omit [Fintype V] in
lemma active_of_oddAt {G : SimpleGraph V} {a : V} (h : OddAt G a) : Active G a := by
  obtain ⟨p, hp⟩ := h
  cases p with
  | nil => simp at hp
  | cons h' _ => exact ⟨_, h'⟩

set_option backward.isDefEq.respectTransparency.types false in
/-- **Raíces buenas desde los sucesos buenos.** -/
theorem goodRoot_of_not_badRoot {L Q b : ℕ} (H : Host V I) (F : Set (Multiset I)) (v : V)
    (y : XS L Q b V × XS L Q b Bool) (hy : ¬ BadRoot H F v y) :
    GoodRoot H F (baseW y.1) v := by
  set G := linkGraph H F v
  set W := baseW y.1
  simp only [BadRoot, not_exists, not_and, not_or, not_not] at hy
  -- conexión en cada componente activa
  have hconn : ∀ a ∈ W, Active G a → ∀ b ∈ W, G.Reachable a b → (inducedOn G W).Reachable a b := by
    intro a ha hact b hb hab
    have hK : compOf G a ∈ comps H F v :=
      Finset.mem_image.2 ⟨a, Finset.mem_filter.2 ⟨Finset.mem_univ _, hact⟩, rfl⟩
    have hg := (hy _ hK).1
    have := hg.2 a (by simp [W, ha]) (mem_compOf.2 (SimpleGraph.Reachable.refl a))
      b (by simp [W, hb]) (mem_compOf.2 hab)
    simpa using this
  refine ⟨fun a ha b hb hab => ?_, fun a ha hodd => ?_⟩
  · by_cases hab' : a = b
    · subst hab'; exact SimpleGraph.Reachable.refl _
    · exact hconn a ha (active_of_reach_ne hab hab') b hb hab
  · have hact := active_of_oddAt hodd
    set K := compOf G a
    have hK : K ∈ comps H F v :=
      Finset.mem_image.2 ⟨a, Finset.mem_filter.2 ⟨Finset.mem_univ _, hact⟩, rfl⟩
    have hnb : ∀ x ∈ K, OddAt G x := fun x hx => oddAt_of_reach (mem_compOf.1 hx).symm hodd
    have hcov := (hy K hK).2 hnb
    set Kt := K ×ˢ (univ : Finset Bool)
    set pt := (zipS y.1 y.2).1
    obtain ⟨⟨r, hrp, hrK⟩, hreach⟩ := hcov
    have hex : ∃ z ∈ pvals pt, z ∈ Kt := ⟨r, hrp, hrK⟩
    set r' := hex.choose
    have hr'p : r' ∈ pvals pt := hex.choose_spec.1
    have hr'K : r' ∈ Kt := hex.choose_spec.2
    have hmark : markC Kt pt = {flipB r'} := by simp only [markC, dif_pos hex]; rfl
    have hfK : flipB r' ∈ Kt :=
      Finset.mem_product.2 ⟨(Finset.mem_product.1 hr'K).1, Finset.mem_univ _⟩
    have hrW : r'.1 ∈ W := by
      simp only [W]
      rw [← image_fst_baseW_zip y.1 y.2]
      exact Finset.mem_image_of_mem _ (Finset.mem_union_left _ hr'p)
    obtain ⟨wlk⟩ := hreach r' (Finset.mem_union_left _ (Finset.mem_union_left _ hr'p)) hr'K
      (flipB r') (Finset.mem_union_right _ (by rw [hmark]; simp)) hfK
    -- paridad impar
    have hodd' : Odd wlk.length := by
      have hpar : (!r'.2) = (r'.2 ^^ Nat.bodd wlk.length) := by
        simpa only [SimpleGraph.Walk.length_map, SimpleGraph.Hom.ofLE_apply, flipB] using
          dcover_walk_parity (wlk.map (SimpleGraph.Hom.ofLE (inducedOn_le _ _)))
      cases hb' : Nat.bodd wlk.length
      · simp [hb'] at hpar
      · exact odd_of_bodd hb'
    -- proyección al inducido sobre `W`
    obtain ⟨wq, hwq⟩ := dcover_induced_proj _ wlk
    have hsub : (baseW (zipS y.1 y.2) ∪ markC Kt pt).image Prod.fst ⊆ W := by
      intro t ht
      obtain ⟨z, hz, rfl⟩ := Finset.mem_image.1 ht
      rcases Finset.mem_union.1 hz with hz | hz
      · simp only [W]; rw [← image_fst_baseW_zip y.1 y.2]; exact Finset.mem_image_of_mem _ hz
      · rw [hmark, Finset.mem_singleton] at hz
        subst hz
        exact hrW
    have hoddr : OddAt (inducedOn G W) r'.1 := by
      refine ⟨(wq.map (SimpleGraph.Hom.ofLE (inducedOn_mono G hsub))).copy rfl rfl, ?_⟩
      simpa only [SimpleGraph.Walk.length_copy, SimpleGraph.Walk.length_map, hwq] using hodd'
    -- `a` y `r'.1` están en la misma componente
    have hrKa : r'.1 ∈ K := (Finset.mem_product.1 hr'K).1
    have har := hconn a ha hact r'.1 hrW (mem_compOf.1 hrKa)
    exact oddAt_of_reach har hoddr

end TypedTriangle
