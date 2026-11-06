/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import RequestProject.TypedTriangle.SampleCount

@[expose] public section

/-!
# G1-Z, §2 de la guía V6 — Conexión y recorridos impares desde la igualdad de imágenes

* `reach_of_mem_incLattice`: si `δ_a − ε δ_b` (`ε ∈ ℤ` arbitrario) está en la imagen entera de `G`,
  entonces `a` y `b` están conectados en `G` (la suma sobre la componente de `a` sería impar).
* `oddAt_of_two_dlt_mem`: si `2δ_a` está en la imagen entera de `G`, hay un recorrido cerrado
  impar en `a` (si no, el signo alternado de la componente de `a` daría `±2 ≠ 0`).
* `delG`: grafo con los vértices de `Z` y las aristas de `B` borrados.
* `link_reach_robust`, `link_oddAt_robust`: con H3, H4 y las ventanas de `link_image_robust`,
  la conexión y los recorridos impares del enlace de `z` sobreviven al borrado de `Z` y `B`.
-/

open Finset

noncomputable section
open Classical

namespace TypedTriangle

namespace Incidence

variable {V : Type*} [Fintype V]

/-- La componente de `a` como conjunto cerrado. -/
lemma reach_closed (G : SimpleGraph V) (a : V) :
    ∀ u v, G.Adj u v → (u ∈ univ.filter (G.Reachable a) ↔ v ∈ univ.filter (G.Reachable a)) := by
  intro u v huv
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  exact ⟨fun h => h.trans huv.reachable, fun h => h.trans huv.reachable.symm⟩

/-- **Conexión desde la imagen entera.** -/
theorem reach_of_mem_incLattice {G : SimpleGraph V} {a b : V} {ε : ℤ}
    (h : dlt a - ε • dlt b ∈ incLattice G) : G.Reachable a b := by
  by_contra hab
  have hev := (incLattice_necessary h).2 _ (reach_closed G a)
  have hne : a ≠ b := fun e => hab (e ▸ SimpleGraph.Reachable.refl a)
  have hsum : ∑ v ∈ univ.filter (G.Reachable a), (dlt a - ε • dlt b) v = 1 := by
    simp only [Pi.sub_apply]
    rw [Finset.sum_sub_distrib]
    have h1 : ∑ v ∈ univ.filter (G.Reachable a), dlt a v = 1 := by
      rw [Finset.sum_eq_single a]
      · simp
      · intro v _ hv; simp [dlt, hv]
      · intro ha; exact absurd (by simp) ha
    have h2 : ∑ v ∈ univ.filter (G.Reachable a), (ε • dlt b) v = 0 := by
      refine Finset.sum_eq_zero fun v hv => ?_
      have hvb : v ≠ b := by
        rintro rfl; exact hab (Finset.mem_filter.1 hv).2
      simp [dlt, hvb]
    rw [h1, h2]; ring
  rw [hsum] at hev
  exact (Int.not_even_one) hev

/-- **Recorrido impar desde la imagen entera.** -/
theorem oddAt_of_two_dlt_mem {G : SimpleGraph V} {a : V} (h : (2 : ℤ) • dlt a ∈ incLattice G) :
    OddAt G a := by
  by_contra hno
  have hno' : ∀ p : G.Walk a a, ¬ Odd p.length := fun p hp => hno ⟨p, hp⟩
  set σ : V → ℤ := fun u => if hu : G.Reachable u a then (-1) ^ hu.some.length else 0
  have hval : ∀ u (p : G.Walk u a), σ u = (-1) ^ p.length := by
    intro u p
    have hu : G.Reachable u a := ⟨p⟩
    simp only [σ, dif_pos hu]
    exact parity_unique hno' _ _
  have hadm : ∀ u v, G.Adj u v → σ u + σ v = 0 := by
    intro u v huv
    by_cases hv : G.Reachable v a
    · obtain ⟨p⟩ := hv
      rw [hval u (SimpleGraph.Walk.cons huv p), hval v p, SimpleGraph.Walk.length_cons, pow_succ]
      ring
    · have hu : ¬ G.Reachable u a := fun hu => hv (huv.reachable.symm.trans hu)
      simp [σ, hu, hv]
  have h0 := (incLattice_necessary h).1 σ hadm
  have hσa : σ a = 1 := by
    rw [hval a SimpleGraph.Walk.nil]; simp
  have : ∑ v, σ v * ((2 : ℤ) • dlt a) v = 2 * σ a := by
    rw [Finset.sum_eq_single a]
    · simp [dlt]; ring
    · intro v _ hv; simp [dlt, hv]
    · intro ha; exact absurd (Finset.mem_univ a) ha
  rw [this, hσa] at h0
  norm_num at h0

end Incidence

open Incidence

variable {Ω : Type*}

/-- Grafo con los vértices de `Z` y las aristas de `B` borrados. -/
def delG (J : SimpleGraph Ω) (Z : Finset Ω) (B : Finset (Sym2 Ω)) : SimpleGraph Ω where
  Adj x y := J.Adj x y ∧ x ∉ Z ∧ y ∉ Z ∧ s(x, y) ∉ B
  symm := ⟨fun x y h => ⟨h.1.symm, h.2.2.1, h.2.1, by rw [Sym2.eq_swap]; exact h.2.2.2⟩⟩
  loopless := ⟨fun _ h => J.loopless.irrefl _ h.1⟩

lemma delG_le (J : SimpleGraph Ω) (Z : Finset Ω) (B : Finset (Sym2 Ω)) : delG J Z B ≤ J :=
  fun _ _ h => h.1

variable {V I : Type*} [Fintype V]

/-- El enlace restringido a aristas buenas es el enlace con `Z` y `B` borrados. -/
lemma linkOn_goodEdges_eq (H : Host V I) (F : Set (Multiset I)) (z : V) (Z : Finset V)
    (B : Finset (Sym2 V)) :
    linkOn H F z (goodEdges H Z B) = delG (linkGraph H F z) Z B := by
  ext u w
  simp only [linkOn, delG, goodEdges, avoidSet, Finset.mem_filter]
  constructor
  · rintro ⟨h, ⟨-, hZ⟩, hB⟩
    exact ⟨h, fun hu => hZ u hu (by simp), fun hw => hZ w hw (by simp), hB⟩
  · rintro ⟨h, hu, hw, hB⟩
    refine ⟨h, ⟨?_, fun y hy hye => ?_⟩, hB⟩
    · have := h.2.2.1 u (by simp) w (by simp) h.1
      simp [edges, this]
    · rcases Sym2.mem_iff.1 hye with rfl | rfl
      · exact hu hy
      · exact hw hy

/-- **Conexión robusta del enlace.** -/
theorem link_reach_robust {H : Host V I} {F : Set (Multiset I)} {α : ℝ} {h : ℕ}
    (hα : 0 < α) (hH3 : CommonNbrCond H F α) (hH4 : HingeCond H F α h) {z : V}
    (Z : Finset V) (hz : z ∉ Z) (B : Finset (Sym2 V)) (d : ℕ) (hdeg : ∀ x, degIn B x ≤ d)
    (hwin1 : (Z.card : ℝ) + 2 + 4 * d < α * Fintype.card V)
    (hwin2 : ((Z.card : ℝ) + h + 5 * d) * 2 ^ Nat.choose h 2 ≤ α / 2 * Fintype.card V)
    {a b : V} (ha : a ∉ Z) (hb : b ∉ Z) (hab : (linkGraph H F z).Reachable a b) :
    (delG (linkGraph H F z) Z B).Reachable a b := by
  obtain ⟨p⟩ := hab
  have hm := walk_mem p
  have hx : ∀ y ∈ Z, (dlt a - ((-1 : ℤ) ^ p.length) • dlt b) y = 0 := by
    intro y hy
    have hya : y ≠ a := fun e => ha (e ▸ hy)
    have hyb : y ≠ b := fun e => hb (e ▸ hy)
    simp [dlt, hya, hyb]
  rw [link_image_robust hα hH3 hH4 Z hz B d hdeg hwin1 hwin2 hx, linkOn_goodEdges_eq] at hm
  exact reach_of_mem_incLattice hm

/-- **Recorridos impares robustos del enlace.** -/
theorem link_oddAt_robust {H : Host V I} {F : Set (Multiset I)} {α : ℝ} {h : ℕ}
    (hα : 0 < α) (hH3 : CommonNbrCond H F α) (hH4 : HingeCond H F α h) {z : V}
    (Z : Finset V) (hz : z ∉ Z) (B : Finset (Sym2 V)) (d : ℕ) (hdeg : ∀ x, degIn B x ≤ d)
    (hwin1 : (Z.card : ℝ) + 2 + 4 * d < α * Fintype.card V)
    (hwin2 : ((Z.card : ℝ) + h + 5 * d) * 2 ^ Nat.choose h 2 ≤ α / 2 * Fintype.card V)
    {a : V} (ha : a ∉ Z) (hodd : OddAt (linkGraph H F z) a) :
    OddAt (delG (linkGraph H F z) Z B) a := by
  obtain ⟨p, hp⟩ := hodd
  have hm := walk_mem p
  rw [hp.neg_one_pow, neg_one_smul, sub_neg_eq_add, ← two_smul ℤ] at hm
  have hx : ∀ y ∈ Z, ((2 : ℤ) • dlt a) y = 0 := by
    intro y hy
    have hya : y ≠ a := fun e => ha (e ▸ hy)
    simp [dlt, hya]
  rw [link_image_robust hα hH3 hH4 Z hz B d hdeg hwin1 hwin2 hx, linkOn_goodEdges_eq] at hm
  exact oddAt_of_two_dlt_mem hm

end TypedTriangle
