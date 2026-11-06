/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import RequestProject.S07V26.ForkSingle
public import RequestProject.TypedTriangle.SparseEdgeLattice

@[expose] public section

/-!
# V26 — degree accounting for forks

* `degIn` of unions/insertions, the handshake `∑ₓ degIn X x = 2|X|` for loopless `X`.
* `Fork.Valid.degIn_root`: a root `x ∉ W` gets fork degree `≤ 2·[x ∈ uv]`.
* `Fork.Valid.degIn_aux`: an auxiliary `x ∈ W` gets fork degree `≤ 4·[x=w] + 2·[x=a] + 2·[x=b]`.
* `Fork.Valid.sum_degIn_W`: in total the fork costs at most EIGHT auxiliary incidences in `W`.
-/

open Finset

noncomputable section
open Classical

namespace S07V26

open TypedTriangle.SparseEdge TypedTriangle.ComponentRows S07V25

variable {V I : Type*}

lemma degIn_union_le (A B : Finset (Sym2 V)) (x : V) :
    degIn (A ∪ B) x ≤ degIn A x + degIn B x := by
  unfold degIn; rw [filter_union]; exact card_union_le _ _

lemma degIn_mono {A B : Finset (Sym2 V)} (h : A ⊆ B) (x : V) : degIn A x ≤ degIn B x :=
  card_le_card (filter_subset_filter _ h)

lemma degIn_insert_le (e : Sym2 V) (A : Finset (Sym2 V)) (x : V) :
    degIn (insert e A) x ≤ degIn A x + 1 := by
  unfold degIn; rw [filter_insert]
  split_ifs
  · exact card_insert_le _ _
  · omega

lemma degIn_insert_of_notMem {e : Sym2 V} {A : Finset (Sym2 V)} (he : e ∉ A) (x : V) :
    degIn (insert e A) x = degIn {e} x + degIn A x := by
  unfold degIn
  rw [insert_eq, filter_union, card_union_of_disjoint]
  exact disjoint_filter_filter (disjoint_singleton_left.2 he)

lemma degIn_singleton (e : Sym2 V) (x : V) : degIn {e} x = if x ∈ e then 1 else 0 := by
  unfold degIn; rw [filter_singleton]; split_ifs <;> simp

lemma degIn_le_of_forall {S T : Finset (Sym2 V)} {x : V} (h : ∀ e ∈ S, x ∈ e → e ∈ T) :
    degIn S x ≤ T.card :=
  card_le_card (fun e he => h e (mem_filter.1 he).1 (mem_filter.1 he).2)

variable [Fintype V] {G : SimpleGraph V} {lab : V → I} {F : Set (Multiset I)} {W : Finset V}

/-- handshake for loopless edge sets -/
lemma sum_degIn_eq {X : Finset (Sym2 V)} (hX : ∀ e ∈ X, ¬ e.IsDiag) :
    ∑ x, degIn X x = 2 * X.card := by
  unfold degIn
  simp_rw [card_filter]
  rw [sum_comm, card_eq_sum_ones, mul_sum, mul_one]
  refine sum_congr rfl fun e he => ?_
  induction e using Sym2.ind with
  | _ a b =>
    have hab : a ≠ b := fun h => hX _ he (by simp [h])
    rw [← card_filter]
    have : (univ.filter fun x => x ∈ s(a, b)) = {a, b} := by ext; simp
    rw [this, card_pair hab]

/-- `2|X| ≤ n·r` when every degree is at most `r` -/
lemma two_card_le {X : Finset (Sym2 V)} (hX : ∀ e ∈ X, ¬ e.IsDiag) {r : ℕ}
    (hr : ∀ x, degIn X x ≤ r) : 2 * X.card ≤ Fintype.card V * r := by
  rw [← sum_degIn_eq hX]
  calc ∑ x, degIn X x ≤ ∑ _x : V, r := sum_le_sum fun x _ => hr x
    _ = Fintype.card V * r := by simp

/-- **root degree**: a vertex outside `W` gets at most `2` fork edges, only if it is a root -/
lemma Fork.Valid.degIn_root {f : Fork V} (hf : f.Valid G lab F W) {x : V} (hx : x ∉ W) :
    degIn f.E x ≤ 2 * degIn {f.root} x := by
  obtain ⟨huv, huw, hua, hub, hvw, hva, hvb, hwa, hwb, hab⟩ := hf.distinct
  obtain ⟨hu, hv, hw, ha, hb, -⟩ := hf
  have hxw : x ≠ f.w := fun h => hx (h ▸ hw)
  have hxa : x ≠ f.a := fun h => hx (h ▸ ha)
  have hxb : x ≠ f.b := fun h => hx (h ▸ hb)
  rw [degIn_singleton]
  by_cases hxu : x = f.u
  · have : degIn f.E x ≤ ({s(f.u, f.w), s(f.u, f.a)} : Finset (Sym2 V)).card := by
      refine degIn_le_of_forall fun e he hxe => ?_
      rw [Fork.mem_E] at he
      rcases he with rfl | rfl | rfl | rfl | rfl | rfl <;> simp_all
    have h2 := card_le_two (a := s(f.u, f.w)) (b := s(f.u, f.a))
    rw [if_pos (by simp [Fork.root, hxu])]; omega
  by_cases hxv : x = f.v
  · have : degIn f.E x ≤ ({s(f.v, f.w), s(f.b, f.v)} : Finset (Sym2 V)).card := by
      refine degIn_le_of_forall fun e he hxe => ?_
      rw [Fork.mem_E] at he
      rcases he with rfl | rfl | rfl | rfl | rfl | rfl <;> simp_all
    have h2 := card_le_two (a := s(f.v, f.w)) (b := s(f.b, f.v))
    rw [if_pos (by simp [Fork.root, hxv])]; omega
  · have : degIn f.E x ≤ (∅ : Finset (Sym2 V)).card := by
      refine degIn_le_of_forall fun e he hxe => ?_
      rw [Fork.mem_E] at he
      rcases he with rfl | rfl | rfl | rfl | rfl | rfl <;> simp_all
    simp at this; omega

/-- **auxiliary degree**: `≤ 4` at `w`, `≤ 2` at `a` and at `b`, and `0` at every other vertex
of `W` -/
lemma Fork.Valid.degIn_aux {f : Fork V} (hf : f.Valid G lab F W) {x : V} (hx : x ∈ W) :
    degIn f.E x ≤ (if x = f.w then 4 else 0) + (if x = f.a then 2 else 0) +
      (if x = f.b then 2 else 0) := by
  obtain ⟨huv, huw, hua, hub, hvw, hva, hvb, hwa, hwb, hab⟩ := hf.distinct
  obtain ⟨hu, hv, hw, ha, hb, -⟩ := hf
  have hxu : x ≠ f.u := fun h => hu (h ▸ hx)
  have hxv : x ≠ f.v := fun h => hv (h ▸ hx)
  by_cases hxw : x = f.w
  · have : degIn f.E x ≤
        ({s(f.u, f.w), s(f.v, f.w), s(f.a, f.w), s(f.w, f.b)} : Finset (Sym2 V)).card := by
      refine degIn_le_of_forall fun e he hxe => ?_
      rw [Fork.mem_E] at he
      rcases he with rfl | rfl | rfl | rfl | rfl | rfl <;> simp_all
    have h4 := card_le_four (a := s(f.u, f.w)) (b := s(f.v, f.w)) (c := s(f.a, f.w))
      (d := s(f.w, f.b))
    rw [if_pos hxw, if_neg (by rw [hxw]; exact hwa), if_neg (by rw [hxw]; exact hwb)]; omega
  by_cases hxa : x = f.a
  · have : degIn f.E x ≤ ({s(f.u, f.a), s(f.a, f.w)} : Finset (Sym2 V)).card := by
      refine degIn_le_of_forall fun e he hxe => ?_
      rw [Fork.mem_E] at he
      rcases he with rfl | rfl | rfl | rfl | rfl | rfl <;> simp_all
    have h2 := card_le_two (a := s(f.u, f.a)) (b := s(f.a, f.w))
    rw [if_neg hxw, if_pos hxa, if_neg (by rw [hxa]; exact hab)]; omega
  by_cases hxb : x = f.b
  · have : degIn f.E x ≤ ({s(f.w, f.b), s(f.b, f.v)} : Finset (Sym2 V)).card := by
      refine degIn_le_of_forall fun e he hxe => ?_
      rw [Fork.mem_E] at he
      rcases he with rfl | rfl | rfl | rfl | rfl | rfl <;> simp_all
    have h2 := card_le_two (a := s(f.w, f.b)) (b := s(f.b, f.v))
    rw [if_neg hxw, if_neg hxa, if_pos hxb]; omega
  · have : degIn f.E x ≤ (∅ : Finset (Sym2 V)).card := by
      refine degIn_le_of_forall fun e he hxe => ?_
      rw [Fork.mem_E] at he
      rcases he with rfl | rfl | rfl | rfl | rfl | rfl <;> simp_all
    simp at this; omega

/-- **eight auxiliary incidences**: a fork costs at most `8` incidences inside `W` -/
lemma Fork.Valid.sum_degIn_W {f : Fork V} (hf : f.Valid G lab F W) :
    ∑ x ∈ W, degIn f.E x ≤ 8 := by
  calc ∑ x ∈ W, degIn f.E x
      ≤ ∑ x ∈ W, ((if x = f.w then 4 else 0) + (if x = f.a then 2 else 0) +
          (if x = f.b then 2 else 0)) := sum_le_sum fun x hx => hf.degIn_aux hx
    _ ≤ 8 := by
      rw [sum_add_distrib, sum_add_distrib, sum_ite_eq', sum_ite_eq', sum_ite_eq']
      split_ifs <;> omega

end S07V26

end
