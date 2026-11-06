/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import RequestProject.TypedTriangle.Absorb
public import PartitionedTriangleAbsorption.RootedAvoidanceCountsStage51

@[expose] public section

/-!
# Oferta de bisagras frescas (cuentas de S05 §2–§3, S02), reutilizando Paper II

Se conecta la noción de soporte de `TypedTriangle` con la de
`PartitionedTriangleAbsorption.PhysicalHinge` (corte de Paper II adaptado a 4.28) y se
reutilizan sus cotas de conteo de conjuntos de aristas enraizados:

* `support_eq_physicalHinge_support`: ambos soportes coinciden;
* `hinges_card_le`: `|𝓗_i(T_a,T_b)| ≤ C(n−4, i−4) · 2^{C(i+1,2)}`;
* `hinges_through_le`: las bisagras de orden `i` cuyo soporte contiene un vértice fijo
  `z` fuera de las raíces son a lo sumo `C(n−5, i−5) · 2^{C(i+1,2)} ≤ n^{i−5} 2^{C(i+1,2)}`;
* `fresh_hinges`: si (H4) da `|𝓗_i| ≥ α n^{i−4}` y un historial `Z` cumple
  `|Z| n^{i−5} 2^{C(i+1,2)} ≤ (α/2) n^{i−4}`, entonces al menos `(α/2) n^{i−4}` bisagras de
  orden `i` evitan `Z` fuera de sus raíces. Es la cuenta «las que tocan el historial fuera
  de las raíces son a lo sumo `R 2^M n^{i−5}`» de S05 §2.
-/

open Finset

noncomputable section
open Classical

namespace TypedTriangle

variable {V I : Type*} [Fintype V]

lemma support_eq_physicalHinge_support (J : Finset (Sym2 V)) :
    support J = PartitionedTriangleAbsorption.PhysicalHinge.support J := by
  ext x
  simp [support, PartitionedTriangleAbsorption.PhysicalHinge.support, Finset.mem_biUnion,
    Sym2.mem_toFinset]

omit [Fintype V] in
lemma roots_card {u v a b : V} (huv : u ≠ v) (hua : u ≠ a) (hva : v ≠ a) (hub : u ≠ b)
    (hvb : v ≠ b) (hab : a ≠ b) : ({u, v, a, b} : Finset V).card = 4 := by
  rw [Finset.card_insert_of_notMem (by simp [huv, hua, hub]),
    Finset.card_insert_of_notMem (by simp [hva, hvb]),
    Finset.card_insert_of_notMem (by simp [hab]), Finset.card_singleton]

/-- Cota superior universal del número de bisagras de orden `i`. -/
theorem hinges_card_le {H : Host V I} {F : Set (Multiset I)} {u v a b : V} (hab : a ≠ b)
    (hTa : IsAllowed H F {u, v, a}) (hTb : IsAllowed H F {u, v, b}) (i : ℕ) (hi : 4 ≤ i) :
    (hinges H F u v a b i).card ≤
      Nat.choose (Fintype.card V - 4) (i - 4) * 2 ^ Nat.choose (i + 1) 2 := by
  obtain ⟨huv, hua, hva⟩ := distinct_of_card_three hTa.1
  obtain ⟨-, hub, hvb⟩ := distinct_of_card_three hTb.1
  have hR := roots_card huv hua hva hub hvb hab
  have := PartitionedTriangleAbsorption.PhysicalHinge.rooted_edge_sets_card_le
    (hinges H F u v a b i) {u, v, a, b} i (by rw [hR]; exact hi)
    (fun J hJ => by
      simp only [hinges, Finset.mem_filter, Finset.mem_univ, true_and] at hJ
      rw [← support_eq_physicalHinge_support]
      exact (hinge_order_ge_six hab hTa hTb hJ.1).1)
    (fun J hJ => by
      simp only [hinges, Finset.mem_filter, Finset.mem_univ, true_and] at hJ
      rw [← support_eq_physicalHinge_support]; exact hJ.2)
  simpa only [hR] using this

/-- Bisagras de orden `i` cuyo soporte contiene un vértice `z` fuera de las raíces. -/
theorem hinges_through_le {H : Host V I} {F : Set (Multiset I)} {u v a b : V} (hab : a ≠ b)
    (hTa : IsAllowed H F {u, v, a}) (hTb : IsAllowed H F {u, v, b}) (i : ℕ) (hi : 5 ≤ i)
    (z : V) (hz : z ∉ ({u, v, a, b} : Finset V)) :
    ((hinges H F u v a b i).filter (fun J => z ∈ support J)).card ≤
      Fintype.card V ^ (i - 5) * 2 ^ Nat.choose (i + 1) 2 := by
  obtain ⟨huv, hua, hva⟩ := distinct_of_card_three hTa.1
  obtain ⟨-, hub, hvb⟩ := distinct_of_card_three hTb.1
  have hR := roots_card huv hua hva hub hvb hab
  have h := PartitionedTriangleAbsorption.RootedAvoidanceCountsStage51.one_extra_vertex
    (hinges H F u v a b i) {u, v, a, b} i z hz (by rw [hR]; omega)
    (fun J hJ => by
      simp only [hinges, Finset.mem_filter, Finset.mem_univ, true_and] at hJ
      rw [← support_eq_physicalHinge_support]
      exact (hinge_order_ge_six hab hTa hTb hJ.1).1)
    (fun J hJ => by
      simp only [hinges, Finset.mem_filter, Finset.mem_univ, true_and] at hJ
      rw [← support_eq_physicalHinge_support]; exact hJ.2)
  rw [hR] at h
  have hfilt : (hinges H F u v a b i).filter (fun J => z ∈ support J) =
      (hinges H F u v a b i).filter
        (fun J => z ∈ PartitionedTriangleAbsorption.PhysicalHinge.support J) := by
    refine Finset.filter_congr fun J _ => ?_
    rw [support_eq_physicalHinge_support]
  rw [hfilt]
  refine h.trans (Nat.mul_le_mul_right _ ?_)
  refine (Nat.choose_le_pow _ _).trans ?_
  have : i - (4 + 1) = i - 5 := rfl
  rw [this]
  exact Nat.pow_le_pow_left (Nat.sub_le _ _) _

/-- **Bisagras frescas (S05 §2).** Si hay al menos `α n^{i−4}` bisagras de orden `i` y el
historial `Z` es pequeño, al menos `(α/2) n^{i−4}` de ellas evitan `Z` fuera de las
raíces. -/
theorem fresh_hinges {H : Host V I} {F : Set (Multiset I)} {u v a b : V} (hab : a ≠ b)
    (hTa : IsAllowed H F {u, v, a}) (hTb : IsAllowed H F {u, v, b}) (i : ℕ) (hi : 5 ≤ i)
    (α : ℝ) (Z : Finset V)
    (hsupply : α * (Fintype.card V : ℝ) ^ (i - 4) ≤ (hinges H F u v a b i).card)
    (hZ : (Z.card : ℝ) * (Fintype.card V : ℝ) ^ (i - 5) * 2 ^ Nat.choose (i + 1) 2 ≤
      α / 2 * (Fintype.card V : ℝ) ^ (i - 4)) :
    α / 2 * (Fintype.card V : ℝ) ^ (i - 4) ≤
      ((hinges H F u v a b i).filter
        (fun J => ∀ z ∈ Z, z ∈ support J → z ∈ ({u, v, a, b} : Finset V))).card := by
  set K := hinges H F u v a b i
  set Zout := Z.filter (fun z => z ∉ ({u, v, a, b} : Finset V))
  have hbad : K.filter (fun J => ¬ ∀ z ∈ Z, z ∈ support J → z ∈ ({u, v, a, b} : Finset V)) ⊆
      Zout.biUnion (fun z => K.filter (fun J => z ∈ support J)) := by
    intro J hJ
    simp only [Finset.mem_filter, not_forall] at hJ
    obtain ⟨hJK, z, hzZ, hzJ, hzR⟩ := hJ
    exact Finset.mem_biUnion.2 ⟨z, Finset.mem_filter.2 ⟨hzZ, hzR⟩,
      Finset.mem_filter.2 ⟨hJK, hzJ⟩⟩
  have hbadcard : ((K.filter (fun J => ¬ ∀ z ∈ Z, z ∈ support J →
      z ∈ ({u, v, a, b} : Finset V))).card : ℝ) ≤
      Z.card * ((Fintype.card V : ℝ) ^ (i - 5) * 2 ^ Nat.choose (i + 1) 2) := by
    have h1 := (Finset.card_le_card hbad).trans Finset.card_biUnion_le
    have h2 : ∑ z ∈ Zout, (K.filter (fun J => z ∈ support J)).card ≤
        ∑ _z ∈ Zout, Fintype.card V ^ (i - 5) * 2 ^ Nat.choose (i + 1) 2 :=
      Finset.sum_le_sum fun z hz =>
        hinges_through_le hab hTa hTb i hi z (Finset.mem_filter.1 hz).2
    rw [Finset.sum_const, smul_eq_mul] at h2
    have h3 : Zout.card ≤ Z.card := Finset.card_filter_le _ _
    have h4 : (K.filter (fun J => ¬ ∀ z ∈ Z, z ∈ support J →
        z ∈ ({u, v, a, b} : Finset V))).card ≤
        Z.card * (Fintype.card V ^ (i - 5) * 2 ^ Nat.choose (i + 1) 2) :=
      (h1.trans h2).trans (Nat.mul_le_mul_right _ h3)
    exact_mod_cast h4
  have hsplit := Finset.card_filter_add_card_filter_not
    (s := K) (fun J => ∀ z ∈ Z, z ∈ support J → z ∈ ({u, v, a, b} : Finset V))
  have hsplit' : ((K.filter (fun J => ∀ z ∈ Z, z ∈ support J →
      z ∈ ({u, v, a, b} : Finset V))).card : ℝ) +
      (K.filter (fun J => ¬ ∀ z ∈ Z, z ∈ support J →
        z ∈ ({u, v, a, b} : Finset V))).card = K.card := by exact_mod_cast hsplit
  nlinarith

/-- **Bisagra fresca a partir de (H4).** Si se cumple (H4) con constantes `α > 0`, `h`, y
el historial `Z` satisface `|Z| · 2^{C(h+1,2)} ≤ (α/2) n`, entonces para cada par de
triángulos permitidos `T_a, T_b` con arista común existe una bisagra de orden
`i ∈ [6, h]` cuyo soporte evita `Z` fuera de las cuatro raíces. -/
theorem exists_fresh_hinge {H : Host V I} {F : Set (Multiset I)} {α : ℝ} {h : ℕ}
    (hα : 0 < α) (hH4 : HingeCond H F α h) {u v a b : V} (hab : a ≠ b)
    (hTa : IsAllowed H F {u, v, a}) (hTb : IsAllowed H F {u, v, b}) (Z : Finset V)
    (hZ : (Z.card : ℝ) * 2 ^ Nat.choose (h + 1) 2 ≤ α / 2 * Fintype.card V) :
    ∃ i, 6 ≤ i ∧ i ≤ h ∧ ∃ J ∈ hinges H F u v a b i,
      ∀ z ∈ Z, z ∈ support J → z ∈ ({u, v, a, b} : Finset V) := by
  obtain ⟨i, hi6, hih, hsupply⟩ := hH4 u v a b hab hTa hTb
  have hn : (0 : ℝ) < Fintype.card V := by
    have : Nonempty V := ⟨u⟩
    exact_mod_cast Fintype.card_pos
  have hpow : (Fintype.card V : ℝ) ^ (i - 4) = Fintype.card V * (Fintype.card V : ℝ) ^ (i - 5) := by
    rw [← pow_succ']; congr 1; omega
  have hchoose : (2 : ℝ) ^ Nat.choose (i + 1) 2 ≤ 2 ^ Nat.choose (h + 1) 2 := by
    apply pow_le_pow_right₀ (by norm_num)
    exact Nat.choose_le_choose 2 (by omega)
  have hZ' : (Z.card : ℝ) * (Fintype.card V : ℝ) ^ (i - 5) * 2 ^ Nat.choose (i + 1) 2 ≤
      α / 2 * (Fintype.card V : ℝ) ^ (i - 4) := by
    rw [hpow]
    have hp : (0 : ℝ) ≤ (Fintype.card V : ℝ) ^ (i - 5) := by positivity
    calc (Z.card : ℝ) * (Fintype.card V : ℝ) ^ (i - 5) * 2 ^ Nat.choose (i + 1) 2
        ≤ (Z.card : ℝ) * (Fintype.card V : ℝ) ^ (i - 5) * 2 ^ Nat.choose (h + 1) 2 :=
          mul_le_mul_of_nonneg_left hchoose (by positivity)
      _ = ((Z.card : ℝ) * 2 ^ Nat.choose (h + 1) 2) * (Fintype.card V : ℝ) ^ (i - 5) := by ring
      _ ≤ (α / 2 * Fintype.card V) * (Fintype.card V : ℝ) ^ (i - 5) :=
          mul_le_mul_of_nonneg_right hZ hp
      _ = α / 2 * (Fintype.card V * (Fintype.card V : ℝ) ^ (i - 5)) := by ring
  have hfresh := fresh_hinges hab hTa hTb i (by omega) α Z hsupply hZ'
  have hpos : (0 : ℝ) < α / 2 * (Fintype.card V : ℝ) ^ (i - 4) := by positivity
  have hne : ((hinges H F u v a b i).filter
      (fun J => ∀ z ∈ Z, z ∈ support J → z ∈ ({u, v, a, b} : Finset V))).Nonempty := by
    rw [← Finset.card_pos]
    exact_mod_cast hpos.trans_le hfresh
  obtain ⟨J, hJ⟩ := hne
  exact ⟨i, hi6, hih, J, (Finset.mem_filter.1 hJ).1, (Finset.mem_filter.1 hJ).2⟩

end TypedTriangle
