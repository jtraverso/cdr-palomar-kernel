/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license.
Authors: Juan Pablo Traverso Gianini
-/
module

public import CDRIIILib.KBicolor.ResidualSeedK

/-!
# Residual seeds with exact type masses (`k` classes)

The cycle coordinates are the pairs `Y < Z` of classes other than the hub `o` (`Coord o`). The
circulation `circ o Y Z` of the oriented triangle `Y → Z → o → Y` is antisymmetric, has zero row
sums (`circ_row_zero`), and is `1` on the coordinate `(Y, Z)` and `0` on the other coordinates
(`circ_coord`). Shifting a real type-count target by circulations preserves the linear identities
(`seedData_of_targetR`).

`residual_seed_exact`: for every target `t₀` in the interior (with margin), a diffuse seed of
`K_n − L` whose type masses on all cycle coordinates are exactly `t₀`. Each vertex of the cube
`t₀ ± R` is realised up to `E < R` by `residual_seed_k`; `exists_seed_exact_mass` concludes.
-/

@[expose] public section

noncomputable section

namespace CDRBicolour.KBicolor

open Finset TypedTriangle CDRBicolour.Absorption CDRBicolour.Absorption.Refined

variable {k : ℕ}

/-- Cycle coordinates: pairs `Y < Z` of classes other than `o`. -/
abbrev Coord (o : Fin k) := {p : Fin k × Fin k // p.1 < p.2 ∧ p.1 ≠ o ∧ p.2 ≠ o}

/-- The oriented triangle `Y → Z → o → Y`. -/
def fcyc (o Y Z A B : Fin k) : ℝ :=
  (if A = Y then (if B = Z then 1 else 0) else 0) + (if A = Z then (if B = o then 1 else 0) else 0) +
    (if A = o then (if B = Y then 1 else 0) else 0)

/-- Its circulation. -/
def circ (o Y Z : Fin k) (A B : Fin k) : ℝ := fcyc o Y Z A B - fcyc o Y Z B A

theorem circ_antisymm (o Y Z A B : Fin k) : circ o Y Z A B + circ o Y Z B A = 0 := by
  unfold circ; ring

theorem fcyc_bounds (o Y Z A B : Fin k) : 0 ≤ fcyc o Y Z A B ∧ fcyc o Y Z A B ≤ 3 := by
  unfold fcyc; constructor <;> split_ifs <;> norm_num

theorem abs_circ_le (o Y Z A B : Fin k) : |circ o Y Z A B| ≤ 3 := by
  unfold circ
  obtain ⟨a1, a2⟩ := fcyc_bounds o Y Z A B
  obtain ⟨b1, b2⟩ := fcyc_bounds o Y Z B A
  rw [abs_le]; constructor <;> linarith

theorem sum_ite_ne (A Z : Fin k) (c : ℝ) :
    ∑ B ∈ univ.filter (fun B => B ≠ A), (if B = Z then c else 0) = if Z ≠ A then c else 0 := by
  rw [sum_ite_eq']
  simp

theorem sum_fcyc_out {o Y Z : Fin k} (hY : Y ≠ o) (hZ : Z ≠ o) (hYZ : Y ≠ Z) (A : Fin k) :
    ∑ B ∈ univ.filter (fun B => B ≠ A), fcyc o Y Z A B =
      (if A = Y then 1 else 0) + (if A = Z then 1 else 0) + (if A = o then 1 else 0) := by
  unfold fcyc
  rw [sum_add_distrib, sum_add_distrib]
  have h : ∀ (P : Prop) [Decidable P] (W : Fin k),
      ∑ B ∈ univ.filter (fun B => B ≠ A), (if P then (if B = W then (1 : ℝ) else 0) else 0) =
        if P then (if W ≠ A then 1 else 0) else 0 := by
    intro P _ W
    by_cases hP : P
    · simp only [hP, ite_true]; exact sum_ite_ne A W 1
    · simp [hP]
  rw [h, h, h]
  by_cases h1 : A = Y <;> by_cases h2 : A = Z <;> by_cases h3 : A = o <;> subst_vars <;>
    simp_all [eq_comm]

theorem sum_fcyc_in {o Y Z : Fin k} (hY : Y ≠ o) (hZ : Z ≠ o) (hYZ : Y ≠ Z) (A : Fin k) :
    ∑ B ∈ univ.filter (fun B => B ≠ A), fcyc o Y Z B A =
      (if A = Y then 1 else 0) + (if A = Z then 1 else 0) + (if A = o then 1 else 0) := by
  unfold fcyc
  rw [sum_add_distrib, sum_add_distrib]
  have h : ∀ (W : Fin k) (P : Prop) [Decidable P],
      ∑ B ∈ univ.filter (fun B => B ≠ A), (if B = W then (if P then (1 : ℝ) else 0) else 0) =
        if W ≠ A then (if P then 1 else 0) else 0 := by
    intro W P _
    exact sum_ite_ne A W _
  rw [h, h, h]
  by_cases h1 : A = Y <;> by_cases h2 : A = Z <;> by_cases h3 : A = o <;> subst_vars <;>
    simp_all [eq_comm]

theorem circ_row_zero {o Y Z : Fin k} (hY : Y ≠ o) (hZ : Z ≠ o) (hYZ : Y ≠ Z) (A : Fin k) :
    ∑ B ∈ univ.filter (fun B => B ≠ A), circ o Y Z A B = 0 := by
  unfold circ
  rw [sum_sub_distrib, sum_fcyc_out hY hZ hYZ, sum_fcyc_in hY hZ hYZ, sub_self]

theorem circ_coord {o : Fin k} (i j : Coord o) :
    circ o j.1.1 j.1.2 i.1.1 i.1.2 = if i = j then 1 else 0 := by
  obtain ⟨⟨Y, Z⟩, hlt, hY, hZ⟩ := i
  obtain ⟨⟨Y', Z'⟩, hlt', hY', hZ'⟩ := j
  simp only at hlt hY hZ hlt' hY' hZ' ⊢
  unfold circ fcyc
  by_cases hY1 : Y = Y' <;> by_cases hZ1 : Z = Z'
  · subst hY1; subst hZ1
    have h1 : Z ≠ Y := (ne_of_lt hlt).symm
    simp [h1, hZ, hY, Ne.symm hY]
  · have hne : (⟨⟨Y, Z⟩, hlt, hY, hZ⟩ : Coord o) ≠ ⟨⟨Y', Z'⟩, hlt', hY', hZ'⟩ := by
      intro h; apply hZ1; have := congrArg (fun q : Coord o => q.1.2) h; exact this
    rw [if_neg hne]
    by_cases h2 : Z = Y'
    · subst h2
      by_cases h3 : Y = Z'
      · subst h3; exact absurd (hlt.trans hlt') (lt_irrefl _)
      · simp [hY1, hZ1, h3, hZ, hY, Ne.symm hY', Ne.symm hZ', hY', hZ']
    · simp [hY1, hZ1, h2, hZ, hY, Ne.symm hY', Ne.symm hZ', hY', hZ']
  · have hne : (⟨⟨Y, Z⟩, hlt, hY, hZ⟩ : Coord o) ≠ ⟨⟨Y', Z'⟩, hlt', hY', hZ'⟩ := by
      intro h; apply hY1; have := congrArg (fun q : Coord o => q.1.1) h; exact this
    rw [if_neg hne]
    by_cases h3 : Y = Z'
    · subst h3
      by_cases h2 : Z = Y'
      · subst h2; exact absurd (hlt.trans hlt') (lt_irrefl _)
      · simp [hY1, hZ1, h2, hZ, hY, Ne.symm hY', Ne.symm hZ', hY', hZ']
    · simp [hY1, hZ1, h3, hZ, hY, Ne.symm hY', Ne.symm hZ', hY', hZ']
  · have hne : (⟨⟨Y, Z⟩, hlt, hY, hZ⟩ : Coord o) ≠ ⟨⟨Y', Z'⟩, hlt', hY', hZ'⟩ := by
      intro h; apply hY1; have := congrArg (fun q : Coord o => q.1.1) h; exact this
    rw [if_neg hne]
    by_cases h2 : Z = Y' <;> by_cases h3 : Y = Z'
    · subst h2; subst h3; exact absurd (hlt.trans hlt') (lt_irrefl _)
    all_goals simp_all [Ne.symm hY', Ne.symm hZ']

/-- Seed data from a real type-count target. -/
theorem seedData_of_targetR {V : Type*} [Fintype V] (lab : V → Fin k) {η : ℝ}
    (t : Fin k → Fin k → ℝ) (hpos : ∀ X, 0 < ksz lab X)
    (hpair : ∀ X Y, X ≠ Y → 2 * (t X Y + t Y X) = (ksz lab X : ℝ) * ksz lab Y)
    (hrow : ∀ X, 2 * ∑ Y ∈ univ.filter (fun Y => Y ≠ X), t X Y =
      (ksz lab X : ℝ) * ((ksz lab X : ℝ) - 1))
    (hlow : ∀ X Y, X ≠ Y → η * ksz lab X * ksz lab Y ≤ 2 * t X Y) :
    SeedData (ksz lab) η (fun X Y => 2 * t X Y / ((ksz lab X : ℝ) * ksz lab Y)) := by
  have hc : ∀ X, (0 : ℝ) < ksz lab X := fun X => by exact_mod_cast hpos X
  refine ⟨fun X Y hXY => ?_, fun X Y hXY => ?_, fun X => ?_⟩
  · have h' := hpair X Y hXY
    have hXY0 := (mul_pos (hc X) (hc Y)).ne'
    have hYX0 := (mul_pos (hc Y) (hc X)).ne'
    rw [div_add_div _ _ hXY0 hYX0, div_eq_one_iff_eq (mul_ne_zero hXY0 hYX0)]
    have e : (ksz lab Y : ℝ) * ksz lab X = ksz lab X * ksz lab Y := mul_comm _ _
    rw [e]
    have h'' := congrArg (· * ((ksz lab X : ℝ) * ksz lab Y)) h'
    linarith
  · rw [le_div_iff₀ (mul_pos (hc X) (hc Y))]
    have := hlow X Y hXY
    linarith
  · have e : ∀ Y ∈ univ.filter (fun Y => Y ≠ X),
        (ksz lab Y : ℝ) * (2 * t X Y / ((ksz lab X : ℝ) * ksz lab Y)) =
          2 * t X Y / ksz lab X := fun Y _ => by
      field_simp [(hc X).ne', (hc Y).ne']
    rw [sum_congr rfl e, ← sum_div, ← mul_sum, hrow X]
    field_simp [(hc X).ne']

/-- The shifted target of a vertex of the cube. -/
def tshift (o : Fin k) (t₀ : Fin k → Fin k → ℝ) (R : ℝ) (v : Coord o → Bool) (A B : Fin k) : ℝ :=
  t₀ A B + ∑ j : Coord o, (if v j then R else -R) * circ o j.1.1 j.1.2 A B

theorem tshift_pair (o : Fin k) (t₀ : Fin k → Fin k → ℝ) (R : ℝ) (v : Coord o → Bool)
    (A B : Fin k) :
    tshift o t₀ R v A B + tshift o t₀ R v B A = t₀ A B + t₀ B A := by
  unfold tshift
  have : ∑ j : Coord o, (if v j then R else -R) * circ o j.1.1 j.1.2 A B +
      ∑ j : Coord o, (if v j then R else -R) * circ o j.1.1 j.1.2 B A = 0 := by
    rw [← sum_add_distrib]
    exact sum_eq_zero fun j _ => by rw [← mul_add, circ_antisymm, mul_zero]
  linarith

theorem tshift_row (o : Fin k) (t₀ : Fin k → Fin k → ℝ) (R : ℝ) (v : Coord o → Bool) (A : Fin k) :
    ∑ B ∈ univ.filter (fun B => B ≠ A), tshift o t₀ R v A B =
      ∑ B ∈ univ.filter (fun B => B ≠ A), t₀ A B := by
  unfold tshift
  rw [sum_add_distrib, sum_comm]
  have : ∑ j : Coord o, ∑ B ∈ univ.filter (fun B => B ≠ A),
      (if v j then R else -R) * circ o j.1.1 j.1.2 A B = 0 := by
    refine sum_eq_zero fun j _ => ?_
    rw [← mul_sum, circ_row_zero j.2.2.1 j.2.2.2 (ne_of_lt j.2.1), mul_zero]
  rw [this, add_zero]

theorem tshift_coord (o : Fin k) (t₀ : Fin k → Fin k → ℝ) (R : ℝ) (v : Coord o → Bool)
    (i : Coord o) :
    tshift o t₀ R v i.1.1 i.1.2 = t₀ i.1.1 i.1.2 + (if v i then R else -R) := by
  unfold tshift
  simp_rw [circ_coord i, mul_ite, mul_one, mul_zero]
  rw [sum_ite_eq]
  simp

theorem tshift_low (o : Fin k) (t₀ : Fin k → Fin k → ℝ) {R : ℝ} (hR : 0 ≤ R)
    (v : Coord o → Bool) (A B : Fin k) :
    t₀ A B - 3 * Fintype.card (Coord o) * R ≤ tshift o t₀ R v A B := by
  unfold tshift
  have : -(3 * Fintype.card (Coord o) * R) ≤
      ∑ j : Coord o, (if v j then R else -R) * circ o j.1.1 j.1.2 A B := by
    have h : ∀ j : Coord o, -(3 * R) ≤ (if v j then R else -R) * circ o j.1.1 j.1.2 A B := by
      intro j
      have hc := abs_circ_le o j.1.1 j.1.2 A B
      rw [abs_le] at hc
      split_ifs <;> nlinarith
    calc -(3 * Fintype.card (Coord o) * R) = ∑ _j : Coord o, -(3 * R) := by
          rw [sum_const, card_univ, nsmul_eq_mul]; ring
      _ ≤ _ := sum_le_sum fun j _ => h j
  linarith

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- **Residual seed with exact type masses on the cycle coordinates.** -/
theorem residual_seed_exact (lab : V → Fin k) (hk : 3 ≤ k) (o : Fin k) {m : ℕ} {R δ η : ℝ}
    (hR : 1 ≤ R) (hm : ∀ X, m ≤ ksz lab X) (h512 : 512 ≤ m) (hmR : 64 * R ^ 3 ≤ m)
    (hbal : (Fintype.card V : ℝ) ≤ R * m) (hδ : 0 < δ) (hη : 0 < η)
    (hcls : ∀ X, δ * Fintype.card V ≤ ksz lab X) (h2 : 2 ≤ δ * Fintype.card V)
    (t₀ : Fin k → Fin k → ℝ)
    (hpair : ∀ X Y, X ≠ Y → 2 * (t₀ X Y + t₀ Y X) = (ksz lab X : ℝ) * ksz lab Y)
    (hrow : ∀ X, 2 * ∑ Y ∈ univ.filter (fun Y => Y ≠ X), t₀ X Y =
      (ksz lab X : ℝ) * ((ksz lab X : ℝ) - 1))
    (P : Finset (Finset V)) (hP : ∀ T ∈ P, IsAllowed (kHost lab) (bicF k) T)
    (hPd : (P : Set (Finset V)).PairwiseDisjoint triEdges) {Δ : ℕ}
    (hdeg : ∀ p, degL (P.biUnion triEdges) p ≤ Δ)
    (hΔ : 8 * ((#(Trip o) : ℝ) * (400 * R ^ 5 * R * (1 + 4 * R ^ 2))) *
      (1 / η + 2 / δ) ^ 2 * Δ ≤ Fintype.card V)
    {ρ : ℝ} (hρ : (4 * ((#(Trip o) : ℝ) * (400 * R ^ 5 * R * (1 + 4 * R ^ 2))) + 1) *
      (1 / η + 2 / δ) * Δ * Fintype.card V < ρ)
    (hlow : ∀ X Y, X ≠ Y →
      η * ksz lab X * ksz lab Y + 6 * Fintype.card (Coord o) * ρ ≤ 2 * t₀ X Y) :
    ∃ μ, IsDiffuseSeed (rHostK lab (P.biUnion triEdges)) (bicF k) (2 * (1 / η + 2 / δ)) μ ∧
      ∀ i : Coord o,
        ∑ Q ∈ allowed (rHostK lab (P.biUnion triEdges)) (bicF k), μ Q * wXY lab i.1.1 i.1.2 Q =
          t₀ i.1.1 i.1.2 := by
  classical
  have hρ0 : 0 ≤ ρ := le_trans (by positivity) hρ.le
  have hpos : ∀ X, 0 < ksz lab X := fun X => by
    have : (0 : ℝ) < ksz lab X := lt_of_lt_of_le (by linarith) (le_trans h2 (hcls X))
    exact_mod_cast this
  refine exists_seed_exact_mass (allowed (rHostK lab (P.biUnion triEdges)) (bicF k))
    (fun i : Coord o => wXY lab i.1.1 i.1.2) (fun i : Coord o => t₀ i.1.1 i.1.2) hρ
    (fun v => ?_)
  -- the seed of the shifted target
  set t := tshift o t₀ ρ v
  have ht_pair : ∀ X Y, X ≠ Y → 2 * (t X Y + t Y X) = (ksz lab X : ℝ) * ksz lab Y := by
    intro X Y h; rw [tshift_pair, hpair X Y h]
  have ht_row : ∀ X, 2 * ∑ Y ∈ univ.filter (fun Y => Y ≠ X), t X Y =
      (ksz lab X : ℝ) * ((ksz lab X : ℝ) - 1) := by
    intro X; rw [tshift_row, hrow X]
  have ht_low : ∀ X Y, X ≠ Y → η * ksz lab X * ksz lab Y ≤ 2 * t X Y := by
    intro X Y h
    have h1 := tshift_low o t₀ hρ0 v X Y
    have h2' := hlow X Y h
    linarith
  have ha := seedData_of_targetR lab t hpos ht_pair ht_row ht_low
  obtain ⟨μ, hμ, hmass⟩ := residual_seed_k lab hk o hR hm h512 hmR hbal hδ hη hcls h2 ha P hP
    hPd hdeg hΔ
  refine ⟨μ, hμ, fun i => ?_⟩
  have hi := hmass i.1.1 i.1.2 (ne_of_lt i.2.1)
  have hc : ∀ X, (0 : ℝ) < ksz lab X := fun X => by exact_mod_cast hpos X
  have e : (ksz lab i.1.1 : ℝ) * ksz lab i.1.2 *
      (2 * t i.1.1 i.1.2 / ((ksz lab i.1.1 : ℝ) * ksz lab i.1.2)) / 2 = t i.1.1 i.1.2 := by
    field_simp [(hc i.1.1).ne', (hc i.1.2).ne']
  have hcoord : t i.1.1 i.1.2 = t₀ i.1.1 i.1.2 + (if v i then ρ else -ρ) :=
    tshift_coord o t₀ ρ v i
  rw [e, hcoord] at hi
  exact hi

end CDRBicolour.KBicolor
