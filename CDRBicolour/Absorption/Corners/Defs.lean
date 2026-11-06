/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license.
Authors: Juan Pablo Traverso Gianini
-/
module

public import CDRBicolour.Absorption.Corners.GenSeedMulti
public import CDRBicolour.Absorption.Lattice

/-!
# Majority types and the vertex functionals `π_u` (item 3, corners)

Classes `X ∈ Fin 3`.  The **majority** types are `XX(X+1)` (`AAB`, `BBC`, `CCA`, family `majF`);
the **minority** types are `XX(X+2)` (`AAC`, `BBA`, `CCB`).  Together they are the bicoloured types.

For a vertex `u` of class `X`, `π_u(y) = y(X-edges at u) − y((X+1)-edges at u)`: weight `wpi u`.
Every majority triangle has `π_u = 0` for all `u` (`maj_piT`); a minority triangle `{p, q, r}` with
`p, q ∈ X`, `r ∈ X+2` has `π = 1, 1, −2` at `p, q, r` and `0` elsewhere (`min_piT`).
Summing over `u` gives `−ℓ` (`sum_wpi`), so `ker π ⊆ ker ℓ` (`ell_of_pi`).
-/

@[expose] public section

noncomputable section

namespace CDRBicolour.Absorption.Corners

open Finset TypedTriangle CDRBicolour.Prefix CDRBicolour.Absorption CDRBicolour.Absorption.Refined

/-! ### Types -/

/-- Majority types `XX(X+1)`. -/
def majF : Set (Multiset (Fin 3)) := {m | ∃ X : Fin 3, m = {X, X, X + 1}}

/-- The minority type `XX(X+2)`. -/
def minT (X : Fin 3) : Multiset (Fin 3) := {X, X, X + 2}

theorem majF_sub : majF ⊆ cdrF := by
  rintro m ⟨X, rfl⟩
  simp only [cdrF, Set.mem_setOf_eq]
  fin_cases X <;> decide

theorem minT_mem (X : Fin 3) : minT X ∈ cdrF := by
  simp only [cdrF, Set.mem_setOf_eq, minT]
  fin_cases X <;> decide

theorem maj_triple_iff (x y z : Fin 3) :
    ({x, y, z} : Multiset (Fin 3)) ∈ majF ↔ ∃ X : Fin 3, ({x, y, z} : Multiset (Fin 3)) = {X, X, X + 1} :=
  Iff.rfl

theorem cdr_triple_cases (x y z : Fin 3) (h : ({x, y, z} : Multiset (Fin 3)) ∈ cdrF) :
    (∃ X : Fin 3, ({x, y, z} : Multiset (Fin 3)) = {X, X, X + 1}) ∨
      ∃ X : Fin 3, ({x, y, z} : Multiset (Fin 3)) = minT X := by
  simp only [cdrF, Set.mem_setOf_eq] at h
  unfold minT
  revert x y z
  decide

theorem maj_not_min (x y z : Fin 3) (X Y : Fin 3)
    (h1 : ({x, y, z} : Multiset (Fin 3)) = {X, X, X + 1}) : ({x, y, z} : Multiset (Fin 3)) ≠ minT Y := by
  unfold minT
  revert x y z X Y
  decide

theorem maj_triple_shape (x y z X : Fin 3) (h : ({x, y, z} : Multiset (Fin 3)) = {X, X, X + 1}) :
    (x = X ∧ y = X ∧ z = X + 1) ∨ (x = X ∧ y = X + 1 ∧ z = X) ∨ (x = X + 1 ∧ y = X ∧ z = X) := by
  revert x y z X
  decide

theorem min_triple_shape (x y z X : Fin 3) (h : ({x, y, z} : Multiset (Fin 3)) = minT X) :
    (x = X ∧ y = X ∧ z = X + 2) ∨ (x = X ∧ y = X + 2 ∧ z = X) ∨ (x = X + 2 ∧ y = X ∧ z = X) := by
  unfold minT at h
  revert x y z X
  decide

theorem minT_triple (X : Fin 3) : ({X, X, X + 2} : Multiset (Fin 3)) = minT X := rfl

theorem minT_inj {X Y : Fin 3} (h : minT X = minT Y) : X = Y := by
  unfold minT at h
  revert X Y
  decide

variable {V : Type*} [Fintype V] [DecidableEq V] (lab : V → Fin 3)

/-! ### Shapes of triangles of the complete host -/

theorem tri_three {F : Set (Multiset (Fin 3))} {T : Finset V} (hT : T ∈ triG lab F) :
    ∃ p q r, T = {p, q, r} ∧ p ≠ q ∧ p ≠ r ∧ q ≠ r ∧
      ({lab p, lab q, lab r} : Multiset (Fin 3)) ∈ F := by
  rw [gmem_tri] at hT
  obtain ⟨h3, -, hF⟩ := hT
  obtain ⟨p, q, r, hpq, hpr, hqr, rfl⟩ := card_eq_three.mp h3
  refine ⟨p, q, r, rfl, hpq, hpr, hqr, ?_⟩
  rwa [val_map_triple lab hpq hpr.symm hqr.symm] at hF

/-- A majority triangle: `p, q ∈ X`, `r ∈ X + 1`. -/
theorem maj_shape {T : Finset V} (hT : T ∈ triG lab majF) :
    ∃ p q r, T = {p, q, r} ∧ p ≠ q ∧ lab q = lab p ∧ lab r = lab p + 1 := by
  obtain ⟨p, q, r, rfl, hpq, hpr, hqr, X, hX⟩ := tri_three lab hT
  rcases maj_triple_shape _ _ _ X hX with ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩
  · exact ⟨p, q, r, rfl, hpq, by rw [h1, h2], by rw [h1, h3]⟩
  · exact ⟨p, r, q, by ext; simp; tauto, hpr, by rw [h1, h3], by rw [h1, h2]⟩
  · exact ⟨q, r, p, by ext; simp; tauto, hqr, by rw [h2, h3], by rw [h1, h2]⟩

/-- A minority triangle: `p, q ∈ X`, `r ∈ X + 2`. -/
theorem min_shape {T : Finset V} {X : Fin 3} (hT : T ∈ triG lab cdrF) (hX : T.val.map lab = minT X) :
    ∃ p q r, T = {p, q, r} ∧ p ≠ q ∧ lab p = X ∧ lab q = X ∧ lab r = X + 2 := by
  obtain ⟨p, q, r, rfl, hpq, hpr, hqr, -⟩ := tri_three lab hT
  rw [val_map_triple lab hpq hpr.symm hqr.symm] at hX
  rcases min_triple_shape _ _ _ X hX with ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩
  · exact ⟨p, q, r, rfl, hpq, h1, h2, h3⟩
  · exact ⟨p, r, q, by ext; simp; tauto, hpr, h1, h3, h2⟩
  · exact ⟨q, r, p, by ext; simp; tauto, hqr, h2, h3, h1⟩

/-- Every bicoloured triangle of the complete host is majority or minority. -/
theorem cdr_split {T : Finset V} (hT : T ∈ triG lab cdrF) :
    T ∈ triG lab majF ∨ ∃ X, T.val.map lab = minT X := by
  obtain ⟨p, q, r, rfl, hpq, hpr, hqr, hF⟩ := tri_three lab hT
  have hv := val_map_triple lab hpq hpr.symm hqr.symm
  rcases cdr_triple_cases _ _ _ hF with ⟨X, hX⟩ | ⟨X, hX⟩
  · left
    rw [gmem_tri] at hT ⊢
    exact ⟨hT.1, hT.2.1, by show _ ∈ majF; rw [hv]; exact ⟨X, hX⟩⟩
  · right; exact ⟨X, by rw [hv, hX]⟩

theorem maj_not_minT {T : Finset V} (hT : T ∈ triG lab majF) (X : Fin 3) :
    T.val.map lab ≠ minT X := by
  obtain ⟨p, q, r, rfl, hpq, hpr, hqr, Y, hY⟩ := tri_three lab hT
  rw [val_map_triple lab hpq hpr.symm hqr.symm]
  exact maj_not_min _ _ _ Y X hY

/-! ### The vertex functionals -/

/-- The weight of a neighbour `y` seen from `u`: `1` in the class of `u`, `−1` in the next class. -/
def chi (u y : V) : ℝ := if lab y = lab u then 1 else if lab y = lab u + 1 then -1 else 0

/-- The weight of `π_u`. -/
def wpi (u : V) : Sym2 V → ℝ :=
  Sym2.lift ⟨fun p q => (if p = u then chi lab u q else 0) + (if q = u then chi lab u p else 0),
    fun _ _ => add_comm _ _⟩

theorem wpi_mk (u p q : V) :
    wpi lab u s(p, q) = (if p = u then chi lab u q else 0) + (if q = u then chi lab u p else 0) :=
  rfl

/-- `π_u` of a triangle. -/
def piT (T : Finset V) (u : V) : ℝ := ∑ f ∈ triEdges T, wpi lab u f

theorem piT_triple {p q r : V} (hpq : p ≠ q) (hpr : p ≠ r) (hqr : q ≠ r) (u : V) :
    piT lab {p, q, r} u = wpi lab u s(p, q) + wpi lab u s(p, r) + wpi lab u s(q, r) := by
  unfold piT
  rw [triEdges_triple hpq hpr hqr]
  have h1 : s(p, q) ≠ s(p, r) := fun h => by
    rcases Sym2.eq_iff.1 h with ⟨-, h⟩ | ⟨h, -⟩
    · exact hqr h
    · exact hpr h
  have h2 : s(p, q) ≠ s(q, r) := fun h => by
    rcases Sym2.eq_iff.1 h with ⟨h, -⟩ | ⟨h, -⟩
    · exact hpq h
    · exact hpr h
  have h3 : s(p, r) ≠ s(q, r) := fun h => by
    rcases Sym2.eq_iff.1 h with ⟨h, -⟩ | ⟨h, -⟩
    · exact hpq h
    · exact hpr h
  rw [sum_insert (by simp [h1, h2]), sum_insert (by simp [h3]), sum_singleton, add_assoc]

theorem lab_ne_succ (x : Fin 3) : x ≠ x + 1 := by revert x; decide
theorem lab_ne_succ2 (x : Fin 3) : x ≠ x + 2 := by revert x; decide
theorem lab_succ_ne (x : Fin 3) : x + 1 ≠ x + 2 := by revert x; decide
theorem lab_ne_succ_succ (x : Fin 3) : x ≠ x + 1 + 1 := by revert x; decide

/-- **Majority triangles have `π = 0`.** -/
theorem maj_piT {T : Finset V} (hT : T ∈ triG lab majF) (u : V) : piT lab T u = 0 := by
  obtain ⟨p, q, r, rfl, hpq, hq, hr⟩ := maj_shape lab hT
  have hpr : p ≠ r := fun h => lab_ne_succ (lab p) (by rw [← hr, h])
  have hqr : q ≠ r := fun h => lab_ne_succ (lab p) (by rw [← hr, ← hq, h])
  rw [piT_triple lab hpq hpr hqr]
  simp only [wpi_mk, chi]
  have a1 : lab p ≠ lab r := by rw [hr]; exact lab_ne_succ _
  have a2 : lab r ≠ lab p + 1 + 1 := by rw [hr]; exact lab_ne_succ _
  by_cases hu : u = p
  · subst hu
    simp [hpq.symm, hpr.symm, hq, hr, lab_ne_succ, Ne.symm hpq, Ne.symm hpr]
  by_cases hu' : u = q
  · subst hu'
    simp [hpq, hqr.symm, Ne.symm hu, hq, hr, lab_ne_succ]
  by_cases hu'' : u = r
  · subst hu''
    have b1 : lab p ≠ lab u := a1
    have b2 : lab p ≠ lab u + 1 := by
      rw [hr]; intro h; exact absurd h (by revert h; generalize lab p = x; revert x; decide)
    simp [Ne.symm hu, Ne.symm hu', hpr, hqr, hq, b1, b2]
  simp [Ne.symm hu, Ne.symm hu', Ne.symm hu'']

/-- **Minority triangles: `π = 1, 1, −2`.** -/
theorem min_piT {p q r : V} (hpq : p ≠ q) (hq : lab q = lab p) (hr : lab r = lab p + 2) (u : V) :
    piT lab {p, q, r} u =
      (if u = p then 1 else 0) + (if u = q then 1 else 0) - 2 * (if u = r then 1 else 0) := by
  have hpr : p ≠ r := fun h => lab_ne_succ2 (lab p) (by rw [← hr, h])
  have hqr : q ≠ r := fun h => lab_ne_succ2 (lab p) (by rw [← hr, ← hq, h])
  rw [piT_triple lab hpq hpr hqr]
  simp only [wpi_mk, chi]
  have c1 : lab r ≠ lab p := by rw [hr]; exact (lab_ne_succ2 _).symm
  have c2 : lab r ≠ lab p + 1 := by rw [hr]; exact (lab_succ_ne _).symm
  have c3 : lab p = lab r + 1 := by rw [hr]; generalize lab p = x; revert x; decide
  have c4 : lab p ≠ lab r := by rw [hr]; exact lab_ne_succ2 _
  by_cases hu : u = p
  · subst hu
    simp [hpq, hpr, hq, c1, c2, Ne.symm hpq, Ne.symm hpr]
  by_cases hu' : u = q
  · subst hu'
    simp [hpq.symm, hqr, hq, c1, c2, Ne.symm hu, Ne.symm hqr]
  by_cases hu'' : u = r
  · subst hu''
    simp [Ne.symm hu, Ne.symm hu', hpr.symm, hqr.symm, hq, c3, c4]
    norm_num
  simp [Ne.symm hu, Ne.symm hu', Ne.symm hu'', hu, hu', hu'']

/-! ### `Σ_u π_u = −ℓ` -/

theorem sum_wpi (e : E0 V) : ∑ u, wpi lab u e.1 = -wl lab e.1 := by
  obtain ⟨e, he⟩ := e
  induction e using Sym2.ind with
  | _ p q =>
  have hpq : p ≠ q := by simpa using he
  simp only [wpi_mk, sum_add_distrib, sum_ite_eq', mem_univ, if_true, wl, Sym2.lift_mk]
  simp only [chi]
  by_cases h : lab p = lab q
  · simp [h]; norm_num
  · rcases (show lab q = lab p + 1 ∨ lab p = lab q + 1 by
        revert h; generalize lab p = x; generalize lab q = y; revert x y; decide) with h1 | h1
    · have h2 : lab p ≠ lab q + 1 := by rw [h1]; generalize lab p = x; revert x; decide
      simp [h, Ne.symm h, h1, h2, lab_ne_succ_succ]
    · have h2 : lab q ≠ lab p + 1 := by rw [h1]; generalize lab q = x; revert x; decide
      simp [h, Ne.symm h, h1, h2, lab_ne_succ_succ]

/-- `ker π ⊆ ker ℓ`. -/
theorem ell_of_pi {d : E0 V → ℝ} (hd : ∀ u, ellG' (wpi lab u) d = 0) : ellG' (wl lab) d = 0 := by
  have : ellG' (wl lab) d = -∑ u, ellG' (wpi lab u) d := by
    simp only [ellG', LinearMap.coe_mk, AddHom.coe_mk]
    rw [sum_comm, ← sum_neg_distrib]
    refine sum_congr rfl fun e _ => ?_
    rw [← sum_mul, sum_wpi]; ring
  rw [this, sum_eq_zero fun u _ => hd u, neg_zero]

/-- `π_u` of an incidence vector. -/
theorem ell_wpi_Minc (F : Set (Multiset (Fin 3))) (c : Finset V → ℝ) (u : V) :
    ellG' (wpi lab u) (MincG lab F c) = ∑ T ∈ triG lab F, c T * piT lab T u := by
  simp only [ellG', MincG, LinearMap.coe_mk, AddHom.coe_mk]
  simp_rw [mul_sum, sum_filter]
  rw [sum_comm]
  refine sum_congr rfl fun T _ => ?_
  have : ∀ e : E0 V, (if e.1 ∈ triEdges T then wpi lab u e.1 * c T else 0) =
      (if e.1 ∈ triEdges T then wpi lab u e.1 else 0) * c T := by
    intro e; split_ifs <;> simp
  simp_rw [this, ← sum_mul]
  rw [sum_E0 _ (triEdges T) (triEdges_nondiag T), mul_comm]
  rfl

end CDRBicolour.Absorption.Corners
