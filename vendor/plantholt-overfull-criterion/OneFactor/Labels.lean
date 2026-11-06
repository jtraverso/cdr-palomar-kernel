/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import OneFactor.Factors

/-!
# The vertex sets and the round-robin classes

`G` is `d`-regular; `w ≠ v*` are vertices. `W` = non-neighbours of `w`, `X` = neighbours of `w`
not adjacent to `v*`, `Y = W ∩ N(v*)`, `P = W − N[v*]`. Then `|X| = |Y|` (`card_X_eq_card_Y`).

Labels in `ℤ_N`, `N = 4|X| + 2|P| + 1`: `v* ↦ 0`, `X ↦` odd numbers `< 2|X|`, `Y ↦ 2·(label of the
paired x)`, `P ↦ 4|X| + j`. The class of a pair `{a, b}` is `(λa + λb)/2`; class `k` misses the
vertex labelled `k`, and the class of `v* y` is the label of the `x` paired with `y`.
-/

@[expose] public section

namespace OneFactor

open SimpleGraph Finset

open scoped Classical

attribute [-instance] SimpleGraph.Sdiff.adjDecidable SimpleGraph.Sup.adjDecidable

variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)

/-- Non-neighbours of `z` other than `z`. -/
noncomputable def nonNbr (z : V) : Finset V := univ.filter fun u => u ≠ z ∧ ¬ G.Adj z u

theorem card_nonNbr {d : ℕ} (hreg : ∀ v, G.degree v = d) (z : V) :
    #(nonNbr G z) + d + 1 = Fintype.card V := by
  have h1 : univ = insert z (G.neighborFinset z ∪ nonNbr G z) := by
    ext u; simp only [mem_univ, mem_insert, mem_union, mem_neighborFinset, nonNbr, mem_filter,
      true_and, true_iff]
    tauto
  have h2 : Disjoint (G.neighborFinset z) (nonNbr G z) := by
    rw [Finset.disjoint_left]; intro u hu hu'
    exact (mem_filter.1 hu').2.2 ((mem_neighborFinset _ _ _).1 hu)
  have h3 : z ∉ G.neighborFinset z ∪ nonNbr G z := by
    simp [nonNbr, mem_neighborFinset]
  rw [← card_univ, h1, card_insert_of_notMem h3, card_union_of_disjoint h2,
    card_neighborFinset_eq_degree, hreg]
  omega

variable (w vs : V)

/-- `W`: the non-neighbours of `w`. -/
noncomputable def setW : Finset V := nonNbr G w
/-- `X`: neighbours of `w` not adjacent to `v*`. -/
noncomputable def setX : Finset V := univ.filter fun u => G.Adj w u ∧ u ≠ vs ∧ ¬ G.Adj vs u
/-- `Y = W ∩ N(v*)`. -/
noncomputable def setY : Finset V := (setW G w).filter fun u => G.Adj vs u
/-- `P = W − N[v*]`. -/
noncomputable def setP : Finset V := (setW G w).filter fun u => u ≠ vs ∧ ¬ G.Adj vs u

variable {G w vs}

theorem mem_setW {u : V} : u ∈ setW G w ↔ u ≠ w ∧ ¬ G.Adj w u := by simp [setW, nonNbr]
theorem mem_setX {u : V} : u ∈ setX G w vs ↔ G.Adj w u ∧ u ≠ vs ∧ ¬ G.Adj vs u := by
  simp [setX]
theorem mem_setY {u : V} : u ∈ setY G w vs ↔ (u ≠ w ∧ ¬ G.Adj w u) ∧ G.Adj vs u := by
  simp [setY, mem_setW]
theorem mem_setP {u : V} : u ∈ setP G w vs ↔ (u ≠ w ∧ ¬ G.Adj w u) ∧ u ≠ vs ∧ ¬ G.Adj vs u := by
  simp [setP, mem_setW]

theorem card_X_eq_card_Y {d : ℕ} (hreg : ∀ v, G.degree v = d) (hwv : w ≠ vs) :
    #(setX G w vs) = #(setY G w vs) := by
  have hv := card_nonNbr G hreg vs
  have hw := card_nonNbr G hreg w
  -- `N̄(v*) = X ∪ P ∪ ({w} if w ≁ v*)`, `W = Y ∪ P ∪ ({v*} if w ≁ v*)`
  have e1 : nonNbr G vs = (setX G w vs ∪ setP G w vs) ∪
      (if G.Adj w vs then ∅ else {w}) := by
    ext u
    simp only [nonNbr, mem_filter, mem_univ, true_and, mem_union, mem_setX, mem_setP]
    split_ifs with h
    · simp only [notMem_empty, or_false]
      constructor
      · rintro ⟨h1, h2⟩
        by_cases huw : u = w
        · subst huw; exact absurd h.symm h2
        · by_cases hwu : G.Adj w u
          · exact Or.inl ⟨hwu, h1, h2⟩
          · exact Or.inr ⟨⟨huw, hwu⟩, h1, h2⟩
      · rintro (⟨-, h1, h2⟩ | ⟨-, h1, h2⟩) <;> exact ⟨h1, h2⟩
    · simp only [mem_singleton]
      constructor
      · rintro ⟨h1, h2⟩
        by_cases huw : u = w
        · exact Or.inr huw
        · by_cases hwu : G.Adj w u
          · exact Or.inl (Or.inl ⟨hwu, h1, h2⟩)
          · exact Or.inl (Or.inr ⟨⟨huw, hwu⟩, h1, h2⟩)
      · rintro ((⟨-, h1, h2⟩ | ⟨-, h1, h2⟩) | rfl)
        · exact ⟨h1, h2⟩
        · exact ⟨h1, h2⟩
        · exact ⟨hwv, fun h' => h h'.symm⟩
  have e2 : setW G w = (setY G w vs ∪ setP G w vs) ∪ (if G.Adj w vs then ∅ else {vs}) := by
    ext u
    simp only [mem_setW, mem_union, mem_setY, mem_setP]
    split_ifs with h
    · simp only [notMem_empty, or_false]
      constructor
      · rintro ⟨h1, h2⟩
        by_cases hvu : G.Adj vs u
        · exact Or.inl ⟨⟨h1, h2⟩, hvu⟩
        · refine Or.inr ⟨⟨h1, h2⟩, fun he => ?_, hvu⟩
          subst he; exact h2 h
      · rintro (⟨h1, -⟩ | ⟨h1, -⟩) <;> exact h1
    · simp only [mem_singleton]
      constructor
      · rintro ⟨h1, h2⟩
        by_cases hvu : G.Adj vs u
        · exact Or.inl (Or.inl ⟨⟨h1, h2⟩, hvu⟩)
        · by_cases he : u = vs
          · exact Or.inr he
          · exact Or.inl (Or.inr ⟨⟨h1, h2⟩, he, hvu⟩)
      · rintro ((⟨h1, -⟩ | ⟨h1, -⟩) | rfl)
        · exact h1
        · exact h1
        · exact ⟨fun h' => hwv h'.symm, h⟩
  have dXP : Disjoint (setX G w vs) (setP G w vs) := by
    rw [Finset.disjoint_left]; intro u h1 h2
    exact (mem_setP.1 h2).1.2 (mem_setX.1 h1).1
  have dYP : Disjoint (setY G w vs) (setP G w vs) := by
    rw [Finset.disjoint_left]; intro u h1 h2
    exact (mem_setP.1 h2).2.2 (mem_setY.1 h1).2
  have hW : setW G w = nonNbr G w := rfl
  rw [e1, card_union_of_disjoint, card_union_of_disjoint dXP] at hv
  · rw [hW.symm, e2, card_union_of_disjoint, card_union_of_disjoint dYP] at hw
    · split_ifs at hv hw <;> simp at hv hw <;> omega
    · split_ifs with h
      · exact disjoint_empty_right _
      · rw [Finset.disjoint_singleton_right, mem_union, not_or]
        exact ⟨fun h' => (mem_setY.1 h').2.ne rfl |>.elim,
          fun h' => (mem_setP.1 h').2.1 rfl⟩
  · split_ifs with h
    · exact disjoint_empty_right _
    · rw [Finset.disjoint_singleton_right, mem_union, not_or]
      exact ⟨fun h' => (mem_setX.1 h').1.ne rfl |>.elim, fun h' => (mem_setP.1 h').1.1 rfl⟩

/-! ### Labels -/

variable (G w vs)

/-- The vertices that get labels: `v*`, `X`, `W`. -/
noncomputable def setH : Finset V := insert vs (setX G w vs ∪ setW G w)

/-- The modulus `N = 4|X| + 2|P| + 1`. -/
noncomputable def modN : ℕ := 4 * #(setX G w vs) + 2 * #(setP G w vs) + 1

/-- The labels. -/
noncomputable def label (v : V) : ℕ :=
  if v = vs then 0
  else if h : v ∈ setX G w vs then 2 * ((setX G w vs).equivFin ⟨v, h⟩ : ℕ) + 1
  else if h : v ∈ setY G w vs then 4 * ((setY G w vs).equivFin ⟨v, h⟩ : ℕ) + 2
  else if h : v ∈ setP G w vs then 4 * #(setX G w vs) + 1 + ((setP G w vs).equivFin ⟨v, h⟩ : ℕ)
  else 0

variable {G w vs}

theorem vs_notMem_X : vs ∉ setX G w vs := fun h => (mem_setX.1 h).2.1 rfl
theorem vs_notMem_Y : vs ∉ setY G w vs := fun h => (mem_setY.1 h).2.ne rfl
theorem vs_notMem_P : vs ∉ setP G w vs := fun h => (mem_setP.1 h).2.1 rfl
theorem X_notMem_Y {u : V} (h : u ∈ setX G w vs) : u ∉ setY G w vs := fun h' =>
  (mem_setY.1 h').1.2 (mem_setX.1 h).1
theorem X_notMem_P {u : V} (h : u ∈ setX G w vs) : u ∉ setP G w vs := fun h' =>
  (mem_setP.1 h').1.2 (mem_setX.1 h).1
theorem Y_notMem_P {u : V} (h : u ∈ setY G w vs) : u ∉ setP G w vs := fun h' =>
  (mem_setP.1 h').2.2 (mem_setY.1 h).2

theorem mem_setH {u : V} : u ∈ setH G w vs ↔
    u = vs ∨ u ∈ setX G w vs ∨ u ∈ setY G w vs ∨ u ∈ setP G w vs := by
  simp only [setH, mem_insert, mem_union, mem_setW, mem_setY, mem_setP]
  constructor
  · rintro (h | h | h)
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · by_cases hv : G.Adj vs u
      · exact Or.inr (Or.inr (Or.inl ⟨h, hv⟩))
      · by_cases he : u = vs
        · exact Or.inl he
        · exact Or.inr (Or.inr (Or.inr ⟨h, he, hv⟩))
  · rintro (h | h | h | h)
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr h.1)
    · exact Or.inr (Or.inr h.1)

theorem label_vs : label G w vs vs = 0 := by simp [label]

theorem label_X {u : V} (h : u ∈ setX G w vs) :
    label G w vs u = 2 * ((setX G w vs).equivFin ⟨u, h⟩ : ℕ) + 1 := by
  have hne : u ≠ vs := fun e => vs_notMem_X (e ▸ h)
  simp only [label, if_neg hne, dif_pos h]

theorem label_Y {u : V} (h : u ∈ setY G w vs) :
    label G w vs u = 4 * ((setY G w vs).equivFin ⟨u, h⟩ : ℕ) + 2 := by
  have hne : u ≠ vs := fun e => vs_notMem_Y (e ▸ h)
  have hX : u ∉ setX G w vs := fun hX => X_notMem_Y hX h
  simp only [label, if_neg hne, dif_neg hX, dif_pos h]

theorem label_P {u : V} (h : u ∈ setP G w vs) :
    label G w vs u = 4 * #(setX G w vs) + 1 + ((setP G w vs).equivFin ⟨u, h⟩ : ℕ) := by
  have hne : u ≠ vs := fun e => vs_notMem_P (e ▸ h)
  have hX : u ∉ setX G w vs := fun hX => X_notMem_P hX h
  have hY : u ∉ setY G w vs := fun hY => Y_notMem_P hY h
  simp only [label, if_neg hne, dif_neg hX, dif_neg hY, dif_pos h]

section Pair

variable (hXY : #(setX G w vs) = #(setY G w vs))
include hXY

theorem label_lt {u : V} (hu : u ∈ setH G w vs) : label G w vs u < modN G w vs := by
  rw [modN]
  rcases mem_setH.1 hu with rfl | h | h | h
  · rw [label_vs]; omega
  · rw [label_X h]; have := ((setX G w vs).equivFin ⟨u, h⟩).2; omega
  · rw [label_Y h]; have := ((setY G w vs).equivFin ⟨u, h⟩).2; omega
  · rw [label_P h]; have := ((setP G w vs).equivFin ⟨u, h⟩).2; omega

theorem label_injOn {u v : V} (hu : u ∈ setH G w vs) (hv : v ∈ setH G w vs)
    (h : label G w vs u = label G w vs v) : u = v := by
  rcases mem_setH.1 hu with rfl | hu | hu | hu <;> rcases mem_setH.1 hv with rfl | hv | hv | hv
  all_goals first
    | rfl
    | (simp only [label_vs, label_X, label_Y, label_P, *] at h; omega)
    | (have e : (((setX G w vs).equivFin ⟨u, hu⟩ : Fin _) : ℕ) =
          (((setX G w vs).equivFin ⟨v, hv⟩ : Fin _) : ℕ) := by
          rw [label_X hu, label_X hv] at h; omega
       exact congrArg Subtype.val ((setX G w vs).equivFin.injective (Fin.ext e)))
    | (have e : (((setY G w vs).equivFin ⟨u, hu⟩ : Fin _) : ℕ) =
          (((setY G w vs).equivFin ⟨v, hv⟩ : Fin _) : ℕ) := by
          rw [label_Y hu, label_Y hv] at h; omega
       exact congrArg Subtype.val ((setY G w vs).equivFin.injective (Fin.ext e)))
    | (have e : (((setP G w vs).equivFin ⟨u, hu⟩ : Fin _) : ℕ) =
          (((setP G w vs).equivFin ⟨v, hv⟩ : Fin _) : ℕ) := by
          rw [label_P hu, label_P hv] at h; omega
       exact congrArg Subtype.val ((setP G w vs).equivFin.injective (Fin.ext e)))

end Pair

end OneFactor
