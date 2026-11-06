/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import CDR.ForbiddenGood

/-!
# Forbidden latin squares exist (Colbourn–Dinitz–Rosa, Lemma 2.3)

The two constructions of the paper for the array with placeholders (`GoodQ`), with
`d = a + b − c` placeholders:

* `a ≤ b` (`exists_goodQ_of_le`): a latin square of order `a + b` on the symbols `C ∪ X`
  containing, on `A × A`, a subsquare of order `a` whose symbols include all of `X`; it exists by
  Ryser's theorem since `a ≤ (a + b)/2`.
* `b ≤ a` (`exists_goodQ_of_ge`): cyclic rectangles on a set `C_a` of `a` symbols of `C` in
  `A × B` and `B × A`, and a cyclic latin square on `(C \ C_a) ∪ X` in `B × B`.

`exists_forbidden_latin` is the sufficiency part of Lemma 2.3: if `a, b ≤ c ≤ a + b`, an
`(a, b, c)`-forbidden latin square exists.
-/

@[expose] public section

namespace CDR

open Finset

variable {N : Type*} [Fintype N] [DecidableEq N]

/-- The trivial `GoodQ` when `A ∪ B` is empty. -/
theorem goodQ_of_all_C {lab : N → Fin 3} {d : ℕ} (h : ∀ x, lab x = 2) :
    GoodQ lab d (fun r _ => .inl r) := by
  have h0 : ∀ x, lab x ≠ 0 := fun x hx => absurd (hx.symm.trans (h x)) (by decide)
  have h1 : ∀ x, lab x ≠ 1 := fun x hx => absurd (hx.symm.trans (h x)) (by decide)
  exact ⟨fun r hr => absurd hr (h1 r), fun r hr => absurd hr (h0 r),
    fun g hg => absurd hg (h1 g), fun g hg => absurd hg (h0 g),
    fun r _ hr => absurd hr (h0 r), fun r _ hr => absurd hr (h1 r),
    fun r _ _ hr => absurd hr (h1 r), fun r hr => absurd hr (h1 r),
    fun g hg => absurd hg (h1 g), fun r hr => absurd hr (h1 r), fun g hg => absurd hg (h1 g)⟩

/-! ### The case `a ≤ b` -/

/-- An injection of `Fin a` into the symbols `C ⊕ X` whose range contains every placeholder,
when `d ≤ a ≤ c + d`. -/
theorem exists_subsquareSymbols {lab : N → Fin 3} {a d : ℕ} (hda : d ≤ a)
    (hac : a ≤ #(cls lab 2) + d) :
    ∃ s₀ : Fin a → {σ // lab σ = 2} ⊕ Fin d, Function.Injective s₀ ∧ ∀ x, ∃ i, s₀ i = .inr x := by
  let eC := classEquiv lab 2
  let cEmb : Fin (a - d) → {σ // lab σ = 2} := fun j => eC.symm (Fin.castLE (by omega) j)
  have hcEmb : Function.Injective cEmb := fun j j' h =>
    Fin.castLE_injective _ (eC.symm.injective h)
  refine ⟨fun i => if h : i.val < d then .inr ⟨i, h⟩ else .inl (cEmb ⟨i - d, by omega⟩),
    fun i i' h => ?_, fun x => ⟨⟨x, by omega⟩, by simp⟩⟩
  by_cases hi : i.val < d <;> by_cases hi' : i'.val < d <;> simp only [hi, hi', dite_true,
    dite_false, Sum.inr.injEq, Sum.inl.injEq, reduceCtorEq] at h
  · exact Fin.ext (by simpa using congrArg Fin.val h)
  · have := congrArg Fin.val (hcEmb h)
    simp at this
    exact Fin.ext (by omega)

theorem exists_goodQ_of_le {lab : N → Fin 3} (hab : #(cls lab 0) ≤ #(cls lab 1))
    (hbc : #(cls lab 1) ≤ #(cls lab 2)) (hc : #(cls lab 2) ≤ #(cls lab 0) + #(cls lab 1)) :
    ∃ Q, GoodQ lab (#(cls lab 0) + #(cls lab 1) - #(cls lab 2)) Q := by
  set a := #(cls lab 0)
  set b := #(cls lab 1)
  set c := #(cls lab 2)
  set d := a + b - c
  by_cases hall : ∀ x, lab x = 2
  · exact ⟨_, goodQ_of_all_C hall⟩
  push Not at hall
  obtain ⟨x₀, hx₀⟩ := hall
  let N' := {x : N // lab x ≠ 2}
  let Y := {σ : N // lab σ = 2} ⊕ Fin d
  have hN' : Fintype.card N' = a + b := by
    rw [Fintype.card_subtype, ← card_clsAB]
    rfl
  have hY : Fintype.card Y = Fintype.card N' := by
    rw [Fintype.card_sum, card_classSubtype, Fintype.card_fin, hN']
    omega
  haveI : Nonempty Y := Fintype.card_pos_iff.1 (hY ▸ Fintype.card_pos_iff.2 ⟨⟨x₀, hx₀⟩⟩)
  obtain ⟨s₀, hs₀, hs₀X⟩ := exists_subsquareSymbols (lab := lab) (a := a) (d := d) (by omega)
    (by omega)
  let eA := classEquiv lab 0
  let A' : Finset N' := univ.filter fun x => lab x.1 = 0
  let P₀ : N' → N' → Y := fun r g =>
    if h : lab r.1 = 0 ∧ lab g.1 = 0 then s₀ (eA ⟨r.1, h.1⟩ + eA ⟨g.1, h.2⟩)
    else Classical.arbitrary Y
  have hA' : ∀ {x : N'}, x ∈ A' ↔ lab x.1 = 0 := by simp [A']
  have hP₀ : ∀ {r g : N'} (hr : lab r.1 = 0) (hg : lab g.1 = 0),
      P₀ r g = s₀ (eA ⟨r.1, hr⟩ + eA ⟨g.1, hg⟩) := fun hr hg => by simp [P₀, hr, hg]
  have hlatin : IsLatinOn A' A' P₀ := by
    refine ⟨fun r hr g hg g' hg' h => ?_, fun g hg r hr r' hr' h => ?_⟩
    · rw [hA'] at hr
      rw [mem_coe, hA'] at hg hg'
      simp only [hP₀ hr hg, hP₀ hr hg'] at h
      exact Subtype.ext (Subtype.mk.inj (eA.injective (fin_add_left_inj _ (hs₀ h))))
    · rw [hA'] at hg
      rw [mem_coe, hA'] at hr hr'
      simp only [hP₀ hr hg, hP₀ hr' hg] at h
      exact Subtype.ext (Subtype.mk.inj (eA.injective (fin_add_right_inj _ (hs₀ h))))
  have hcond : RyserCond A' A' P₀ := by
    intro σ
    have : #A' = a := by
      rw [show a = Fintype.card {x // lab x = 0} from (card_classSubtype lab 0).symm]
      refine (card_bij (fun x hx => (⟨x.1, hA'.1 hx⟩ : {x // lab x = 0})) (fun _ _ => mem_univ _)
        (fun x _ y _ h => Subtype.ext (congrArg (fun z : {x // lab x = 0} => z.1) h)) ?_).trans
        (card_univ)
      intro y _
      exact ⟨⟨y.1, by rw [y.2]; decide⟩, hA'.2 y.2, rfl⟩
    rw [this, hN']
    omega
  obtain ⟨L, hL, hagree⟩ := ryser hY hlatin hcond
  let conv : Y → N ⊕ Fin d := Sum.map Subtype.val id
  have hconv : Function.Injective conv :=
    Sum.map_injective.2 ⟨Subtype.val_injective, Function.injective_id⟩
  let Q : N → N → N ⊕ Fin d := fun r g =>
    if h : lab r ≠ 2 ∧ lab g ≠ 2 then conv (L ⟨r, h.1⟩ ⟨g, h.2⟩) else .inl r
  have hQ : ∀ {r g} (hr : lab r ≠ 2) (hg : lab g ≠ 2), Q r g = conv (L ⟨r, hr⟩ ⟨g, hg⟩) :=
    fun hr hg => by simp [Q, hr, hg]
  have h02 : (0 : Fin 3) ≠ 2 := by decide
  have h12 : (1 : Fin 3) ≠ 2 := by decide
  -- every placeholder lies in each row and each column of `A` inside `A × A`
  have hrowX : ∀ (r : N') (hr : lab r.1 = 0) (x : Fin d), ∃ g : N', lab g.1 = 0 ∧
      L r g = .inr x := by
    intro r hr x
    obtain ⟨i, hi⟩ := hs₀X x
    obtain ⟨j, hj⟩ := fin_exists_add_left (eA ⟨r.1, hr⟩) i
    refine ⟨⟨(eA.symm j).1, by rw [(eA.symm j).2]; exact h02⟩, (eA.symm j).2, ?_⟩
    rw [hagree r (hA'.2 hr) _ (hA'.2 (eA.symm j).2), hP₀ hr (eA.symm j).2]
    simp [hj, hi]
  have hcolX : ∀ (g : N') (hg : lab g.1 = 0) (x : Fin d), ∃ r : N', lab r.1 = 0 ∧
      L r g = .inr x := by
    intro g hg x
    obtain ⟨i, hi⟩ := hs₀X x
    obtain ⟨j, hj⟩ := fin_exists_add_right (eA ⟨g.1, hg⟩) i
    refine ⟨⟨(eA.symm j).1, by rw [(eA.symm j).2]; exact h02⟩, (eA.symm j).2, ?_⟩
    rw [hagree _ (hA'.2 (eA.symm j).2) g (hA'.2 hg), hP₀ (eA.symm j).2 hg]
    simp [hj, hi]
  -- a cell of `A × B` or `B × A` holds a symbol of `C`
  have hnotX_row : ∀ (r g : N'), lab r.1 = 0 → lab g.1 = 1 → ∃ σ : {σ // lab σ = 2},
      L r g = .inl σ := by
    intro r g hr hg
    rcases hrg : L r g with σ | x
    · exact ⟨σ, rfl⟩
    · obtain ⟨g₀, hg₀, h⟩ := hrowX r hr x
      have := (hL.1 r).1 (hrg.trans h.symm)
      rw [this, hg₀] at hg
      exact absurd hg (by decide)
  have hnotX_col : ∀ (r g : N'), lab r.1 = 1 → lab g.1 = 0 → ∃ σ : {σ // lab σ = 2},
      L r g = .inl σ := by
    intro r g hr hg
    rcases hrg : L r g with σ | x
    · exact ⟨σ, rfl⟩
    · obtain ⟨r₀, hr₀, h⟩ := hcolX g hg x
      have := (hL.2 g).1 (hrg.trans h.symm)
      rw [this, hr₀] at hr
      exact absurd hr (by decide)
  refine ⟨Q, ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩⟩
  · intro r hr g g' hg hg' h
    rw [hQ (by rw [hr]; exact h12) hg, hQ (by rw [hr]; exact h12) hg'] at h
    exact congrArg Subtype.val ((hL.1 _).1 (hconv h))
  · intro r hr g g' hg hg' h
    rw [hQ (by rw [hr]; exact h02) (by rw [hg]; exact h12),
      hQ (by rw [hr]; exact h02) (by rw [hg']; exact h12)] at h
    exact congrArg Subtype.val ((hL.1 _).1 (hconv h))
  · intro g hg r r' hr hr' h
    rw [hQ hr (by rw [hg]; exact h12), hQ hr' (by rw [hg]; exact h12)] at h
    exact congrArg Subtype.val ((hL.2 _).1 (hconv h))
  · intro g hg r r' hr hr' h
    rw [hQ (by rw [hr]; exact h12) (by rw [hg]; exact h02),
      hQ (by rw [hr']; exact h12) (by rw [hg]; exact h02)] at h
    exact congrArg Subtype.val ((hL.2 _).1 (hconv h))
  · intro r g hr hg
    obtain ⟨σ, hσ⟩ := hnotX_row ⟨r, by rw [hr]; exact h02⟩ ⟨g, by rw [hg]; exact h12⟩ hr hg
    exact ⟨σ.1, σ.2, by rw [hQ (by rw [hr]; exact h02) (by rw [hg]; exact h12), hσ]; rfl⟩
  · intro r g hr hg
    obtain ⟨σ, hσ⟩ := hnotX_col ⟨r, by rw [hr]; exact h12⟩ ⟨g, by rw [hg]; exact h02⟩ hr hg
    exact ⟨σ.1, σ.2, by rw [hQ (by rw [hr]; exact h12) (by rw [hg]; exact h02), hσ]; rfl⟩
  · intro r g σ hr hg h
    rw [hQ (by rw [hr]; exact h12) (by rw [hg]; exact h12)] at h
    rcases hrg : L ⟨r, _⟩ ⟨g, _⟩ with τ | x <;> rw [hrg] at h
    · simp only [conv, Sum.map_inl, Sum.inl.injEq] at h
      rw [← h]
      exact τ.2
    · simp [conv] at h
  · intro r hr σ hσ
    obtain ⟨g, hg⟩ := (hL.1 ⟨r, by rw [hr]; exact h12⟩).2 (.inl ⟨σ, hσ⟩)
    exact ⟨g.1, g.2, by rw [hQ (by rw [hr]; exact h12) g.2]; simp [conv, hg]⟩
  · intro g hg σ hσ
    obtain ⟨r, hr⟩ := (hL.2 ⟨g, by rw [hg]; exact h12⟩).2 (.inl ⟨σ, hσ⟩)
    exact ⟨r.1, r.2, by rw [hQ r.2 (by rw [hg]; exact h12)]; simp [conv, hr]⟩
  · intro r hr x
    obtain ⟨g, hg⟩ := (hL.1 ⟨r, by rw [hr]; exact h12⟩).2 (.inr x)
    have hg1 : lab g.1 = 1 := by
      rcases fin3_cases (lab g.1) with h | h | h
      · obtain ⟨r₀, hr₀, h'⟩ := hcolX g h x
        have := (hL.2 g).1 (hg.trans h'.symm)
        rw [← this] at hr₀
        exact absurd (hr.symm.trans hr₀) (by decide)
      · exact h
      · exact absurd h g.2
    exact ⟨g.1, hg1, by rw [hQ (by rw [hr]; exact h12) g.2]; simp [conv, hg]⟩
  · intro g hg x
    obtain ⟨r, hr⟩ := (hL.2 ⟨g, by rw [hg]; exact h12⟩).2 (.inr x)
    have hr1 : lab r.1 = 1 := by
      rcases fin3_cases (lab r.1) with h | h | h
      · obtain ⟨g₀, hg₀, h'⟩ := hrowX r h x
        have := (hL.1 r).1 (hr.trans h'.symm)
        rw [← this] at hg₀
        exact absurd (hg.symm.trans hg₀) (by decide)
      · exact h
      · exact absurd h r.2
    exact ⟨r.1, hr1, by rw [hQ r.2 (by rw [hg]; exact h12)]; simp [conv, hr]⟩


/-! ### The case `b ≤ a` -/

theorem exists_goodQ_of_ge {lab : N → Fin 3} (hba : #(cls lab 1) ≤ #(cls lab 0))
    (hac : #(cls lab 0) ≤ #(cls lab 2)) (hc : #(cls lab 2) ≤ #(cls lab 0) + #(cls lab 1)) :
    ∃ Q, GoodQ lab (#(cls lab 0) + #(cls lab 1) - #(cls lab 2)) Q := by
  set a := #(cls lab 0)
  set b := #(cls lab 1)
  set c := #(cls lab 2)
  set d := a + b - c
  let eA := classEquiv lab 0
  let eB := classEquiv lab 1
  let eC := classEquiv lab 2
  -- the symbols `C_a`
  let cA : Fin a → N := fun i => (eC.symm (Fin.castLE hac i)).1
  have hcA : Function.Injective cA := fun i j h =>
    Fin.castLE_injective _ (eC.symm.injective (Subtype.ext h))
  have hcA2 : ∀ i, lab (cA i) = 2 := fun i => (eC.symm _).2
  -- the other symbols of `C`
  let K : Finset N := (cls lab 2).filter fun σ => ∀ i, cA i ≠ σ
  have hK : #K = c - a := by
    have hsplit : cls lab 2 = K ∪ univ.image cA := by
      ext σ
      simp only [K, mem_union, mem_filter, mem_image, mem_univ, true_and, mem_cls]
      constructor
      · intro h
        by_cases hσ : ∀ i, cA i ≠ σ
        · exact Or.inl ⟨h, hσ⟩
        · push Not at hσ
          exact Or.inr hσ
      · rintro (⟨h, -⟩ | ⟨i, rfl⟩)
        · exact h
        · exact hcA2 i
    have hdisj : Disjoint K (univ.image cA) := by
      rw [disjoint_left]
      intro σ h h'
      simp only [K, mem_filter] at h
      obtain ⟨i, -, rfl⟩ := mem_image.1 h'
      exact h.2 i rfl
    have := congrArg card hsplit
    rw [card_union_of_disjoint hdisj, card_image_of_injective _ hcA, card_univ,
      Fintype.card_fin] at this
    change c = #K + a at this
    omega
  let eK : {x // x ∈ K} ≃ Fin (c - a) := Fintype.equivFinOfCardEq (by rw [Fintype.card_coe, hK])
  have hb' : b = c - a + d := by omega
  let s₁ : Fin b → N ⊕ Fin d := fun i =>
    Sum.elim (fun j => .inl (eK.symm j).1) .inr (finSumFinEquiv.symm (Fin.cast hb' i))
  have hs₁ : Function.Injective s₁ := by
    intro i i' h
    simp only [s₁] at h
    have key : finSumFinEquiv.symm (Fin.cast hb' i) = finSumFinEquiv.symm (Fin.cast hb' i') := by
      rcases hx : finSumFinEquiv.symm (Fin.cast hb' i) with j | x <;>
        rcases hx' : finSumFinEquiv.symm (Fin.cast hb' i') with j' | x' <;>
        rw [hx, hx'] at h <;> simp only [Sum.elim_inl, Sum.elim_inr, Sum.inl.injEq,
          Sum.inr.injEq, reduceCtorEq] at h
      · rw [eK.symm.injective (Subtype.ext h)]
      · rw [h]
    exact Fin.cast_injective _ (finSumFinEquiv.symm.injective key)
  have hs₁K : ∀ {i σ}, s₁ i = .inl σ → σ ∈ K := by
    intro i σ h
    simp only [s₁] at h
    rcases hx : finSumFinEquiv.symm (Fin.cast hb' i) with j | x <;> rw [hx] at h <;>
      simp only [Sum.elim_inl, Sum.elim_inr, Sum.inl.injEq, reduceCtorEq] at h
    rw [← h]
    exact (eK.symm j).2
  have hs₁K' : ∀ σ ∈ K, ∃ i, s₁ i = .inl σ := by
    intro σ hσ
    refine ⟨Fin.cast hb'.symm (finSumFinEquiv (.inl (eK ⟨σ, hσ⟩))), ?_⟩
    simp [s₁]
  have hs₁X : ∀ x, ∃ i, s₁ i = .inr x := by
    intro x
    refine ⟨Fin.cast hb'.symm (finSumFinEquiv (.inr x)), ?_⟩
    simp [s₁]
  have hK2 : ∀ {σ}, σ ∈ K → lab σ = 2 := fun h => mem_cls.1 (mem_filter.1 h).1
  have hKcA : ∀ i, cA i ∉ K := fun i h => (mem_filter.1 h).2 i rfl
  let Q : N → N → N ⊕ Fin d := fun r g =>
    if h : lab r = 0 ∧ lab g = 1 then .inl (cA (eA ⟨r, h.1⟩ + Fin.castLE hba (eB ⟨g, h.2⟩)))
    else if h : lab r = 1 ∧ lab g = 0 then .inl (cA (Fin.castLE hba (eB ⟨r, h.1⟩) + eA ⟨g, h.2⟩))
    else if h : lab r = 1 ∧ lab g = 1 then s₁ (eB ⟨r, h.1⟩ + eB ⟨g, h.2⟩)
    else .inl r
  have hQab : ∀ {r g} (hr : lab r = 0) (hg : lab g = 1),
      Q r g = .inl (cA (eA ⟨r, hr⟩ + Fin.castLE hba (eB ⟨g, hg⟩))) := fun hr hg => by
    simp [Q, hr, hg]
  have hQba : ∀ {r g} (hr : lab r = 1) (hg : lab g = 0),
      Q r g = .inl (cA (Fin.castLE hba (eB ⟨r, hr⟩) + eA ⟨g, hg⟩)) := fun hr hg => by
    simp [Q, hr, hg]
  have hQbb : ∀ {r g} (hr : lab r = 1) (hg : lab g = 1),
      Q r g = s₁ (eB ⟨r, hr⟩ + eB ⟨g, hg⟩) := fun hr hg => by
    simp [Q, hr, hg]
  have hmix : ∀ {i j}, (Sum.inl (cA i) : N ⊕ Fin d) ≠ s₁ j := by
    intro i j h
    exact hKcA i (hs₁K h.symm)
  have hcases : ∀ {x}, lab x ≠ 2 → lab x = 0 ∨ lab x = 1 := fun {x} hx => by
    rcases fin3_cases (lab x) with h | h | h
    · exact Or.inl h
    · exact Or.inr h
    · exact absurd h hx
  have hvalA : ∀ {k} {x y : {x // lab x = k}}, x = y → x.1 = y.1 := fun h => by rw [h]
  refine ⟨Q, ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩⟩
  · intro r hr g g' hg hg' h
    rcases hcases hg with hg0 | hg1 <;> rcases hcases hg' with hg0' | hg1'
    · rw [hQba hr hg0, hQba hr hg0'] at h
      exact hvalA (eA.injective (fin_add_left_inj _ (hcA (Sum.inl_injective h))))
    · rw [hQba hr hg0, hQbb hr hg1'] at h
      exact absurd h hmix
    · rw [hQbb hr hg1, hQba hr hg0'] at h
      exact absurd h.symm hmix
    · rw [hQbb hr hg1, hQbb hr hg1'] at h
      exact hvalA (eB.injective (fin_add_left_inj _ (hs₁ h)))
  · intro r hr g g' hg hg' h
    rw [hQab hr hg, hQab hr hg'] at h
    exact hvalA (eB.injective (Fin.castLE_injective _
      (fin_add_left_inj _ (hcA (Sum.inl_injective h)))))
  · intro g hg r r' hr hr' h
    rcases hcases hr with hr0 | hr1 <;> rcases hcases hr' with hr0' | hr1'
    · rw [hQab hr0 hg, hQab hr0' hg] at h
      exact hvalA (eA.injective (fin_add_right_inj _ (hcA (Sum.inl_injective h))))
    · rw [hQab hr0 hg, hQbb hr1' hg] at h
      exact absurd h hmix
    · rw [hQbb hr1 hg, hQab hr0' hg] at h
      exact absurd h.symm hmix
    · rw [hQbb hr1 hg, hQbb hr1' hg] at h
      exact hvalA (eB.injective (fin_add_right_inj _ (hs₁ h)))
  · intro g hg r r' hr hr' h
    rw [hQba hr hg, hQba hr' hg] at h
    exact hvalA (eB.injective (Fin.castLE_injective _
      (fin_add_right_inj _ (hcA (Sum.inl_injective h)))))
  · intro r g hr hg
    exact ⟨_, hcA2 _, hQab hr hg⟩
  · intro r g hr hg
    exact ⟨_, hcA2 _, hQba hr hg⟩
  · intro r g σ hr hg h
    rw [hQbb hr hg] at h
    exact hK2 (hs₁K h)
  · intro r hr σ hσ
    by_cases hσK : σ ∈ K
    · obtain ⟨i, hi⟩ := hs₁K' σ hσK
      obtain ⟨j, hj⟩ := fin_exists_add_left (eB ⟨r, hr⟩) i
      refine ⟨(eB.symm j).1, by rw [(eB.symm j).2]; decide, ?_⟩
      rw [hQbb hr (eB.symm j).2]
      simp [hj, hi]
    · have : ∃ i, cA i = σ := by
        by_contra hno
        push Not at hno
        exact hσK (mem_filter.2 ⟨mem_cls.2 hσ, hno⟩)
      obtain ⟨i, rfl⟩ := this
      obtain ⟨j, hj⟩ := fin_exists_add_left (Fin.castLE hba (eB ⟨r, hr⟩)) i
      refine ⟨(eA.symm j).1, by rw [(eA.symm j).2]; decide, ?_⟩
      rw [hQba hr (eA.symm j).2]
      simp [hj]
  · intro g hg σ hσ
    by_cases hσK : σ ∈ K
    · obtain ⟨i, hi⟩ := hs₁K' σ hσK
      obtain ⟨j, hj⟩ := fin_exists_add_right (eB ⟨g, hg⟩) i
      refine ⟨(eB.symm j).1, by rw [(eB.symm j).2]; decide, ?_⟩
      rw [hQbb (eB.symm j).2 hg]
      simp [hj, hi]
    · have : ∃ i, cA i = σ := by
        by_contra hno
        push Not at hno
        exact hσK (mem_filter.2 ⟨mem_cls.2 hσ, hno⟩)
      obtain ⟨i, rfl⟩ := this
      obtain ⟨j, hj⟩ := fin_exists_add_right (Fin.castLE hba (eB ⟨g, hg⟩)) i
      refine ⟨(eA.symm j).1, by rw [(eA.symm j).2]; decide, ?_⟩
      rw [hQab (eA.symm j).2 hg]
      simp [hj]
  · intro r hr x
    obtain ⟨i, hi⟩ := hs₁X x
    obtain ⟨j, hj⟩ := fin_exists_add_left (eB ⟨r, hr⟩) i
    refine ⟨(eB.symm j).1, (eB.symm j).2, ?_⟩
    rw [hQbb hr (eB.symm j).2]
    simp [hj, hi]
  · intro g hg x
    obtain ⟨i, hi⟩ := hs₁X x
    obtain ⟨j, hj⟩ := fin_exists_add_right (eB ⟨g, hg⟩) i
    refine ⟨(eB.symm j).1, (eB.symm j).2, ?_⟩
    rw [hQbb (eB.symm j).2 hg]
    simp [hj, hi]

/-- **Colbourn–Dinitz–Rosa, Lemma 2.3 (sufficiency).** Let `N` be split into classes `A, B, C`
of sizes `a, b, c` with `c = max(a, b, c) ≤ n/2`, that is `a, b ≤ c ≤ a + b`. Then there is an
`(a, b, c)`-forbidden latin square on `N`. -/
theorem exists_forbidden_latin {lab : N → Fin 3} (ha : #(cls lab 0) ≤ #(cls lab 2))
    (hb : #(cls lab 1) ≤ #(cls lab 2)) (hc : #(cls lab 2) ≤ #(cls lab 0) + #(cls lab 1)) :
    ∃ L : N → N → N, IsForbiddenLatin lab L := by
  obtain ⟨Q, hQ⟩ : ∃ Q, GoodQ lab (#(cls lab 0) + #(cls lab 1) - #(cls lab 2)) Q :=
    (le_total #(cls lab 0) #(cls lab 1)).elim (fun h => exists_goodQ_of_le h hb hc)
      (fun h => exists_goodQ_of_ge h ha hc)
  obtain ⟨P, hP⟩ := goodArray_of_goodQ hQ (by omega)
  exact exists_forbidden_of_goodArray hP ha hb hc

end CDR
