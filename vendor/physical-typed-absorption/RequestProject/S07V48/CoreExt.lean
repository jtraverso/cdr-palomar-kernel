/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module
public import RequestProject.S07V25.CoreH3H4
public import RequestProject.S07V48.WeightedTail
@[expose] public section

/-!
# V48 — the S07 sampling proof with ADDITIONAL tests intersected into the SAME good event

`S07V24.random_core_H3H4` obtains its core `W` from ONE application of the finite union bound
`exists_good` to an explicit family of bad events (paths, H3 pools, H4 hinges, size). Here the
same proof is re-run with that family ENLARGED by an arbitrary host-dependent family `E j`
(`j ∈ ι`, `|ι| ≤ 2n²`) whose members each fail with probability `≤ exp(-θₓ n)`, where the rate
`θₓ > 0` is a constant fixed before the host. There is ONE union bound and ONE `W`: the extra
tests are not obtained by applying an existential core theorem twice.

* `thetaX`, `n0X` — the combined rate and threshold (constants only).
* `random_core_H3H4_ext` — `random_core_H3H4` + `∀ j, ¬ E j W`.
* `S07_layer12_ext` — `S07V24.S07_layer12` with the extra family.
* `S07_core_ext` — `S07V25.S07_core_H3H4` (native components, ORIGINAL H3/H4) with the extra
  family. Constants `t, a, ε, n₀` depend only on `(α, q, h, θₓ)`.
-/

open Finset

namespace S07V48

open TypedTriangle.SparseEdge TypedTriangle.ComponentRows S07V24 S07V25

/-- the combined decay rate -/
noncomputable def thetaX (α q a : ℝ) (h m : ℕ) (θx : ℝ) : ℝ := min (thetaH α q a h m) θx

/-- the combined threshold -/
noncomputable def n0X (α q a : ℝ) (h m : ℕ) (θx : ℝ) : ℕ := ⌈840 / thetaX α q a h m θx ^ 5⌉₊ + 1

/-- **S07 §2 with the original H3/H4 and an extra family of tests, ONE union bound** -/
theorem random_core_H3H4_ext (α q a θx : ℝ) (h m : ℕ) (hα : 0 < α) (hq : 0 < q) (hq1 : q ≤ 1)
    (ha : 0 < a) (hh : 6 ≤ h) (hm : 0 < m) (hθx : 0 < θx)
    {V I : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (lab : V → I) (F : Set (Multiset I))
    (hH3 : CommonNbrCond G lab F α) (hH4 : HingeCond G lab F α h)
    (hn : n0X α q a h m θx ≤ Fintype.card V)
    (L : V → SimpleGraph V) [∀ v, DecidableRel (L v).Adj]
    (adm : V → V → V → Prop)
    (hpaths : ∀ v x y, adm v x y →
      a * (Fintype.card V : ℝ) ^ m ≤ (pathsLen (L v) (m + 1) x y).card)
    (ι : Type*) [Fintype ι] (hι : Fintype.card ι ≤ 2 * Fintype.card V ^ 2)
    (E : ι → Finset V → Prop) [∀ j, DecidablePred (E j)]
    (hE : ∀ j, bprob q univ (E j) ≤ Real.exp (-(θx * Fintype.card V))) :
    ∃ W : Finset V,
      q * Fintype.card V / 2 ≤ W.card ∧ (W.card : ℝ) < 2 * q * Fintype.card V ∧
      (∀ u v : V, u ≠ v → ∀ k : I, ({lab u, lab v, k} : Multiset I) ∈ F →
        q * α * Fintype.card V / 2 ≤ ((commonNbrs G lab k u v) ∩ W).card) ∧
      (∀ u v a' b' : V, HingeTest G lab F u v a' b' →
        α * q ^ (hOrd hH4 u v a' b' - 4) * (Fintype.card V : ℝ) ^ (hOrd hH4 u v a' b' - 4) / 2 ≤
          ((hinges G lab F u v a' b' (hOrd hH4 u v a' b')).filter fun J =>
            freeV u v a' b' J ⊆ W).card) ∧
      (∀ v x y, adm v x y →
        a * q ^ m * (Fintype.card V : ℝ) ^ m / 2 ≤ (pathsIn (L v) m x y W).card) ∧
      ∀ j, ¬ E j W := by
  classical
  set n := Fintype.card V with hndef
  set θ := thetaX α q a h m θx with hθdef
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have hhR : (0 : ℝ) < h := by have : 0 < h := by omega
                               exact_mod_cast this
  have t1 : 0 < a * q ^ (2 * m) / (16 * m ^ 2) := by positivity
  have t2 : 0 < α * q ^ 2 / 16 := by positivity
  have t3 : 0 < α * q ^ (2 * h) / (16 * 2 ^ (h.choose 2) * h) := by positivity
  have t4 : 0 < q ^ 2 / 16 := by positivity
  have hθHpos : 0 < thetaH α q a h m := lt_min t1 (lt_min t2 (lt_min t3 t4))
  have hθpos : 0 < θ := lt_min hθHpos hθx
  have hθH : θ ≤ thetaH α q a h m := min_le_left _ _
  have hθX : θ ≤ θx := min_le_right _ _
  have hθ1 : θ ≤ a * q ^ (2 * m) / (16 * m ^ 2) := hθH.trans (min_le_left _ _)
  have hθ2 : θ ≤ α * q ^ 2 / 16 := hθH.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hθ3 : θ ≤ α * q ^ (2 * h) / (16 * 2 ^ (h.choose 2) * h) :=
    hθH.trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))
  have hθ4 : θ ≤ q ^ 2 / 16 :=
    hθH.trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _)))
  have hnθ : 120 * 7 / θ ^ 5 < n := by
    have := Nat.le_ceil (840 / θ ^ 5)
    have h2 : ((n0X α q a h m θx : ℕ) : ℝ) ≤ n := by exact_mod_cast hn
    unfold n0X at h2; push_cast at h2; rw [← hθdef] at h2; linarith
  have hnR : (0 : ℝ) < n := lt_trans (by positivity) hnθ
  have hn0 : 0 < n := by exact_mod_cast hnR
  have hq0 := hq.le
  have hexpmono : ∀ t : ℝ, θ ≤ t → Real.exp (-(t * n)) ≤ Real.exp (-(θ * n)) := fun t ht =>
    Real.exp_le_exp.2 (by nlinarith)
  -- the bad events: the V24 family enlarged by the extra tests
  let Idx := (V × V × V) ⊕ ((V × V × V) ⊕ ((V × V × V × V) ⊕ (Bool ⊕ ι)))
  let bad : Idx → Finset V → Prop := fun j W => match j with
    | Sum.inl (v, x, y) => adm v x y ∧
        ((pathsIn (L v) m x y W).card : ℝ) < a * (n : ℝ) ^ m * q ^ m / 2
    | Sum.inr (Sum.inl (u, v, w)) => (u ≠ v ∧ ({lab u, lab v, lab w} : Multiset I) ∈ F) ∧
        (((commonNbrs G lab (lab w) u v) ∩ W).card : ℝ) < α * n * q ^ 1 / 2
    | Sum.inr (Sum.inr (Sum.inl (u, v, a', b'))) => HingeTest G lab F u v a' b' ∧
        (((hinges G lab F u v a' b' (hOrd hH4 u v a' b')).filter fun J =>
            freeV u v a' b' J ⊆ W).card : ℝ) <
          α * (n : ℝ) ^ (hOrd hH4 u v a' b' - 4) * q ^ (hOrd hH4 u v a' b' - 4) / 2
    | Sum.inr (Sum.inr (Sum.inr (Sum.inl true))) => (W.card : ℝ) < n * q ^ 1 / 2
    | Sum.inr (Sum.inr (Sum.inr (Sum.inl false))) => q * n + q * n ≤ (W.card : ℝ)
    | Sum.inr (Sum.inr (Sum.inr (Sum.inr j))) => E j W
  have hE' : ∀ j, bprob q univ (bad j) ≤ Real.exp (-(θ * n)) := by
    intro j
    rcases j with ⟨v, x, y⟩ | ⟨u, v, w⟩ | ⟨u, v, a', b'⟩ | b | j
    · by_cases hadm : adm v x y
      · refine (bprob_mono hq0 hq1 (E := bad (Sum.inl (v, x, y))) (E' := fun W =>
          ((pathsIn (L v) m x y W).card : ℝ) < a * (n : ℝ) ^ m * q ^ m / 2)
          (iE' := fun W => inferInstance) (fun W h => h.2)).trans ?_
        exact (fam_paths ha hq hq1 hm hn0 (L v) x y (hpaths v x y hadm)).trans (hexpmono _ hθ1)
      · rw [bprob_false (E := bad (Sum.inl (v, x, y))) (fun W h => hadm h.1)]
        exact (Real.exp_pos _).le
    · by_cases hc : u ≠ v ∧ ({lab u, lab v, lab w} : Multiset I) ∈ F
      · refine (bprob_mono hq0 hq1 (E := bad (Sum.inr (Sum.inl (u, v, w)))) (E' := fun W =>
          (((commonNbrs G lab (lab w) u v) ∩ W).card : ℝ) < α * n * q ^ 1 / 2)
          (iE' := fun W => inferInstance) (fun W h => h.2)).trans ?_
        exact (fam_pool hq hq1 _ (hH3 u v hc.1 (lab w) hc.2)).trans (hexpmono _ hθ2)
      · rw [bprob_false (E := bad (Sum.inr (Sum.inl (u, v, w)))) (fun W h => hc h.1)]
        exact (Real.exp_pos _).le
    · by_cases ht : HingeTest G lab F u v a' b'
      · obtain ⟨h6, hle, hcnt⟩ := hOrd_spec hH4 ht
        refine (bprob_mono hq0 hq1 (E := bad (Sum.inr (Sum.inr (Sum.inl (u, v, a', b')))))
          (E' := fun W => (((hinges G lab F u v a' b' (hOrd hH4 u v a' b')).filter fun J =>
            freeV u v a' b' J ⊆ W).card : ℝ) <
              α * (n : ℝ) ^ (hOrd hH4 u v a' b' - 4) * q ^ (hOrd hH4 u v a' b' - 4) / 2)
          (iE' := fun W => inferInstance) (fun W h => h.2)).trans ?_
        exact (fam_hinge hα hq hq1 hn0 (roots_distinct ht) h6 hle hcnt).trans (hexpmono _ hθ3)
      · rw [bprob_false (E := bad (Sum.inr (Sum.inr (Sum.inl (u, v, a', b')))))
          (fun W h => ht h.1)]
        exact (Real.exp_pos _).le
    · cases b
      · refine (bprob_mono hq0 hq1 (E := bad (Sum.inr (Sum.inr (Sum.inr (Sum.inl false)))))
          (E' := fun W => q * n + q * n ≤ (W.card : ℝ))
          (iE' := fun W => inferInstance) (fun W h => h)).trans ?_
        exact (fam_size_hi hq hq1).trans (hexpmono _ (by nlinarith))
      · refine (bprob_mono hq0 hq1 (E := bad (Sum.inr (Sum.inr (Sum.inr (Sum.inl true)))))
          (E' := fun W => (W.card : ℝ) < n * q ^ 1 / 2)
          (iE' := fun W => inferInstance) (fun W h => h)).trans ?_
        exact (fam_size_lo hq hq1).trans (hexpmono _ hθ4)
    · refine (bprob_mono hq0 hq1 (E := bad (Sum.inr (Sum.inr (Sum.inr (Sum.inr j)))))
        (E' := E j) (iE' := inferInstance) (fun W h => h)).trans ?_
      exact (hE j).trans (hexpmono _ hθX)
  have hsum : ∑ j : Idx, bprob q univ (bad j) < 1 := by
    calc ∑ j : Idx, bprob q univ (bad j) ≤ ∑ _j : Idx, Real.exp (-(θ * n)) :=
          Finset.sum_le_sum fun j _ => hE' j
      _ = Fintype.card Idx * Real.exp (-(θ * n)) := by
          rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      _ ≤ 7 * (n : ℝ) ^ 4 * Real.exp (-(θ * n)) := by
          apply mul_le_mul_of_nonneg_right _ (Real.exp_pos _).le
          have hc : Fintype.card Idx = n ^ 3 + (n ^ 3 + (n ^ 4 + (2 + Fintype.card ι))) := by
            simp only [Idx, Fintype.card_sum, Fintype.card_prod, Fintype.card_bool, ← hndef]; ring
          rw [hc]; push_cast
          have hn1R : (1 : ℝ) ≤ n := by exact_mod_cast hn0
          have hιR : (Fintype.card ι : ℝ) ≤ 2 * (n : ℝ) ^ 2 := by exact_mod_cast hι
          have h3 : (n : ℝ) ^ 3 ≤ (n : ℝ) ^ 4 := pow_le_pow_right₀ hn1R (by norm_num)
          have h2 : (n : ℝ) ^ 2 ≤ (n : ℝ) ^ 4 := pow_le_pow_right₀ hn1R (by norm_num)
          have h4 : (1 : ℝ) ≤ (n : ℝ) ^ 4 := one_le_pow₀ hn1R
          linarith
      _ < 1 := exp_beats_poly hθpos (by norm_num) hnθ
  obtain ⟨W, -, hW⟩ := exists_good hq0 hq1 univ univ bad hsum
  refine ⟨W, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · have := hW (Sum.inr (Sum.inr (Sum.inr (Sum.inl true)))) (mem_univ _)
    simp only [bad, not_lt] at this; linarith
  · have := hW (Sum.inr (Sum.inr (Sum.inr (Sum.inl false)))) (mem_univ _)
    simp only [bad, not_le] at this; linarith
  · intro u v huv k hk
    have hpool := hH3 u v huv k hk
    obtain ⟨w, hw⟩ : (commonNbrs G lab k u v).Nonempty := by
      rw [← Finset.card_pos]
      have : (0 : ℝ) < (commonNbrs G lab k u v).card := lt_of_lt_of_le (by positivity) hpool
      exact_mod_cast this
    have hlw : lab w = k := by
      simp only [commonNbrs, Finset.mem_filter] at hw; exact hw.2.2.2
    have := hW (Sum.inr (Sum.inl (u, v, w))) (mem_univ _)
    simp only [bad, not_and, not_lt] at this
    have := this ⟨huv, by rw [hlw]; exact hk⟩
    rw [hlw] at this; linarith
  · intro u v a' b' ht
    have := hW (Sum.inr (Sum.inr (Sum.inl (u, v, a', b')))) (mem_univ _)
    simp only [bad, not_and, not_lt] at this
    have := this ht; linarith
  · intro v x y hadm
    have := hW (Sum.inl (v, x, y)) (mem_univ _)
    simp only [bad, not_and, not_lt] at this; have := this hadm; linarith
  · intro j
    exact hW (Sum.inr (Sum.inr (Sum.inr (Sum.inr j)))) (mem_univ _)

/-- **S07 §§1–2 composed, with an extra family on the same event** -/
theorem S07_layer12_ext (c κ α q θx : ℝ) (h : ℕ) (hc : 0 < c) (hκ : 0 < κ) (hα : 0 < α)
    (hq : 0 < q) (hq1 : q ≤ 1) (hh : 6 ≤ h) (hθx : 0 < θx) :
    ∃ (t : ℕ) (a ε : ℝ) (n₀ : ℕ), Odd t ∧ 3 ≤ t ∧ 0 < a ∧ 0 < ε ∧
      ∀ (V : Type) [Fintype V] [DecidableEq V] (I : Type) (G : SimpleGraph V) (lab : V → I)
        (F : Set (Multiset I)) (_ : CommonNbrCond G lab F α) (hH4 : HingeCond G lab F α h),
        n₀ ≤ Fintype.card V →
        ∀ (L : V → SimpleGraph V) [∀ v, DecidableRel (L v).Adj]
          (comps : V → Finset (Finset V)) (bip : V → Finset V → Prop) (col : V → V → Bool),
          (∀ v, ∀ C ∈ comps v, CompInterface (L v) c κ (Fintype.card V) C (bip v C) (col v)) →
        ∀ (ι : Type) [Fintype ι], Fintype.card ι ≤ 2 * Fintype.card V ^ 2 →
        ∀ (E : ι → Finset V → Prop) [∀ j, DecidablePred (E j)],
          (∀ j, bprob q univ (E j) ≤ Real.exp (-(θx * Fintype.card V))) →
          ∃ W : Finset V,
            q * Fintype.card V / 2 ≤ W.card ∧ (W.card : ℝ) < 2 * q * Fintype.card V ∧
            (∀ u v : V, u ≠ v → ∀ k : I, ({lab u, lab v, k} : Multiset I) ∈ F →
              q * α * Fintype.card V / 2 ≤ ((commonNbrs G lab k u v) ∩ W).card) ∧
            (∀ u v a' b' : V, HingeTest G lab F u v a' b' →
              α * q ^ (hOrd hH4 u v a' b' - 4) *
                  (Fintype.card V : ℝ) ^ (hOrd hH4 u v a' b' - 4) / 2 ≤
                ((hinges G lab F u v a' b' (hOrd hH4 u v a' b')).filter fun J =>
                  freeV u v a' b' J ⊆ W).card) ∧
            (∀ (Z : Finset V) (B : SimpleGraph V) [DecidableRel B.Adj] (d : ℕ),
              (Z.card : ℝ) ≤ ε * Fintype.card V → (∀ u, B.degree u ≤ d) →
              (d : ℝ) ≤ ε * Fintype.card V →
              ∀ v x y, AdmPair comps bip col v x y →
                ∃ p ∈ pathsLen (L v) t x y, intlSet (t - 1) p ⊆ W ∧
                  (∀ i : Fin (t - 1), intl (t - 1) p i ∉ Z) ∧
                  ∀ k < t, ¬ B.Adj (p.getVert k) (p.getVert (k + 1))) ∧
            ∀ j, ¬ E j W := by
  obtain ⟨hkodd, -⟩ := kOf_spec hc hκ
  set m := mOf c κ with hmdef
  set a := aOf c κ with hadef
  have hm : 0 < m := by simp [hmdef, mOf]
  have hapos : 0 < a := by
    have : 0 < min c 1 := lt_min hc one_pos
    simp only [hadef, aOf]; positivity
  refine ⟨m + 1, a, epsOf a q m, max (n0Of c κ) (n0X α q a h m θx),
    by simp only [hmdef, mOf]; exact hkodd.add_even even_two,
    by simp only [hmdef, mOf]; obtain ⟨j, hj⟩ := hkodd; omega, hapos,
    by simp only [epsOf]; positivity, ?_⟩
  intro V _ _ I G lab F hH3 hH4 hn L _ comps bip col hI ι _ hι E _ hE
  set n := Fintype.card V with hndef
  have hn1 : n0Of c κ ≤ n := le_trans (le_max_left _ _) hn
  have hn2 : n0X α q a h m θx ≤ n := le_trans (le_max_right _ _) hn
  have hpaths : ∀ v x y, AdmPair comps bip col v x y →
      a * (n : ℝ) ^ m ≤ (pathsLen (L v) (m + 1) x y).card := by
    rintro v x y ⟨C, hC, hx, hy, hxy, hcol⟩
    exact link_paths_of_interface c κ hc hκ (L v) n hn1 rfl C (bip v C) (col v) (hI v C hC)
      x y hx hy hxy hcol
  obtain ⟨W, h1, h2, h3, h4, h5, h6⟩ := random_core_H3H4_ext α q a θx h m hα hq hq1 hapos hh hm
    hθx G lab F hH3 hH4 hn2 L (AdmPair comps bip col) hpaths ι hι E hE
  refine ⟨W, h1, h2, h3, h4, ?_, h6⟩
  intro Z B _ d hZ hB hd v x y hadm
  have hnpos : 0 < n := by
    have : 0 < n0X α q a h m θx := Nat.succ_pos _
    omega
  have hwin := window_ok hapos hq hm hnpos Z d hZ hd
  obtain ⟨p, hp, hW, hZ', hB'⟩ := pay_deterministic (L v) m x y W (h5 v x y hadm) Z B d hB
    (by rw [← hndef]; exact hwin)
  exact ⟨p, hp, by simpa using hW, by simpa using hZ', by simpa using hB'⟩

open Classical in
/-- **ONE robust core from the ORIGINAL H3/H4 (native components), with an extra family of
tests intersected into the same good event** -/
theorem S07_core_ext (α q θx : ℝ) (h : ℕ) (hα : 0 < α) (hq : 0 < q) (hq1 : q ≤ 1) (hh : 6 ≤ h)
    (hθx : 0 < θx) :
    ∃ (t : ℕ) (a ε : ℝ) (n₀ : ℕ), Odd t ∧ 3 ≤ t ∧ 0 < a ∧ 0 < ε ∧
      ∀ (V : Type) [Fintype V] [DecidableEq V] (I : Type) (G : SimpleGraph V) (lab : V → I)
        (F : Set (Multiset I)) (_ : CommonNbrCond G lab F α) (hH4 : HingeCond G lab F α h),
        n₀ ≤ Fintype.card V →
        ∀ (ι : Type) [Fintype ι], Fintype.card ι ≤ 2 * Fintype.card V ^ 2 →
        ∀ (E : ι → Finset V → Prop),
          (∀ j, bprob q univ (E j) ≤ Real.exp (-(θx * Fintype.card V))) →
          ∃ W : Finset V,
            q * Fintype.card V / 2 ≤ W.card ∧ (W.card : ℝ) < 2 * q * Fintype.card V ∧
            (∀ u v : V, u ≠ v → ∀ k : I, ({lab u, lab v, k} : Multiset I) ∈ F →
              q * α * Fintype.card V / 2 ≤ ((commonNbrs G lab k u v) ∩ W).card) ∧
            (∀ u v a' b' : V, HingeTest G lab F u v a' b' →
              α * q ^ (hOrd hH4 u v a' b' - 4) *
                  (Fintype.card V : ℝ) ^ (hOrd hH4 u v a' b' - 4) / 2 ≤
                ((hinges G lab F u v a' b' (hOrd hH4 u v a' b')).filter fun J =>
                  freeV u v a' b' J ⊆ W).card) ∧
            (∀ (Z : Finset V) (B : SimpleGraph V) [DecidableRel B.Adj] (d : ℕ),
              (Z.card : ℝ) ≤ ε * Fintype.card V → (∀ u, B.degree u ≤ d) →
              (d : ℝ) ≤ ε * Fintype.card V →
              ∀ v x y, AdmPair (activeComps G lab F) (fun v C => IsBip G lab F (v, C))
                  (colG G lab F) v x y →
                ∃ p ∈ pathsLen (link G lab F v) t x y, intlSet (t - 1) p ⊆ W ∧
                  (∀ i : Fin (t - 1), intl (t - 1) p i ∉ Z) ∧
                  ∀ k < t, ¬ B.Adj (p.getVert k) (p.getVert (k + 1))) ∧
            ∀ j, ¬ E j W := by
  obtain ⟨t, a, ε, n₀, ht, ht3, ha, hε, hmain⟩ :=
    S07_layer12_ext α (kappaOf α h) α q θx h hα (kappaOf_pos hα h) hα hq hq1 hh hθx
  refine ⟨t, a, ε, max n₀ (n1Of α), ht, ht3, ha, hε, ?_⟩
  intro V _ _ I G lab F hH3 hH4 hn ι _ hι E hE
  exact hmain V I G lab F hH3 hH4 (le_trans (le_max_left _ _) hn) (link G lab F)
    (activeComps G lab F) (fun v C => IsBip G lab F (v, C)) (colG G lab F)
    (activeComps_interface hα hH3 hH4 (le_trans (le_max_right _ _) hn)) ι hι E hE

end S07V48
