/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module
public import RequestProject.S07V48.SeedCore
set_option maxHeartbeats 4000000 -- build option (original: -DmaxHeartbeats=1600000; raised)
set_option maxRecDepth 16384 -- build option (original: -DmaxRecDepth=8192; raised)
@[expose] public section

/-! The robust-route constants of the simultaneous sampler are fixed before
the decay rate of any additional weighted tests. Only the order threshold
depends on that rate. -/

open Finset Classical
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace S07V48
open TypedTriangle.SparseEdge TypedTriangle.ComponentRows S07V24 S07V25

theorem S07_layer12_ext_uniform_rate (c κ α q : ℝ) (h : ℕ)
    (hc : 0 < c) (hκ : 0 < κ) (hα : 0 < α)
    (hq : 0 < q) (hq1 : q ≤ 1) (hh : 6 ≤ h) :
    ∃ (t : ℕ) (a ε : ℝ), Odd t ∧ 3 ≤ t ∧ 0 < a ∧ 0 < ε ∧
      ∀ θx : ℝ, 0 < θx → ∃ n₀ : ℕ,
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
  refine ⟨m + 1, a, epsOf a q m,
    by simp only [hmdef, mOf]; exact hkodd.add_even even_two,
    by simp only [hmdef, mOf]; obtain ⟨j, hj⟩ := hkodd; omega, hapos,
    by simp only [epsOf]; positivity, ?_⟩
  intro θx hθx
  refine ⟨max (n0Of c κ) (n0X α q a h m θx), ?_⟩
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

#print axioms S07_layer12_ext_uniform_rate

/-- The native-component specialization retains the same robust-route
constants for every positive rate of the additional tests. -/
theorem S07_core_ext_uniform_rate (α q : ℝ) (h : ℕ)
    (hα : 0 < α) (hq : 0 < q) (hq1 : q ≤ 1) (hh : 6 ≤ h) :
    ∃ (t : ℕ) (a ε : ℝ), Odd t ∧ 3 ≤ t ∧ 0 < a ∧ 0 < ε ∧
      ∀ θx : ℝ, 0 < θx → ∃ n₀ : ℕ,
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
  obtain ⟨t, a, ε, ht, ht3, ha, hε, hmain⟩ :=
    S07_layer12_ext_uniform_rate α (kappaOf α h) α q h
      hα (kappaOf_pos hα h) hα hq hq1 hh
  refine ⟨t, a, ε, ht, ht3, ha, hε, ?_⟩
  intro θx hθx
  obtain ⟨n₀, hmainθ⟩ := hmain θx hθx
  refine ⟨max n₀ (n1Of α), ?_⟩
  intro V _ _ I G lab F hH3 hH4 hn ι _ hι E hE
  exact hmainθ V I G lab F hH3 hH4 (le_trans (le_max_left _ _) hn) (link G lab F)
    (activeComps G lab F) (fun v C => IsBip G lab F (v, C)) (colG G lab F)
    (activeComps_interface hα hH3 hH4 (le_trans (le_max_right _ _) hn)) ι hι E hE

#print axioms S07_core_ext_uniform_rate

/-- One sampled core with a raw seed profile of any later prescribed accuracy,
while its route budget is fixed in advance. -/
theorem S07_core_seed_uniform_rate (α q C : ℝ) (h : ℕ)
    (hα : 0 < α) (hq : 0 < q) (hq1 : q ≤ 1) (hh : 6 ≤ h) (hC : 0 < C) :
    ∃ (t : ℕ) (a ε : ℝ), Odd t ∧ 3 ≤ t ∧ 0 < a ∧ 0 < ε ∧
      ∀ δ : ℝ, 0 < δ → ∃ n₀ : ℕ,
      ∀ (V : Type) [Fintype V] [DecidableEq V] (I : Type) (G : SimpleGraph V) (lab : V → I)
        (F : Set (Multiset I)) (_ : CommonNbrCond G lab F α) (hH4 : HingeCond G lab F α h),
        n₀ ≤ Fintype.card V →
        ∀ φ : Finset V → ℝ, DiffuseSeed G lab F C φ →
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
            ∀ u v : V, G.Adj u v → |sampW G lab F φ W u v / q - 1| ≤ δ := by
  obtain ⟨t, a, ε, ht, ht3, ha, hε, hmain⟩ :=
    S07_core_ext_uniform_rate α q h hα hq hq1 hh
  refine ⟨t, a, ε, ht, ht3, ha, hε, ?_⟩
  intro δ hδ
  set δ' := min δ 1 with hδ'def
  have hδ' : 0 < δ' := lt_min hδ one_pos
  have hδ'1 : δ' ≤ 1 := min_le_right _ _
  have hδ'δ : δ' ≤ δ := min_le_left _ _
  have hθ : 0 < thetaSeed C q δ := by unfold thetaSeed; positivity
  obtain ⟨n₀, hmainθ⟩ := hmain (thetaSeed C q δ) hθ
  refine ⟨max n₀ 1, ?_⟩
  intro V _ _ I G lab F hH3 hH4 hn φ hφ
  have hn0 : 0 < Fintype.card V := lt_of_lt_of_le one_pos (le_trans (le_max_right _ _) hn)
  have hcard : Fintype.card (V × V × Bool) ≤ 2 * Fintype.card V ^ 2 := by
    simp only [Fintype.card_prod, Fintype.card_bool]; nlinarith
  obtain ⟨W, h1, h2, h3, h4, h5, h6⟩ := hmainθ V I G lab F hH3 hH4
    (le_trans (le_max_left _ _) hn)
    (V × V × Bool) hcard (seedBad G lab F φ q δ') (fun j => by
      have := seedBad_prob hφ hC hq hq1 hδ' hδ'1 hn0 j
      simpa only [thetaSeed, ← hδ'def] using this)
  exact ⟨W, h1, h2, h3, h4, h5,
    fun u v huv => (profile_of_not_bad hq h6 huv).trans hδ'δ⟩

#print axioms S07_core_seed_uniform_rate

end S07V48
