/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import RequestProject.S07.Families
public import RequestProject.S10K.HingeCount

@[expose] public section

/-!
# V24 / S07 §2 (last paragraphs): the same core preserves the ORIGINAL hinges and pools

The hinges are the ORIGINAL objects of `SparseEdgeDefs.lean` (`hinges G lab F u v a b i`,
DISTINCT edge sets, four fixed roots, normalisation `n^(i-4)`), supplied by the ORIGINAL
`HingeCond` (H4). Pools are the ORIGINAL common-neighbour sets of `CommonNbrCond` (H3).

* `freeV` — the `i - 4` free vertices of a hinge (`support J` minus the four roots).
* `hOrd` — the order `i` of H4, FIXED from the roots before sampling.
* `fam_hinge` — one hinge test fails (fewer than `α q^(i-4) n^(i-4) / 2` hinges with all free
  vertices in `W`) with probability `≤ exp(-(α q^(2h) / (16 · 2^(h choose 2) · h)) n)`.
* `hinge_delete` — deterministic: deleting any `S` afterwards loses at most
  `|S| 2^(i choose 2) n^(i-5)` of them.
* `random_core_H3H4` — ONE `W` preserving simultaneously: `|W| ∈ [qn/2, 2qn)`, all H3 pools
  (`|commonNbrs ∩ W| ≥ qαn/2`), all H4 hinge supplies at the fixed order, and all admissible
  path tests of S07 (1.1) (`≥ a q^m n^m / 2` paths inside `W`). At most `5 n^4` tests.

No new seed and no divisibility of the induced core are asserted. H3/H4 are used exactly as
stated in `SparseEdgeDefs.lean`.
-/

open Finset

namespace S07V24

open TypedTriangle.SparseEdge

variable {V I : Type*} [Fintype V] [DecidableEq V]

/-- free vertices of a hinge with roots `u v a b` -/
noncomputable def freeV (u v a b : V) (J : Finset (Sym2 V)) : Finset V := support J \ {u, v, a, b}

/-- the pair of allowed triangles `uva`, `uvb` of an H4 test -/
def HingeTest (G : SimpleGraph V) (lab : V → I) (F : Set (Multiset I)) (u v a b : V) : Prop :=
  a ≠ b ∧ IsAllowed G lab F {u, v, a} ∧ IsAllowed G lab F {u, v, b}

omit [Fintype V] in
lemma distinct_of_allowed {G : SimpleGraph V} {lab : V → I} {F : Set (Multiset I)} {x y z : V}
    (h : IsAllowed G lab F {x, y, z}) : x ≠ y ∧ x ≠ z ∧ y ≠ z := by
  have h3 := h.1
  refine ⟨fun hxy => ?_, fun hxz => ?_, fun hyz => ?_⟩
  · subst hxy; simp only [Finset.insert_eq_of_mem (Finset.mem_insert_self _ _)] at h3
    have := Finset.card_le_two (a := x) (b := z); omega
  · subst hxz
    have : ({x, y, x} : Finset V) = {x, y} := by ext; simp; tauto
    rw [this] at h3; have := Finset.card_le_two (a := x) (b := y); omega
  · subst hyz
    have : ({x, y, y} : Finset V) = {x, y} := by ext; simp
    rw [this] at h3; have := Finset.card_le_two (a := x) (b := y); omega

omit [Fintype V] in
lemma roots_distinct {G : SimpleGraph V} {lab : V → I} {F : Set (Multiset I)} {u v a b : V}
    (ht : HingeTest G lab F u v a b) :
    u ≠ v ∧ u ≠ a ∧ v ≠ a ∧ u ≠ b ∧ v ≠ b ∧ a ≠ b := by
  obtain ⟨hab, h1, h2⟩ := ht
  obtain ⟨huv, hua, hva⟩ := distinct_of_allowed h1
  obtain ⟨-, hub, hvb⟩ := distinct_of_allowed h2
  exact ⟨huv, hua, hva, hub, hvb, hab⟩

/-- the H4 order, fixed from the roots -/
noncomputable def hOrd {G : SimpleGraph V} {lab : V → I} {F : Set (Multiset I)} {α : ℝ} {h : ℕ}
    (hH4 : HingeCond G lab F α h) (u v a b : V) : ℕ := by
  classical
  exact if ht : HingeTest G lab F u v a b then
    Classical.choose (hH4 u v a b ht.1 (by convert ht.2.1) (by convert ht.2.2)) else 6

lemma hOrd_spec {G : SimpleGraph V} {lab : V → I} {F : Set (Multiset I)} {α : ℝ} {h : ℕ}
    (hH4 : HingeCond G lab F α h) {u v a b : V} (ht : HingeTest G lab F u v a b) :
    6 ≤ hOrd hH4 u v a b ∧ hOrd hH4 u v a b ≤ h ∧
      α * (Fintype.card V : ℝ) ^ (hOrd hH4 u v a b - 4) ≤
        (hinges G lab F u v a b (hOrd hH4 u v a b)).card := by
  classical
  unfold hOrd
  rw [dif_pos ht]
  exact Classical.choose_spec (hH4 u v a b ht.1 (by convert ht.2.1) (by convert ht.2.2))

lemma card_freeV {G : SimpleGraph V} {lab : V → I} {F : Set (Multiset I)} {u v a b : V}
    (hd : u ≠ v ∧ u ≠ a ∧ v ≠ a ∧ u ≠ b ∧ v ≠ b ∧ a ≠ b) {i : ℕ} {J : Finset (Sym2 V)}
    (hJ : J ∈ hinges G lab F u v a b i) : (freeV u v a b J).card = i - 4 := by
  obtain ⟨huv, hua, hva, hub, hvb, hab⟩ := hd
  have hmem : IsHinge G lab F u v a b J ∧ (support J).card = i := by
    simpa [hinges] using hJ
  have hsub := S10V23.roots_subset_support' hmem.1 huv hua hva hub hvb
  have hR : ({u, v, a, b} : Finset V).card = 4 := by
    rw [Finset.card_insert_of_notMem (by simp [huv, hua, hub]),
      Finset.card_insert_of_notMem (by simp [hva, hvb]),
      Finset.card_insert_of_notMem (by simp [hab]), Finset.card_singleton]
  unfold freeV
  rw [Finset.card_sdiff_of_subset hsub, hmem.2, hR]

lemma hinge_free_deg {G : SimpleGraph V} {lab : V → I} {F : Set (Multiset I)} {u v a b : V}
    (hd : u ≠ v ∧ u ≠ a ∧ v ≠ a ∧ u ≠ b ∧ v ≠ b ∧ a ≠ b) (i : ℕ) (z : V) :
    (((hinges G lab F u v a b i).filter fun J => z ∈ freeV u v a b J).card : ℝ) ≤
      2 ^ (i.choose 2) * (Fintype.card V : ℝ) ^ (i - 5) := by
  obtain ⟨huv, hua, hva, hub, hvb, hab⟩ := hd
  by_cases hz : z ∈ ({u, v, a, b} : Finset V)
  · have : ((hinges G lab F u v a b i).filter fun J => z ∈ freeV u v a b J) = ∅ := by
      apply Finset.filter_false_of_mem; intro J _ hJ
      simp only [freeV, Finset.mem_sdiff] at hJ; exact hJ.2 hz
    rw [this]; simp only [Finset.card_empty, Nat.cast_zero]; positivity
  · have := S10V23.card_hinges_forced huv hua hva hub hvb hab i {z}
      (Finset.disjoint_singleton_left.2 hz)
      ((hinges G lab F u v a b i).filter fun J => z ∈ freeV u v a b J) (Finset.filter_subset _ _)
      (fun J hJ => by
        simp only [Finset.mem_filter, freeV, Finset.mem_sdiff] at hJ
        exact Finset.singleton_subset_iff.2 hJ.2.1)
    simpa using this

/-- **one hinge test** under the full finite process -/
theorem fam_hinge {G : SimpleGraph V} {lab : V → I} {F : Set (Multiset I)} {α q : ℝ} {h : ℕ}
    (hα : 0 < α) (hq : 0 < q) (hq1 : q ≤ 1) (hn : 0 < Fintype.card V) {u v a b : V}
    (hd : u ≠ v ∧ u ≠ a ∧ v ≠ a ∧ u ≠ b ∧ v ≠ b ∧ a ≠ b) {i : ℕ} (hi6 : 6 ≤ i) (hih : i ≤ h)
    (hcount : α * (Fintype.card V : ℝ) ^ (i - 4) ≤ (hinges G lab F u v a b i).card) :
    bprob q univ (fun W => (((hinges G lab F u v a b i).filter fun J =>
        freeV u v a b J ⊆ W).card : ℝ) < α * (Fintype.card V : ℝ) ^ (i - 4) * q ^ (i - 4) / 2) ≤
      Real.exp (-(α * q ^ (2 * h) / (16 * 2 ^ (h.choose 2) * h) * Fintype.card V)) := by
  set n := Fintype.card V
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hr : 0 < i - 4 := by omega
  have ht := count_tail hq hq1 (hinges G lab F u v a b i) (freeV u v a b) hr
    (fun J hJ => (card_freeV hd hJ).le) (Δ := 2 ^ (i.choose 2) * (n : ℝ) ^ (i - 5))
    (by positivity) (hinge_free_deg hd i) hcount
  refine (le_of_eq ?_).trans (ht.trans (Real.exp_le_exp.2 ?_))
  · rfl
  · have e : α * (n : ℝ) ^ (i - 4) * q ^ (2 * (i - 4)) /
        (16 * (2 ^ (i.choose 2) * (n : ℝ) ^ (i - 5)) * ((i - 4 : ℕ) : ℝ)) =
        α * q ^ (2 * (i - 4)) / (16 * 2 ^ (i.choose 2) * ((i - 4 : ℕ) : ℝ)) * n := by
      have : (n : ℝ) ^ (i - 4) = (n : ℝ) ^ (i - 5) * n := by
        rw [← pow_succ]; congr 1; omega
      rw [this]; field_simp
    rw [e, neg_le_neg_iff]
    apply mul_le_mul_of_nonneg_right _ hnR.le
    have hrR : (0 : ℝ) < ((i - 4 : ℕ) : ℝ) := by exact_mod_cast hr
    have hhR : ((i - 4 : ℕ) : ℝ) ≤ (h : ℝ) := by
      have : i - 4 ≤ h := by omega
      exact_mod_cast this
    have hq2 : q ^ (2 * h) ≤ q ^ (2 * (i - 4)) :=
      pow_le_pow_of_le_one hq.le hq1 (by omega)
    have h2 : (2 : ℝ) ^ (i.choose 2) ≤ 2 ^ (h.choose 2) :=
      pow_le_pow_right₀ (by norm_num) (Nat.choose_le_choose 2 hih)
    apply div_le_div₀ (by positivity) (mul_le_mul_of_nonneg_left hq2 hα.le) (by positivity)
    exact mul_le_mul (mul_le_mul_of_nonneg_left h2 (by norm_num)) hhR hrR.le (by positivity)

/-- **deterministic hinge payment** after fixing `W` -/
theorem hinge_delete {G : SimpleGraph V} {lab : V → I} {F : Set (Multiset I)} {u v a b : V}
    (hd : u ≠ v ∧ u ≠ a ∧ v ≠ a ∧ u ≠ b ∧ v ≠ b ∧ a ≠ b) (i : ℕ) (W S : Finset V) :
    (((hinges G lab F u v a b i).filter fun J => freeV u v a b J ⊆ W).card : ℝ) -
        S.card * (2 ^ (i.choose 2) * (Fintype.card V : ℝ) ^ (i - 5)) ≤
      ((hinges G lab F u v a b i).filter fun J => freeV u v a b J ⊆ W \ S).card := by
  set 𝓗 := hinges G lab F u v a b i
  have hcov : (𝓗.filter fun J => freeV u v a b J ⊆ W) ⊆
      (𝓗.filter fun J => freeV u v a b J ⊆ W \ S) ∪
        S.biUnion (fun z => 𝓗.filter fun J => z ∈ freeV u v a b J) := by
    intro J hJ
    simp only [Finset.mem_filter] at hJ
    by_cases hS : ∃ z ∈ S, z ∈ freeV u v a b J
    · obtain ⟨z, hzS, hz⟩ := hS
      exact Finset.mem_union_right _ (Finset.mem_biUnion.2 ⟨z, hzS, Finset.mem_filter.2 ⟨hJ.1, hz⟩⟩)
    · push_neg at hS
      refine Finset.mem_union_left _ (Finset.mem_filter.2 ⟨hJ.1, ?_⟩)
      intro x hx; exact Finset.mem_sdiff.2 ⟨hJ.2 hx, fun hxS => hS x hxS hx⟩
  have h1 := (Finset.card_le_card hcov).trans (Finset.card_union_le _ _)
  have h2 : ((S.biUnion fun z => 𝓗.filter fun J => z ∈ freeV u v a b J).card : ℝ) ≤
      S.card * (2 ^ (i.choose 2) * (Fintype.card V : ℝ) ^ (i - 5)) := by
    calc _ ≤ ((∑ z ∈ S, (𝓗.filter fun J => z ∈ freeV u v a b J).card : ℕ) : ℝ) := by
          exact_mod_cast Finset.card_biUnion_le
      _ = ∑ z ∈ S, ((𝓗.filter fun J => z ∈ freeV u v a b J).card : ℝ) := by push_cast; rfl
      _ ≤ ∑ _z ∈ S, (2 ^ (i.choose 2) * (Fintype.card V : ℝ) ^ (i - 5)) :=
          Finset.sum_le_sum fun z _ => hinge_free_deg hd i z
      _ = _ := by rw [Finset.sum_const, nsmul_eq_mul]
  have : ((𝓗.filter fun J => freeV u v a b J ⊆ W).card : ℝ) ≤
      ((𝓗.filter fun J => freeV u v a b J ⊆ W \ S).card : ℝ) +
        ((S.biUnion fun z => 𝓗.filter fun J => z ∈ freeV u v a b J).card : ℝ) := by
    exact_mod_cast h1
  linarith

/-- a hinge whose roots and free vertices lie in `W` has its whole support in `W` -/
lemma support_subset_of_free {u v a b : V} {J : Finset (Sym2 V)} {W : Finset V}
    (hroots : ({u, v, a, b} : Finset V) ⊆ W) (hfree : freeV u v a b J ⊆ W) :
    support J ⊆ W := by
  intro x hx
  by_cases hr : x ∈ ({u, v, a, b} : Finset V)
  · exact hroots hr
  · exact hfree (Finset.mem_sdiff.2 ⟨hx, hr⟩)

/-- the threshold rate -/
noncomputable def thetaH (α q a : ℝ) (h m : ℕ) : ℝ :=
  min (a * q ^ (2 * m) / (16 * m ^ 2))
    (min (α * q ^ 2 / 16) (min (α * q ^ (2 * h) / (16 * 2 ^ (h.choose 2) * h)) (q ^ 2 / 16)))

/-- the threshold `n₀` -/
noncomputable def n0H (α q a : ℝ) (h m : ℕ) : ℕ := ⌈600 / thetaH α q a h m ^ 5⌉₊ + 1

/-- **S07 §2 with the original H3/H4**: one random core preserving everything at once. -/
theorem random_core_H3H4 (α q a : ℝ) (h m : ℕ) (hα : 0 < α) (hq : 0 < q) (hq1 : q ≤ 1)
    (ha : 0 < a) (hh : 6 ≤ h) (hm : 0 < m)
    (G : SimpleGraph V) (lab : V → I) (F : Set (Multiset I))
    (hH3 : CommonNbrCond G lab F α) (hH4 : HingeCond G lab F α h)
    (hn : n0H α q a h m ≤ Fintype.card V)
    (L : V → SimpleGraph V) [∀ v, DecidableRel (L v).Adj]
    (adm : V → V → V → Prop)
    (hpaths : ∀ v x y, adm v x y →
      a * (Fintype.card V : ℝ) ^ m ≤ (pathsLen (L v) (m + 1) x y).card) :
    ∃ W : Finset V,
      q * Fintype.card V / 2 ≤ W.card ∧ (W.card : ℝ) < 2 * q * Fintype.card V ∧
      (∀ u v : V, u ≠ v → ∀ k : I, ({lab u, lab v, k} : Multiset I) ∈ F →
        q * α * Fintype.card V / 2 ≤ ((commonNbrs G lab k u v) ∩ W).card) ∧
      (∀ u v a' b' : V, HingeTest G lab F u v a' b' →
        α * q ^ (hOrd hH4 u v a' b' - 4) * (Fintype.card V : ℝ) ^ (hOrd hH4 u v a' b' - 4) / 2 ≤
          ((hinges G lab F u v a' b' (hOrd hH4 u v a' b')).filter fun J =>
            freeV u v a' b' J ⊆ W).card) ∧
      ∀ v x y, adm v x y →
        a * q ^ m * (Fintype.card V : ℝ) ^ m / 2 ≤ (pathsIn (L v) m x y W).card := by
  classical
  set n := Fintype.card V with hndef
  set θ := thetaH α q a h m with hθdef
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have hhR : (0 : ℝ) < h := by have : 0 < h := by omega
                               exact_mod_cast this
  have t1 : 0 < a * q ^ (2 * m) / (16 * m ^ 2) := by positivity
  have t2 : 0 < α * q ^ 2 / 16 := by positivity
  have t3 : 0 < α * q ^ (2 * h) / (16 * 2 ^ (h.choose 2) * h) := by positivity
  have t4 : 0 < q ^ 2 / 16 := by positivity
  have hθpos : 0 < θ := lt_min t1 (lt_min t2 (lt_min t3 t4))
  have hθ1 : θ ≤ a * q ^ (2 * m) / (16 * m ^ 2) := min_le_left _ _
  have hθ2 : θ ≤ α * q ^ 2 / 16 := (min_le_right _ _).trans (min_le_left _ _)
  have hθ3 : θ ≤ α * q ^ (2 * h) / (16 * 2 ^ (h.choose 2) * h) :=
    (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
  have hθ4 : θ ≤ q ^ 2 / 16 :=
    (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _))
  have hnθ : 120 * 5 / θ ^ 5 < n := by
    have := Nat.le_ceil (600 / θ ^ 5)
    have h2 : ((n0H α q a h m : ℕ) : ℝ) ≤ n := by exact_mod_cast hn
    unfold n0H at h2; push_cast at h2; rw [← hθdef] at h2; linarith
  have hnR : (0 : ℝ) < n := lt_trans (by positivity) hnθ
  have hn0 : 0 < n := by exact_mod_cast hnR
  have hq0 := hq.le
  have hexpmono : ∀ t : ℝ, θ ≤ t → Real.exp (-(t * n)) ≤ Real.exp (-(θ * n)) := fun t ht =>
    Real.exp_le_exp.2 (by nlinarith)
  -- the bad events
  let Idx := (V × V × V) ⊕ ((V × V × V) ⊕ ((V × V × V × V) ⊕ Bool))
  let bad : Idx → Finset V → Prop := fun j W => match j with
    | Sum.inl (v, x, y) => adm v x y ∧
        ((pathsIn (L v) m x y W).card : ℝ) < a * (n : ℝ) ^ m * q ^ m / 2
    | Sum.inr (Sum.inl (u, v, w)) => (u ≠ v ∧ ({lab u, lab v, lab w} : Multiset I) ∈ F) ∧
        (((commonNbrs G lab (lab w) u v) ∩ W).card : ℝ) < α * n * q ^ 1 / 2
    | Sum.inr (Sum.inr (Sum.inl (u, v, a', b'))) => HingeTest G lab F u v a' b' ∧
        (((hinges G lab F u v a' b' (hOrd hH4 u v a' b')).filter fun J =>
            freeV u v a' b' J ⊆ W).card : ℝ) <
          α * (n : ℝ) ^ (hOrd hH4 u v a' b' - 4) * q ^ (hOrd hH4 u v a' b' - 4) / 2
    | Sum.inr (Sum.inr (Sum.inr true)) => (W.card : ℝ) < n * q ^ 1 / 2
    | Sum.inr (Sum.inr (Sum.inr false)) => q * n + q * n ≤ (W.card : ℝ)
  have hE : ∀ j, bprob q univ (bad j) ≤ Real.exp (-(θ * n)) := by
    intro j
    rcases j with ⟨v, x, y⟩ | ⟨u, v, w⟩ | ⟨u, v, a', b'⟩ | b
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
      · refine (bprob_mono hq0 hq1 (E := bad (Sum.inr (Sum.inr (Sum.inr false))))
          (E' := fun W => q * n + q * n ≤ (W.card : ℝ))
          (iE' := fun W => inferInstance) (fun W h => h)).trans ?_
        exact (fam_size_hi hq hq1).trans (hexpmono _ (by nlinarith))
      · refine (bprob_mono hq0 hq1 (E := bad (Sum.inr (Sum.inr (Sum.inr true))))
          (E' := fun W => (W.card : ℝ) < n * q ^ 1 / 2)
          (iE' := fun W => inferInstance) (fun W h => h)).trans ?_
        exact (fam_size_lo hq hq1).trans (hexpmono _ hθ4)
  have hsum : ∑ j : Idx, bprob q univ (bad j) < 1 := by
    calc ∑ j : Idx, bprob q univ (bad j) ≤ ∑ _j : Idx, Real.exp (-(θ * n)) :=
          Finset.sum_le_sum fun j _ => hE j
      _ = Fintype.card Idx * Real.exp (-(θ * n)) := by
          rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      _ ≤ 5 * (n : ℝ) ^ 4 * Real.exp (-(θ * n)) := by
          apply mul_le_mul_of_nonneg_right _ (Real.exp_pos _).le
          have hc : Fintype.card Idx = n ^ 3 + (n ^ 3 + (n ^ 4 + 2)) := by
            simp only [Idx, Fintype.card_sum, Fintype.card_prod, Fintype.card_bool, ← hndef]; ring
          rw [hc]; push_cast
          have hn1R : (1 : ℝ) ≤ n := by exact_mod_cast hn0
          have h3 : (n : ℝ) ^ 3 ≤ (n : ℝ) ^ 4 := by
            have := pow_le_pow_right₀ hn1R (show 3 ≤ 4 by norm_num); exact this
          have h4 : (1 : ℝ) ≤ (n : ℝ) ^ 4 := one_le_pow₀ hn1R
          linarith
      _ < 1 := exp_beats_poly hθpos (by norm_num) hnθ
  obtain ⟨W, -, hW⟩ := exists_good hq0 hq1 univ univ bad hsum
  refine ⟨W, ?_, ?_, ?_, ?_, ?_⟩
  · have := hW (Sum.inr (Sum.inr (Sum.inr true))) (mem_univ _)
    simp only [bad, not_lt] at this; linarith
  · have := hW (Sum.inr (Sum.inr (Sum.inr false))) (mem_univ _)
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

end S07V24
