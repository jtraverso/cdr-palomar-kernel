/-
Copyright (c) 2026 Juan Pablo Traverso Gianini.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module
public import RequestProject.TypedTriangle.VortexCleanHinge
public import RequestProject.TypedTriangle.VortexHingeSubfamilyTail
public import RequestProject.TypedTriangle.VortexAnchoredParameters
public import RequestProject.TypedTriangle.VortexRelativeChildGeometry
set_option maxHeartbeats 4000000 -- build option (original: -DmaxHeartbeats=1600000; raised)
set_option maxRecDepth 16384 -- build option (original: -DmaxRecDepth=8192; raised)
@[expose] public section

/-! Relative sampling retains the clean hinge invariant on the actual child,
with the original fixed hinge order and summable relative error. -/

open Finset Classical S07V24
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace TypedTriangle.Vortex
open RawReference CorePaid

def cleanHingeOrder {V I : Type*} [Fintype V]
    {H : Host V I} {F : Set (Multiset I)} {α : ℝ} {h : ℕ}
    (hClean : CleanHingeCond H F α h) (u v a b : V) : ℕ :=
  if ht : HingeTest H.G H.lab F u v a b then
    Classical.choose (hClean u v a b ht.1 ht.2.1 ht.2.2) else 6

theorem cleanHingeOrder_spec {V I : Type*} [Fintype V]
    {H : Host V I} {F : Set (Multiset I)} {α : ℝ} {h : ℕ}
    (hClean : CleanHingeCond H F α h) {u v a b : V}
    (ht : HingeTest H.G H.lab F u v a b) :
    6 ≤ cleanHingeOrder hClean u v a b ∧
      cleanHingeOrder hClean u v a b ≤ h ∧
      α * (Fintype.card V : ℝ) ^ (cleanHingeOrder hClean u v a b - 4) ≤
        ((SparseEdge.hinges H.G H.lab F u v a b
          (cleanHingeOrder hClean u v a b)).filter (fun J => s(a, b) ∉ J)).card := by
  unfold cleanHingeOrder
  rw [dite_eq_left ht]
  exact Classical.choose_spec (hClean u v a b ht.1 ht.2.1 ht.2.2)

theorem clean_hinge_tail_at_rate {V I : Type*} [Fintype V]
    (H : Host V I) (F : Set (Multiset I)) (α q η θ : ℝ) (h : ℕ)
    (hα : 0 < α) (hq : 0 < q) (hq1 : q ≤ 1)
    (hη : 0 < η) (hη1 : η ≤ 1) (hn : 0 < Fintype.card V)
    (hClean : CleanHingeCond H F α h)
    (hθ : ∀ i, 6 ≤ i → i ≤ h → θ ≤ η ^ 2 * α ^ 2 * q ^ (2 * (i - 4)) /
      (4 * ((2 : ℝ) ^ (i.choose 2)) ^ 2 * ((i - 4 : ℕ) : ℝ)))
    (u v a b : V) (ht : HingeTest H.G H.lab F u v a b) :
    bprob q univ (fun W =>
      ((((SparseEdge.hinges H.G H.lab F u v a b
        (cleanHingeOrder hClean u v a b)).filter (fun J => s(a, b) ∉ J)).filter
          (fun J => freeV u v a b J ⊆ W)).card : ℝ) <
        (1 - η) * α * q ^ (cleanHingeOrder hClean u v a b - 4) *
          (Fintype.card V : ℝ) ^ (cleanHingeOrder hClean u v a b - 4)) ≤
      Real.exp (-(θ * Fintype.card V)) := by
  let i := cleanHingeOrder hClean u v a b
  let Fam := (SparseEdge.hinges H.G H.lab F u v a b i).filter (fun J => s(a, b) ∉ J)
  have hi := cleanHingeOrder_spec hClean ht
  have htail := hinge_subfamily_tail_linear (roots_distinct ht) hi.1
    hα hq hq1 hη hη1 hn Fam (filter_subset _ _) hi.2.2
  have hrate := mul_le_mul_of_nonneg_right (hθ i hi.1 hi.2.1)
    (show (0 : ℝ) ≤ Fintype.card V by positivity)
  have hfrac : θ * Fintype.card V ≤
      η ^ 2 * α ^ 2 * q ^ (2 * (i - 4)) * (Fintype.card V : ℝ) /
        (4 * ((2 : ℝ) ^ (i.choose 2)) ^ 2 * ((i - 4 : ℕ) : ℝ)) := by
    convert hrate using 1 <;> ring
  calc
    _ ≤ Real.exp (-(η ^ 2 * α ^ 2 * q ^ (2 * (i - 4)) * (Fintype.card V : ℝ) /
        (4 * ((2 : ℝ) ^ (i.choose 2)) ^ 2 * ((i - 4 : ℕ) : ℝ)))) := by
      convert htail using 1
      congr 1
      funext W
      apply propext
      dsimp only [ccount, Fam, i]
      congr 1
      ring
    _ ≤ Real.exp (-(θ * Fintype.card V)) :=
      Real.exp_le_exp.mpr (neg_le_neg hfrac)

theorem anchored_clean_relative_sample_at_rate
    {V I : Type*} [Fintype V]
    (H : Host V I) (F : Set (Multiset I)) (α q η θ : ℝ) (h : ℕ)
    (hα : 0 < α) (hq : 0 < q) (hq1 : q ≤ 1)
    (hη : 0 < η) (hη1 : η ≤ 1) (hn : 0 < Fintype.card V)
    (h3 : CommonNbrCond H F α) (hClean : CleanHingeCond H F α h)
    (hθsize : θ ≤ η ^ 2 * q ^ 2 / 4)
    (hθpool : θ ≤ η ^ 2 * α ^ 2 * q ^ 2 / 4)
    (hθhinge : ∀ i, 6 ≤ i → i ≤ h →
      θ ≤ η ^ 2 * α ^ 2 * q ^ (2 * (i - 4)) /
        (4 * ((2 : ℝ) ^ (i.choose 2)) ^ 2 * ((i - 4 : ℕ) : ℝ)))
    (hbudget : (Fintype.card ((V × V × V) ⊕ (V × V × V × V)) + 2 : ℝ) *
      Real.exp (-(θ * Fintype.card V)) < 1) :
    ∃ W : Finset V,
      (1 - η) * q * Fintype.card V ≤ W.card ∧
      (W.card : ℝ) < (1 + η) * q * Fintype.card V ∧
      (∀ u v, u ≠ v → ∀ k, ({H.lab u, H.lab v, k} : Multiset I) ∈ F →
        (1 - η) * α * q * Fintype.card V ≤ ((commonNbrs H k u v) ∩ W).card) ∧
      (∀ u v a b, HingeTest H.G H.lab F u v a b →
        (1 - η) * α * q ^ (cleanHingeOrder hClean u v a b - 4) *
          (Fintype.card V : ℝ) ^ (cleanHingeOrder hClean u v a b - 4) ≤
            (((SparseEdge.hinges H.G H.lab F u v a b
              (cleanHingeOrder hClean u v a b)).filter (fun J => s(a, b) ∉ J)).filter
                (fun J => freeV u v a b J ⊆ W)).card) := by
  let E : ((V × V × V) ⊕ (V × V × V × V)) → Finset V → Prop := fun j W =>
    match j with
    | Sum.inl (u, v, x) =>
        if u ≠ v ∧ ({H.lab u, H.lab v, H.lab x} : Multiset I) ∈ F then
          (((commonNbrs H (H.lab x) u v) ∩ W).card : ℝ) <
            (1 - η) * α * q * Fintype.card V else False
    | Sum.inr (u, v, a, b) =>
        if HingeTest H.G H.lab F u v a b then
          ((((SparseEdge.hinges H.G H.lab F u v a b
            (cleanHingeOrder hClean u v a b)).filter (fun J => s(a, b) ∉ J)).filter
              (fun J => freeV u v a b J ⊆ W)).card : ℝ) <
            (1 - η) * α * q ^ (cleanHingeOrder hClean u v a b - 4) *
              (Fintype.card V : ℝ) ^ (cleanHingeOrder hClean u v a b - 4) else False
  have hE : ∀ j, bprob q univ (E j) ≤ Real.exp (-(θ * Fintype.card V)) := by
    intro j
    rcases j with ⟨⟨u, v, x⟩⟩ | ⟨⟨u, v, a, b⟩⟩
    · by_cases ht : u ≠ v ∧ ({H.lab u, H.lab v, H.lab x} : Multiset I) ∈ F
      · simpa only [E, ite_eq_left ht] using
          pool_tail_at_rate H F α q η θ hα hq hq1 hη hη1 hn h3 hθpool u v x ht.1 ht.2
      · simpa only [E, ite_eq_right ht, bprob, ite_false, bexp_const] using
          (Real.exp_pos (-(θ * Fintype.card V))).le
    · by_cases ht : HingeTest H.G H.lab F u v a b
      · simpa only [E, ite_eq_left ht] using
          clean_hinge_tail_at_rate H F α q η θ h hα hq hq1 hη hη1 hn hClean
            hθhinge u v a b ht
      · simpa only [E, ite_eq_right ht, bprob, ite_false, bexp_const] using
          (Real.exp_pos (-(θ * Fintype.card V))).le
  obtain ⟨W, hWlo, hWhi, hgood⟩ :=
    joint_sample_relative_size q η θ E hq hq1 hη hη1 hn hθsize hE hbudget
  refine ⟨W, hWlo, hWhi, ?_, ?_⟩
  · intro u v huv k hk
    have hcount := h3 u v huv k hk
    have hnR : (0 : ℝ) < Fintype.card V := by exact_mod_cast hn
    have hcountpos : 0 < (commonNbrs H k u v).card := by
      exact_mod_cast (show (0 : ℝ) < (commonNbrs H k u v).card by
        nlinarith [mul_pos hα hnR])
    obtain ⟨x, hx⟩ := card_pos.mp hcountpos
    have hxlab : H.lab x = k := (mem_filter.mp hx).2.2.2
    have ht : u ≠ v ∧ ({H.lab u, H.lab v, H.lab x} : Multiset I) ∈ F := by
      simpa only [hxlab] using (show u ≠ v ∧
        ({H.lab u, H.lab v, k} : Multiset I) ∈ F from ⟨huv, hk⟩)
    have hgood' := hgood (Sum.inl (u, v, x))
    simpa only [E, ite_eq_left ht, hxlab, not_lt] using hgood'
  · intro u v a b ht
    have hgood' := hgood (Sum.inr (u, v, a, b))
    simpa only [E, ite_eq_left ht, not_lt] using hgood'

private theorem surviving_clean_hinges_card_le {V I : Type*} [Fintype V]
    (H : Host V I) (F : Set (Multiset I)) (Z : Finset V)
    (u v a b : Survivors Z) (i : ℕ)
    (hTa : IsAllowed H F {u.1, v.1, a.1}) (hTb : IsAllowed H F {u.1, v.1, b.1}) :
    ((hinges H F u.1 v.1 a.1 b.1 i).filter
      (fun J => Disjoint (support J) Z ∧ s(a.1, b.1) ∉ J)).card ≤
      ((SparseEdge.hinges (restrictedHost H Z).G (restrictedHost H Z).lab F
        u v a b i).filter (fun J => s(a, b) ∉ J)).card := by
  refine Finset.card_le_card_of_injOn (fun J => restrictEdgeSet Z J) ?_ ?_
  · intro J hJ
    obtain ⟨hJ, hd, hClean⟩ := mem_filter.mp hJ
    have hparts := (mem_filter.mp hJ).2
    refine mem_filter.mpr ⟨?_, ?_⟩
    · change restrictEdgeSet Z J ∈ hinges (restrictedHost H Z) F u v a b i
      exact mem_filter.mpr ⟨mem_univ _,
        isHinge_restrictEdgeSet H F Z u v a b hparts.1 hd hTa hTb,
        (card_support_restrictEdgeSet Z J hd).trans hparts.2⟩
    · intro hab
      have hmap := (mem_restrictEdgeSet Z J s(a, b)).mp hab
      exact hClean (by simpa only [Sym2.map_mk] using hmap)
  · intro J hJ K hK heq
    exact restrictEdgeSet_injective_on_avoiding Z
      (mem_filter.mp hJ).2.1 (mem_filter.mp hK).2.1 heq

theorem clean_relative_sample_child_geometry {V I : Type*} [Fintype V]
    (H : Host V I) (F : Set (Multiset I)) {α q η : ℝ} {h : ℕ}
    (hα : 0 < α) (hq : 0 < q) (hη : 0 ≤ η) (hη1 : η < 1)
    (hh : 1 ≤ h) (hClean : CleanHingeCond H F α h) (W : Finset V)
    (hW : (W.card : ℝ) ≤ (1 + η) * q * Fintype.card V)
    (hpool : ∀ u v, u ≠ v → ∀ k, ({H.lab u, H.lab v, k} : Multiset I) ∈ F →
      (1 - η) * α * q * Fintype.card V ≤ ((commonNbrs H k u v) ∩ W).card)
    (hhinge : ∀ u v a b, HingeTest H.G H.lab F u v a b →
      (1 - η) * α * q ^ (cleanHingeOrder hClean u v a b - 4) *
        (Fintype.card V : ℝ) ^ (cleanHingeOrder hClean u v a b - 4) ≤
          (((SparseEdge.hinges H.G H.lab F u v a b
            (cleanHingeOrder hClean u v a b)).filter (fun J => s(a, b) ∉ J)).filter
              (fun J => freeV u v a b J ⊆ W)).card) :
    CommonNbrCond (restrictedHost H (univ \ W)) F
      (α * (1 - ((h : ℝ) + 1) * η)) ∧
    CleanHingeCond (restrictedHost H (univ \ W)) F
      (α * (1 - ((h : ℝ) + 1) * η)) h := by
  have hc : 0 < 1 - η := by linarith
  have hr : 1 ≤ 1 + η := by linarith
  have hrp : 0 < 1 + η := by linarith
  have hbound : α * (1 - ((h : ℝ) + 1) * η) ≤ (1 - η) * α / (1 + η) ^ h := by
    have hs := mul_le_mul_of_nonneg_left (one_step_relative_geometry_loss h hη) hα.le
    convert hs using 1 <;> ring
  have hnum : ∀ d : ℕ, d ≤ h →
      (1 - η) * α / (1 + η) ^ h * (W.card : ℝ) ^ d ≤
        (1 - η) * α * q ^ d * (Fintype.card V : ℝ) ^ d := by
    intro d hd
    have hpow : (1 + η) ^ d ≤ (1 + η) ^ h := pow_le_pow_right₀ hr hd
    calc
      _ ≤ (1 - η) * α / (1 + η) ^ h * ((1 + η) * q * Fintype.card V) ^ d := by gcongr
      _ = (1 - η) * α / (1 + η) ^ h * (1 + η) ^ d * q ^ d *
          (Fintype.card V : ℝ) ^ d := by rw [mul_pow, mul_pow]; ring
      _ ≤ (1 - η) * α / (1 + η) ^ h * (1 + η) ^ h * q ^ d *
          (Fintype.card V : ℝ) ^ d := by gcongr
      _ = _ := by field_simp
  constructor
  · intro u v huv k hk
    have heq : ((commonNbrs H k u.1 v.1).filter (fun w => w ∉ univ \ W)) =
        commonNbrs H k u.1 v.1 ∩ W := by ext w; simp
    rw [card_commonNbrs_restrictedHost, heq, card_survivors_compl]
    have hfirst := mul_le_mul_of_nonneg_right hbound (show (0 : ℝ) ≤ W.card by positivity)
    have hnext := hnum 1 hh
    simp only [pow_one] at hnext
    exact (hfirst.trans hnext).trans (hpool u.1 v.1 (fun he => huv (Subtype.ext he)) k hk)
  · intro u v a b hab hTa hTb
    have hTa' : IsAllowed H F {u.1, v.1, a.1} := by
      apply (isAllowed_restricted_triple H F (univ \ W) u v a).mp
      convert hTa using 1 <;> ext x <;> simp
    have hTb' : IsAllowed H F {u.1, v.1, b.1} := by
      apply (isAllowed_restricted_triple H F (univ \ W) u v b).mp
      convert hTb using 1 <;> ext x <;> simp
    have ht : HingeTest H.G H.lab F u.1 v.1 a.1 b.1 :=
      ⟨fun he => hab (Subtype.ext he), hTa', hTb'⟩
    have hs := cleanHingeOrder_spec hClean ht
    let i := cleanHingeOrder hClean u.1 v.1 a.1 b.1
    have hroot : ({u.1, v.1, a.1, b.1} : Finset V) ⊆ W := by
      intro x hx
      simp only [mem_insert, mem_singleton] at hx
      rcases hx with rfl | rfl | rfl | rfl <;>
        first | simpa only [mem_sdiff, mem_univ, true_and, not_not] using u.2
              | simpa only [mem_sdiff, mem_univ, true_and, not_not] using v.2
              | simpa only [mem_sdiff, mem_univ, true_and, not_not] using a.2
              | simpa only [mem_sdiff, mem_univ, true_and, not_not] using b.2
    have hSub : (((SparseEdge.hinges H.G H.lab F u.1 v.1 a.1 b.1 i).filter
        (fun J => s(a.1, b.1) ∉ J)).filter (fun J => freeV u.1 v.1 a.1 b.1 J ⊆ W)) ⊆
        (hinges H F u.1 v.1 a.1 b.1 i).filter
          (fun J => Disjoint (support J) (univ \ W) ∧ s(a.1, b.1) ∉ J) := by
      intro J hJ
      obtain ⟨hJ, hFree⟩ := mem_filter.mp hJ
      obtain ⟨hJ, hCleanJ⟩ := mem_filter.mp hJ
      refine mem_filter.mpr ⟨hJ, disjoint_left.mpr ?_, hCleanJ⟩
      intro x hx hxOut
      have hxW : x ∈ W := by
        by_cases hr : x ∈ ({u.1, v.1, a.1, b.1} : Finset V)
        · exact hroot hr
        · exact hFree (mem_sdiff.mpr ⟨hx, hr⟩)
      exact (mem_sdiff.mp hxOut).2 hxW
    have hCount := (card_le_card hSub).trans
      (surviving_clean_hinges_card_le H F (univ \ W) u v a b i hTa' hTb')
    refine ⟨i, hs.1, hs.2.1, ?_⟩
    rw [card_survivors_compl]
    have hfirst := mul_le_mul_of_nonneg_right hbound
      (show (0 : ℝ) ≤ (W.card : ℝ) ^ (i - 4) by positivity)
    have hnext := hnum (i - 4) (by have := hs.2.1; omega)
    exact ((hfirst.trans hnext).trans (hhinge u.1 v.1 a.1 b.1 ht)).trans
      (by
        have hCountR := (Nat.cast_le (α := ℝ)).mpr hCount
        convert hCountR using 1 <;> congr 1 <;> congr 1 <;>
          ext E <;> simp only [Finset.mem_filter])

theorem exists_automatic_clean_relative_sample_uniform
    (αmin q : ℝ) (h : ℕ) (hαmin : 0 < αmin) (hq : 0 < q)
    (hq1 : q ≤ 1) :
    ∃ N : ℝ, ∀ {V I : Type*} [Fintype V] (H : Host V I)
      (F : Set (Multiset I)) (α : ℝ), αmin ≤ α → N ≤ (Fintype.card V : ℝ) →
      CommonNbrCond H F α → ∀ hClean : CleanHingeCond H F α h,
      let η : ℝ := (Real.sqrt (Real.sqrt (Fintype.card V : ℝ)))⁻¹
      0 < η ∧ η < 1 ∧
      ∃ W : Finset V,
        (1 - η) * q * Fintype.card V ≤ W.card ∧
        (W.card : ℝ) < (1 + η) * q * Fintype.card V ∧
        (∀ u v, u ≠ v → ∀ k, ({H.lab u, H.lab v, k} : Multiset I) ∈ F →
          (1 - η) * α * q * Fintype.card V ≤ ((commonNbrs H k u v) ∩ W).card) ∧
        (∀ u v a b, HingeTest H.G H.lab F u v a b →
          (1 - η) * α * q ^ (cleanHingeOrder hClean u v a b - 4) *
            (Fintype.card V : ℝ) ^ (cleanHingeOrder hClean u v a b - 4) ≤
              (((SparseEdge.hinges H.G H.lab F u v a b
                (cleanHingeOrder hClean u v a b)).filter (fun J => s(a, b) ∉ J)).filter
                  (fun J => freeV u v a b J ⊆ W)).card) := by
  obtain ⟨c, N₀, hc, hparam⟩ := exists_anchored_sampling_parameters αmin q h hαmin hq
  refine ⟨max N₀ 2, ?_⟩
  intro V I _ H F α hαge hn h3 hClean
  have hα : 0 < α := lt_of_lt_of_le hαmin hαge
  letI : DecidableEq V := Classical.decEq V
  have hn₀ : N₀ ≤ (Fintype.card V : ℝ) := (le_max_left _ _).trans hn
  have hn2 : (2 : ℝ) ≤ Fintype.card V := (le_max_right _ _).trans hn
  have hnpos : 0 < Fintype.card V := by
    exact_mod_cast (show (0 : ℝ) < Fintype.card V by linarith)
  obtain ⟨hηpos, hηle, hθsize, hθpool, hθhinge, hpoly⟩ := hparam (Fintype.card V) hn₀
  let η : ℝ := (Real.sqrt (Real.sqrt (Fintype.card V : ℝ)))⁻¹
  let θ : ℝ := c * η ^ 2
  have hθpool' : θ ≤ η ^ 2 * α ^ 2 * q ^ 2 / 4 :=
    hθpool.trans (by gcongr)
  have hθhinge' : ∀ i, 6 ≤ i → i ≤ h →
      θ ≤ η ^ 2 * α ^ 2 * q ^ (2 * (i - 4)) /
        (4 * ((2 : ℝ) ^ (i.choose 2)) ^ 2 * ((i - 4 : ℕ) : ℝ)) := by
    intro i hi6 hih
    exact (hθhinge i hi6 hih).trans (by gcongr)
  have hbudget : (Fintype.card ((V × V × V) ⊕ (V × V × V × V)) + 2 : ℝ) *
      Real.exp (-(θ * Fintype.card V)) < 1 := by
    have hcount : (Fintype.card ((V × V × V) ⊕ (V × V × V × V)) : ℝ) =
        (Fintype.card V : ℝ) ^ 3 + (Fintype.card V : ℝ) ^ 4 := by
      simp only [Fintype.card_sum, Fintype.card_prod, Nat.cast_add, Nat.cast_mul]
      ring
    simpa only [Nat.cast_add, Nat.cast_ofNat, hcount] using hpoly
  obtain ⟨W, hWlo, hWhi, hpool, hhinge⟩ :=
    anchored_clean_relative_sample_at_rate H F α q η θ h hα hq hq1
      hηpos hηle hnpos h3 hClean hθsize hθpool' hθhinge' hbudget
  have hηlt : η < 1 := by
    have hn1 : (1 : ℝ) < Fintype.card V := by linarith
    have hs1 : (1 : ℝ) < Real.sqrt (Fintype.card V : ℝ) := by
      simpa only [Real.sqrt_one] using
        (Real.sqrt_lt_sqrt (by norm_num : (0 : ℝ) ≤ 1) hn1)
    have hss1 : (1 : ℝ) < Real.sqrt (Real.sqrt (Fintype.card V : ℝ)) := by
      simpa only [Real.sqrt_one] using
        (Real.sqrt_lt_sqrt (by norm_num : (0 : ℝ) ≤ 1) hs1)
    exact inv_lt_one_of_one_lt₀ hss1
  exact ⟨hηpos, hηlt, W, hWlo, hWhi, hpool, hhinge⟩

theorem exists_automatic_clean_relative_child_uniform
    (αmin q : ℝ) (h : ℕ) (hαmin : 0 < αmin) (hq : 0 < q)
    (hq1 : q ≤ 1) (hh : 1 ≤ h) :
    ∃ N : ℝ, ∀ {V I : Type*} [Fintype V] (H : Host V I)
      (F : Set (Multiset I)) (α : ℝ), αmin ≤ α → N ≤ (Fintype.card V : ℝ) →
      CommonNbrCond H F α → CleanHingeCond H F α h →
      let η : ℝ := (Real.sqrt (Real.sqrt (Fintype.card V : ℝ)))⁻¹
      ∃ W : Finset V,
        (1 - η) * q * Fintype.card V ≤ W.card ∧
        (W.card : ℝ) < (1 + η) * q * Fintype.card V ∧
        CommonNbrCond (restrictedHost H (univ \ W)) F
          (α * (1 - ((h : ℝ) + 1) * η)) ∧
        CleanHingeCond (restrictedHost H (univ \ W)) F
          (α * (1 - ((h : ℝ) + 1) * η)) h := by
  obtain ⟨N, hSample⟩ :=
    exists_automatic_clean_relative_sample_uniform αmin q h hαmin hq hq1
  refine ⟨N, ?_⟩
  intro V I _ H F α hαge hn h3 hClean
  obtain ⟨hηpos, hηlt, W, hWlo, hWhi, hpool, hhinge⟩ :=
    hSample H F α hαge hn h3 hClean
  have hgeom := clean_relative_sample_child_geometry H F
    (lt_of_lt_of_le hαmin hαge) hq hηpos.le hηlt hh hClean W hWhi.le hpool hhinge
  exact ⟨W, hWlo, hWhi, hgeom.1, hgeom.2⟩

#print axioms clean_hinge_tail_at_rate
#print axioms anchored_clean_relative_sample_at_rate
#print axioms clean_relative_sample_child_geometry
#print axioms exists_automatic_clean_relative_sample_uniform
#print axioms exists_automatic_clean_relative_child_uniform

end TypedTriangle.Vortex
