/-
Copyright (c) 2026 Juan Pablo Traverso Gianini.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module
public import RequestProject.TypedTriangle.VortexOuterAvailableTails
public import RequestProject.TypedTriangle.VortexNativeAvailablePathSupply
set_option maxHeartbeats 4000000 -- build option (original: -DmaxHeartbeats=1600000; raised)
set_option maxRecDepth 16384 -- build option (original: -DmaxRecDepth=8192; raised)
@[expose] public section
open Finset Classical S07V24 S07V25
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace TypedTriangle.Vortex
open ComponentRows

private theorem bprob_instance_irrel {X : Type*} (q : ℝ) (U : Finset X)
    (E : Finset X → Prop) (d₁ d₂ : DecidablePred E) :
    @bprob X q U E d₁ = @bprob X q U E d₂ := by
  cases Subsingleton.elim d₁ d₂
  rfl

/-- Concrete tests for every root of the original host, including roots in
the prepared cut. Only path auxiliaries and pool vertices avoid that cut;
all native constants precede the sampling rate. -/
theorem native_outer_tests (α : ℝ) (h : ℕ) (hα : 0 < α) :
    ∃ m : ℕ, ∃ a δ : ℝ, ∃ n₀ : ℕ, 0 < m ∧ 0 < a ∧ 0 < δ ∧
      Odd (m+1) ∧ 3 ≤ m+1 ∧
      ∀ q : ℝ, 0 < q → q ≤ 1 → ∃ θ : ℝ, 0 < θ ∧
      ∀ {V I : Type} [Fintype V] (H : Host V I) (F : Set (Multiset I)),
        n₀ ≤ Fintype.card V → CommonNbrCond H F α → HingeCond H F α h →
        ∀ A : Finset V, (A.card : ℝ) ≤ δ * Fintype.card V →
          16 ≤ Fintype.card (Survivors A) →
        letI : DecidableEq (Survivors A) := Classical.decEq _
        ∃ E : ((V × V × V) ⊕ (V × V × V)) → Finset (Survivors A) → Prop,
          Fintype.card ((V × V × V) ⊕ (V × V × V)) ≤ Fintype.card (Survivors A)^4 ∧
          (∀ j, bprob q univ (E j) ≤ Real.exp (-(θ * Fintype.card (Survivors A)))) ∧
          ∀ W : Finset (Survivors A), (∀ j, ¬ E j W) →
            (∀ u v, u ≠ v → ∀ k, ({H.lab u,H.lab v,k} : Multiset I) ∈ F →
              (α / 2) * Fintype.card V * q / 2 ≤ ((commonNbrs H k u v) ∩ liftVertexSet A W).card) ∧
            ∀ v x y, AdmPair (activeComps H.G H.lab F)
              (fun v B => IsBip H.G H.lab F (v,B)) (colG H.G H.lab F) v x y →
              (a / 2) * (Fintype.card V : ℝ)^m * q^m / 2 ≤
                (pathsIn (link H.G H.lab F v) m x y (liftVertexSet A W)).card := by
  obtain ⟨m, a, δNative, n₀, hm, ha, hδNative, hOdd, hLen, hSupply⟩ := native_available_path_supply α h hα
  let δ : ℝ := min δNative (min (α / 2) (1 / 2))
  have hδ : 0 < δ := lt_min hδNative (lt_min (by positivity) (by norm_num))
  refine ⟨m, a, δ, n₀, hm, ha, hδ, hOdd, hLen, ?_⟩
  intro q hq hq1
  let θPool : ℝ := (α / 2)^2 * q^2 / 16
  let θPath : ℝ := (a / 2) * q^(2*m) / (16 * (m : ℝ)^2)
  let θ := min θPool θPath
  have hθPool : 0 < θPool := by dsimp [θPool]; positivity
  have hθPath : 0 < θPath := by dsimp [θPath]; positivity
  refine ⟨θ, lt_min hθPool hθPath, ?_⟩
  intro V I _ H F hn h3 h4 A hA hLarge
  letI : DecidableEq (Survivors A) := Classical.decEq _
  letI : ∀ v, DecidableRel (link H.G H.lab F v).Adj := fun _ => Classical.decRel _
  have hδNative' : δ ≤ δNative := min_le_left _ _
  have hδα : δ ≤ α / 2 := (min_le_right _ _).trans (min_le_left _ _)
  have hδHalf : δ ≤ 1 / 2 := (min_le_right _ _).trans (min_le_right _ _)
  have hAα : (A.card : ℝ) ≤ α / 2 * Fintype.card V :=
    hA.trans (mul_le_mul_of_nonneg_right hδα (by positivity))
  have hAHalf : (A.card : ℝ) ≤ (Fintype.card V : ℝ) / 2 := by
    have hs := hA.trans (mul_le_mul_of_nonneg_right hδHalf (by positivity))
    linarith
  have hCard : (Fintype.card (Survivors A) : ℝ) + A.card = Fintype.card V := by
    exact_mod_cast card_survivors_add_card A
  have hRatio : (Fintype.card V : ℝ) ≤ 2 * Fintype.card (Survivors A) := by linarith
  have hLargeR : (16 : ℝ) ≤ Fintype.card (Survivors A) := by exact_mod_cast hLarge
  have hnPos : 0 < Fintype.card V := by
    have hposR : (0 : ℝ) < Fintype.card V := by linarith [(by positivity : (0 : ℝ) ≤ A.card)]
    exact_mod_cast hposR
  have hNHA : (0 : ℝ) ≤ Fintype.card (Survivors A) := by positivity
  have hJ : Fintype.card ((V × V × V) ⊕ (V × V × V)) ≤ Fintype.card (Survivors A)^4 := by
    have hp := pow_le_pow_left₀ (by positivity : (0 : ℝ) ≤ Fintype.card V) hRatio 3
    have hs := mul_le_mul_of_nonneg_right hLargeR (pow_nonneg hNHA 3)
    have hh : (2 : ℝ) * (Fintype.card V : ℝ)^3 ≤ (Fintype.card (Survivors A) : ℝ)^4 := by nlinarith
    have hJR : (Fintype.card ((V × V × V) ⊕ (V × V × V)) : ℝ) ≤
        (Fintype.card (Survivors A) : ℝ)^4 := by
      simp only [Fintype.card_sum,Fintype.card_prod,Nat.cast_add,Nat.cast_mul]
      nlinarith
    exact_mod_cast hJR
  let Pool (u v x : V) := commonNbrs H (H.lab x) u v \ A
  let Paths (v x y : V) := pathsIn (link H.G H.lab F v) m x y (univ \ A)
  let E : ((V × V × V) ⊕ (V × V × V)) → Finset (Survivors A) → Prop := fun j W =>
    match j with
    | Sum.inl (u,v,x) => (u ≠ v ∧ ({H.lab u,H.lab v,H.lab x} : Multiset I) ∈ F) ∧
        (((Pool u v x) ∩ liftVertexSet A W).card : ℝ) < (α / 2) * Fintype.card V * q / 2
    | Sum.inr (v,x,y) => AdmPair (activeComps H.G H.lab F)
        (fun v B => IsBip H.G H.lab F (v,B)) (colG H.G H.lab F) v x y ∧
        (((Paths v x y).filter (fun p => intlSet m p ⊆ liftVertexSet A W)).card : ℝ) <
          (a / 2) * (Fintype.card V : ℝ)^m * q^m / 2
  have hPoolCount (u v x : V) (huv : u ≠ v)
      (hk : ({H.lab u,H.lab v,H.lab x} : Multiset I) ∈ F) :
      (α / 2) * Fintype.card V ≤ (Pool u v x).card := by
    have hp := h3 u v huv (H.lab x) hk
    have hCover : commonNbrs H (H.lab x) u v ⊆ Pool u v x ∪ A := by
      intro z hz
      by_cases hza : z ∈ A
      · exact mem_union_right _ hza
      · exact mem_union_left _ (mem_sdiff.mpr ⟨hz,hza⟩)
    have hc : ((commonNbrs H (H.lab x) u v).card : ℝ) ≤ (Pool u v x).card + A.card := by
      exact_mod_cast (card_le_card hCover).trans (card_union_le _ _)
    nlinarith
  have hExtra : ∀ j, bprob q univ (E j) ≤ Real.exp (-(θ * Fintype.card (Survivors A))) := by
    intro j
    rcases j with ⟨u,v,x⟩ | ⟨v,x,y⟩
    · by_cases ht : u ≠ v ∧ ({H.lab u,H.lab v,H.lab x} : Multiset I) ∈ F
      · have hTail := available_pool_tail_on_survivors A (Pool u v x) (α / 2) q
          (by positivity) hq hq1 hnPos (hPoolCount u v x ht.1 ht.2)
          (by intro z hz; exact mem_sdiff.mpr ⟨mem_univ _,(mem_sdiff.mp hz).2⟩)
        have hLe : bprob q univ (E (Sum.inl (u,v,x))) ≤ bprob q univ
            (fun W : Finset (Survivors A) => (((Pool u v x) ∩ liftVertexSet A W).card : ℝ) <
              (α / 2) * Fintype.card V * q / 2) :=
          bprob_mono hq.le hq1 (fun W hw => hw.2)
        have hBound := (hLe.trans hTail).trans (Real.exp_le_exp.mpr
          (neg_le_neg (mul_le_mul_of_nonneg_right (min_le_left θPool θPath) hNHA)))
        have hInstances := bprob_instance_irrel q (univ : Finset (Survivors A)) (E (Sum.inl (u,v,x)))
          (fun W => Classical.propDecidable _) (fun W => inferInstance)
        exact hInstances.le.trans hBound
      · rw [bprob_false (E := E (Sum.inl (u,v,x))) (fun W hw => ht hw.1)]
        exact (Real.exp_pos _).le
    · by_cases ht : AdmPair (activeComps H.G H.lab F)
        (fun v B => IsBip H.G H.lab F (v,B)) (colG H.G H.lab F) v x y
      · have hCount := hSupply H F hn h3 h4 A
          (hA.trans (mul_le_mul_of_nonneg_right hδNative' (by positivity))) v x y ht
        have hLength : ∀ p ∈ Paths v x y, p.length = m + 1 := by
          intro p hp
          simp only [Paths, pathsIn, pathsLen,mem_filter,SimpleGraph.mem_finsetWalkLength_iff] at hp
          exact hp.1.1
        have hAvoid : ∀ p ∈ Paths v x y, intlSet m p ⊆ univ \ A := by
          intro p hp
          exact (mem_filter.mp hp).2
        have hTail := available_path_tail_on_survivors A (by positivity : 0 < a / 2) hq hq1 hm hnPos
          (link H.G H.lab F v) x y (Paths v x y) hLength hCount hAvoid
        have hLe : bprob q univ (E (Sum.inr (v,x,y))) ≤ bprob q univ
            (fun W : Finset (Survivors A) => (((Paths v x y).filter
              (fun p => intlSet m p ⊆ liftVertexSet A W)).card : ℝ) <
              (a / 2) * (Fintype.card V : ℝ)^m * q^m / 2) :=
          bprob_mono hq.le hq1 (fun W hw => hw.2)
        have hBound := (hLe.trans hTail).trans (Real.exp_le_exp.mpr
          (neg_le_neg (mul_le_mul_of_nonneg_right (min_le_right θPool θPath) hNHA)))
        have hInstances := bprob_instance_irrel q (univ : Finset (Survivors A)) (E (Sum.inr (v,x,y)))
          (fun W => Classical.propDecidable _) (fun W => inferInstance)
        exact hInstances.le.trans hBound
      · rw [bprob_false (E := E (Sum.inr (v,x,y))) (fun W hw => ht hw.1)]
        exact (Real.exp_pos _).le
  refine ⟨E,hJ,hExtra,?_⟩
  intro W hGood
  have hLift : liftVertexSet A W ⊆ univ \ A := by
    intro z hz
    obtain ⟨w,hw,rfl⟩ := mem_map.mp hz
    exact mem_sdiff.mpr ⟨mem_univ _,w.2⟩
  constructor
  · intro u v huv k hk
    by_cases hkV : ∃ x : V, H.lab x = k
    · obtain ⟨x,hx⟩ := hkV
      subst k
      have hc : (α / 2) * Fintype.card V * q / 2 ≤
          (((Pool u v x) ∩ liftVertexSet A W).card : ℝ) :=
        le_of_not_gt (fun h => hGood (Sum.inl (u,v,x)) ⟨⟨huv,hk⟩,h⟩)
      have hs : Pool u v x ∩ liftVertexSet A W = commonNbrs H (H.lab x) u v ∩ liftVertexSet A W := by
        ext z
        simp only [Pool,mem_inter,mem_sdiff]
        constructor
        · rintro ⟨⟨hp,_⟩,hw⟩; exact ⟨hp,hw⟩
        · rintro ⟨hp,hw⟩; exact ⟨⟨hp,(mem_sdiff.mp (hLift hw)).2⟩,hw⟩
      rwa [hs] at hc
    · have hEmpty : commonNbrs H k u v = ∅ := by
        apply eq_empty_iff_forall_notMem.mpr
        intro z hz
        exact hkV ⟨z,((mem_filter.mp hz).2).2.2⟩
      have hFull := h3 u v huv k hk
      rw [hEmpty,card_empty,Nat.cast_zero] at hFull
      have hnR : (0 : ℝ) < Fintype.card V := by exact_mod_cast hnPos
      nlinarith [mul_pos hα hnR]
  · intro v x y ht
    have hc : (a / 2) * (Fintype.card V : ℝ)^m * q^m / 2 ≤
        (((Paths v x y).filter (fun p => intlSet m p ⊆ liftVertexSet A W)).card : ℝ) :=
      le_of_not_gt (fun h => hGood (Sum.inr (v,x,y)) ⟨ht,h⟩)
    have hs : (Paths v x y).filter (fun p => intlSet m p ⊆ liftVertexSet A W) =
        pathsIn (link H.G H.lab F v) m x y (liftVertexSet A W) := by
      dsimp only [Paths,pathsIn]
      rw [filter_filter]
      apply filter_congr
      intro p _
      exact ⟨fun h => h.2, fun h => ⟨h.trans hLift,h⟩⟩
    rwa [hs] at hc

#print axioms native_outer_tests
end TypedTriangle.Vortex
