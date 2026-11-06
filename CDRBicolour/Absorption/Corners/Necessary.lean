/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license.
Authors: Juan Pablo Traverso Gianini
-/
module

public import CDRBicolour.Absorption.Corners.LowerT

/-!
# The exact necessary condition at the lower corner (item 3)

For a vertex `u` of class `X` let `m_u` be the number of blocks `XX(X+2)` through `u` and `k_u`
the number of blocks `(X+1)(X+1)X` with apex `u`.  Counting the pairs at `u`:
`|X| − 1 = #XX(X+1)(u) + m_u` and `|X+1| = #XX(X+1)(u) + 2 k_u`, so `m_u − 2 k_u = |X| − 1 − |X+1|`
(`vertex_balance`).  Summing, with `K_X = Σ k_u = N_{(X+1)(X+1)X}`, `q_X = ⌊K_X/|X|⌋`,
`r_X = K_X mod |X|` and `d_X = |X| − 1 − |X+1| + 2 q_X`:

* `d_X ≥ 0` (each `k_u ≥ −α/2`);
* the edge relation `|X| d_X + 2 r_X = 2 K_{X+2}`;
* the **degree-0 exception**: `d_X = 0` and `r_X ∈ {1, 2}` is impossible (`lower_nec`).

These are exactly the hypotheses of `corner_lower` (apart from smallness).
-/

@[expose] public section

noncomputable section

open Classical

namespace CDRBicolour.Absorption.Corners

open Finset CDRBicolour.Prefix CDRBicolour.Absorption CDRBicolour.BlockTypes

variable {V : Type*} [Fintype V] [DecidableEq V]

theorem fin3_two_iff : ∀ a b c X : Fin 3, ({a, b, c} : Finset (Fin 3)).card = 2 →
    (a = X ∨ b = X ∨ c = X) →
    ((((if a = X then 1 else 0) + (if b = X then 1 else 0) + (if c = X then 1 else 0) : ℕ) = 2 ↔
      (((if a = X + 1 then 1 else 0) + (if b = X + 1 then 1 else 0) +
          (if c = X + 1 then 1 else 0) : ℕ) = 1 ∨
        ((if a = X + 2 then 1 else 0) + (if b = X + 2 then 1 else 0) +
          (if c = X + 2 then 1 else 0) : ℕ) = 1)) ∧
    ¬ ((((if a = X + 1 then 1 else 0) + (if b = X + 1 then 1 else 0) +
          (if c = X + 1 then 1 else 0) : ℕ) = 1) ∧
        (((if a = X + 2 then 1 else 0) + (if b = X + 2 then 1 else 0) +
          (if c = X + 2 then 1 else 0) : ℕ) = 1))) := by
  decide

theorem two_iff (S : STS V) (col : V → Fin 3) (hcol : IsStrictBicolouring S col) {x : V}
    {B : Finset V} (hB : B ∈ S.blocks) (hxB : x ∈ B) :
    (cnt col (col x) B = 2 ↔ (cnt col (col x + 1) B = 1 ∨ cnt col (col x + 2) B = 1)) ∧
      ¬ (cnt col (col x + 1) B = 1 ∧ cnt col (col x + 2) B = 1) := by
  obtain ⟨p, q, r, hpq, hpr, hqr, rfl⟩ := card_eq_three.mp (S.card_eq_three B hB)
  have himg := hcol _ hB
  simp only [image_insert, image_singleton] at himg
  rw [BlockTypes.cnt_triple col _ hpq hpr hqr, BlockTypes.cnt_triple col _ hpq hpr hqr,
    BlockTypes.cnt_triple col _ hpq hpr hqr]
  have hx : col p = col x ∨ col q = col x ∨ col r = col x := by
    simp only [mem_insert, mem_singleton] at hxB
    rcases hxB with rfl | rfl | rfl <;> simp
  exact fin3_two_iff _ _ _ _ himg hx

/-- **Pairs at a vertex inside its class.** -/
theorem vertex_same (S : STS V) (col : V → Fin 3) (hcol : IsStrictBicolouring S col) (x : V) :
    classSize col (col x) - 1 =
      localCount S col (col x + 1) x + localCount S col (col x + 2) x := by
  have hloc : classSize col (col x) - 1 =
      #(S.blocks.filter fun B => x ∈ B ∧ cnt col (col x) B = 2) := by
    have hE := sum_cnt_erase_through S col x
    rw [← hE, card_filter, sum_filter]
    refine sum_congr rfl fun B hB => ?_
    by_cases hxB : x ∈ B
    · have hcard : #((B.erase x).filter fun y => col y = col x) = cnt col (col x) B - 1 := by
        rw [filter_erase, card_erase_of_mem
          (mem_filter.mpr ⟨hxB, rfl⟩ : x ∈ B.filter fun y => col y = col x), cnt]
      have hpos : 1 ≤ cnt col (col x) B :=
        card_pos.mpr ⟨x, (mem_filter.mpr ⟨hxB, rfl⟩ : x ∈ B.filter fun y => col y = col x)⟩
      have hle : cnt col (col x) B ≤ 3 := by
        have := card_filter_le B (fun y => col y = col x)
        rw [S.card_eq_three B hB] at this
        exact this
      have h3 := cnt_ne_three S col hcol (col x) hB
      rw [if_pos hxB, hcard]
      by_cases h2 : cnt col (col x) B = 2
      · simp [h2, hxB]
      · simp only [h2, and_false, if_false]; omega
    · simp [hxB]
  rw [hloc, localCount, localCount, ← card_union_of_disjoint]
  · congr 1
    ext B
    simp only [mem_filter, mem_union]
    constructor
    · rintro ⟨hB, hxB, h2⟩
      rcases ((two_iff S col hcol hB hxB).1.1 h2) with h | h
      · exact Or.inl ⟨hB, hxB, h⟩
      · exact Or.inr ⟨hB, hxB, h⟩
    · rintro (⟨hB, hxB, h⟩ | ⟨hB, hxB, h⟩)
      · exact ⟨hB, hxB, (two_iff S col hcol hB hxB).1.2 (Or.inl h)⟩
      · exact ⟨hB, hxB, (two_iff S col hcol hB hxB).1.2 (Or.inr h)⟩
  · rw [Finset.disjoint_left]
    intro B h1 h2
    simp only [mem_filter] at h1 h2
    exact (two_iff S col hcol h1.1 h1.2.1).2 ⟨h1.2.2, h2.2.2⟩

/-- **Vertex balance**: `m_u − 2 k_u = |X| − 1 − |X+1|`. -/
theorem vertex_balance (S : STS V) (col : V → Fin 3) (hcol : IsStrictBicolouring S col) (x : V) :
    (localCount S col (col x + 2) x : ℤ) - 2 * localCount₂ S col (col x + 1) x =
      (classSize col (col x) : ℤ) - 1 - classSize col (col x + 1) := by
  have h1 := vertex_same S col hcol x
  have h2 := classSize_eq_local S col (j := col x + 1) (x := x) (fin3_ne_add1 _).symm
  have hpos : 1 ≤ classSize col (col x) := card_pos.mpr ⟨x, by simp⟩
  omega

/-- A vertex lies in at most `N` blocks of type `XX(X+2)`. -/
theorem localCount_le (S : STS V) (col : V → Fin 3) (hcol : IsStrictBicolouring S col) (x : V) :
    localCount S col (col x + 2) x ≤ typeCount S col (col x) (col x + 2) := by
  unfold localCount typeCount
  refine card_le_card fun B hB => ?_
  simp only [mem_filter] at hB ⊢
  exact ⟨hB.1, (two_iff S col hcol hB.1 hB.2.1).1.2 (Or.inr hB.2.2), hB.2.2⟩

/-- The degree-`0` exception, in terms of the per-vertex counts of one class. -/
theorem exception_aux (S : STS V) (col : V → Fin 3) (hcol : IsStrictBicolouring S col) (X : Fin 3)
    (m : V → ℕ) (hm : ∀ u, col u = X → m u = localCount S col (X + 2) u)
    (hle : ∀ u, col u = X → m u ≤ typeCount S col X (X + 2))
    (heven : ∀ u, col u = X → Even (m u))
    (hsum : ∑ u ∈ univ.filter (fun u => col u = X), m u = 2 * typeCount S col X (X + 2))
    (hN : typeCount S col X (X + 2) = 1 ∨ typeCount S col X (X + 2) = 2) : False := by
  set N := typeCount S col X (X + 2) with hNdef
  set C := univ.filter fun u => col u = X
  have hval : ∀ u ∈ C, m u = 0 ∨ m u = 2 ∨ N < m u := by
    intro u hu
    have hu' := (mem_filter.1 hu).2
    obtain ⟨k, hk⟩ := heven u hu'
    have := hle u hu'
    rcases hN with h | h <;> omega
  -- every vertex with a positive count lies in all blocks of type `XX(X+2)`
  obtain ⟨T, hTdef⟩ : ∃ T : Finset (Finset V),
      T = S.blocks.filter fun B => cnt col X B = 2 ∧ cnt col (X + 2) B = 1 := ⟨_, rfl⟩
  have hTN : #T = N := by rw [hTdef]; rfl
  have hall : ∀ u ∈ C, m u = N → ∀ B ∈ T, u ∈ B := by
    intro u hu hmu B hB
    have hu' := (mem_filter.1 hu).2
    have hsub : S.blocks.filter (fun B => u ∈ B ∧ cnt col (X + 2) B = 1) ⊆ T := by
      intro B' hB'
      rw [hTdef]
      simp only [mem_filter] at hB' ⊢
      have := (two_iff S col hcol hB'.1 hB'.2.1).1.2
      rw [hu'] at this
      exact ⟨hB'.1, this (Or.inr hB'.2.2), hB'.2.2⟩
    have hcard : #(S.blocks.filter (fun B => u ∈ B ∧ cnt col (X + 2) B = 1)) = #T := by
      rw [hTN, ← hmu, hm u hu']; rfl
    have heq := eq_of_subset_of_card_le hsub hcard.ge
    rw [← heq] at hB
    exact (mem_filter.1 hB).2.1
  rcases hN with h1 | h2
  · -- `N = 1`: some vertex has `m = 2 > N`
    have hpos : ∃ u ∈ C, 0 < m u := by
      by_contra hcon
      push Not at hcon
      have : ∑ u ∈ C, m u = 0 := sum_eq_zero fun u hu => by have := hcon u hu; omega
      omega
    obtain ⟨u, hu, hmu⟩ := hpos
    have := hle u (mem_filter.1 hu).2
    rcases hval u hu with h | h | h <;> omega
  · -- `N = 2`: two vertices lie in both blocks
    have hvals : ∀ u ∈ C, m u = 0 ∨ m u = 2 := by
      intro u hu
      rcases hval u hu with h | h | h
      · exact Or.inl h
      · exact Or.inr h
      · exact absurd (hle u (mem_filter.1 hu).2) (by omega)
    obtain ⟨A, hAdef⟩ : ∃ A : Finset V, A = C.filter fun u => m u = 2 := ⟨_, rfl⟩
    have hA : #A = 2 := by
      have e : ∑ u ∈ C, m u = ∑ u ∈ A, 2 := by
        rw [hAdef, sum_filter (p := fun u => m u = 2)]
        refine sum_congr rfl fun u hu => ?_
        rcases hvals u hu with h | h <;> simp [h]
      rw [e, sum_const, smul_eq_mul] at hsum
      omega
    obtain ⟨u₁, u₂, hne, hA'⟩ := card_eq_two.1 hA
    have hT : #T = 2 := by rw [hTN]; exact h2
    obtain ⟨B₁, B₂, hBne, hT'⟩ := card_eq_two.1 hT
    have m1 : u₁ ∈ A := by rw [hA']; simp
    have m2 : u₂ ∈ A := by rw [hA']; simp
    rw [hAdef] at m1 m2
    have i1 := fun B hB => hall u₁ (mem_filter.1 m1).1 (by rw [(mem_filter.1 m1).2]; omega) B hB
    have i2 := fun B hB => hall u₂ (mem_filter.1 m2).1 (by rw [(mem_filter.1 m2).2]; omega) B hB
    have b1 : B₁ ∈ T := by rw [hT']; simp
    have b2 : B₂ ∈ T := by rw [hT']; simp
    have bb1 : B₁ ∈ S.blocks := by have := b1; rw [hTdef] at this; exact (mem_filter.1 this).1
    have bb2 : B₂ ∈ S.blocks := by have := b2; rw [hTdef] at this; exact (mem_filter.1 this).1
    obtain ⟨B, -, hu⟩ := S.existsUnique_block u₁ u₂ hne
    have e1 := hu B₁ ⟨bb1, i1 B₁ b1, i2 B₁ b1⟩
    have e2 := hu B₂ ⟨bb2, i1 B₂ b2, i2 B₂ b2⟩
    exact hBne (e1.trans e2.symm)

set_option maxHeartbeats 1600000 in
/-- **The exact necessary condition** for a realised profile, in the form of `corner_lower`. -/
theorem lower_nec {a b c : ℕ} (h : AdmissibleProfile a b c) (S : STS (Fin (a + b + c)))
    (hcol : IsStrictBicolouring S (col3 a b c)) :
    ∃ d q r : Fin 3 → ℕ, (∀ X, r X < sz a b c X) ∧
      (∀ X, (d X : ℤ) = sz a b c X - 1 - sz a b c (X + 1) + 2 * q X) ∧
      (∀ X, sz a b c X * d X + 2 * r X = 2 * (sz a b c (X + 2) * q (X + 2) + r (X + 2))) ∧
      (∀ X, ¬ (d X = 0 ∧ (r X = 1 ∨ r X = 2))) ∧
      c * q 2 + r 2 = typeCount S (col3 a b c) 0 2 := by
  set col := col3 a b c with hcoldef
  have hcs : ∀ X, classSize col X = sz a b c X := fun X => by
    rw [← sz_csz]; rfl
  have hpos : ∀ X, 0 < sz a b c X := by
    intro X; fin_cases X
    · exact h.1
    · exact h.2.1
    · exact h.2.2.1
  set K : Fin 3 → ℕ := fun X => typeCount S col (X + 1) X with hK
  set q : Fin 3 → ℕ := fun X => K X / sz a b c X with hq
  set r : Fin 3 → ℕ := fun X => K X % sz a b c X with hr
  -- per class facts
  have key : ∀ X, 0 ≤ (sz a b c X : ℤ) - 1 - sz a b c (X + 1) + 2 * q X ∧
      sz a b c X * ((sz a b c X : ℤ) - 1 - sz a b c (X + 1)) + 2 * K X =
        2 * typeCount S col X (X + 2) ∧
      (((sz a b c X : ℤ) - 1 - sz a b c (X + 1) + 2 * q X = 0) →
        ¬ (r X = 1 ∨ r X = 2)) := by
    intro X
    set C := univ.filter fun u => col u = X
    set α : ℤ := (sz a b c X : ℤ) - 1 - sz a b c (X + 1)
    have hbal : ∀ u ∈ C, (localCount S col (X + 2) u : ℤ) =
        α + 2 * localCount₂ S col (X + 1) u := by
      intro u hu
      have hu' := (mem_filter.1 hu).2
      have := vertex_balance S col hcol u
      rw [hu', hcs, hcs] at this
      linarith
    have hK2 : ∑ u ∈ C, localCount₂ S col (X + 1) u = K X :=
      sum_localCount₂ S col (i := X) (j := X + 1) (fin3_ne_add1 X).symm
    have hm2 : ∑ u ∈ C, localCount S col (X + 2) u = 2 * typeCount S col X (X + 2) :=
      sum_localCount S col hcol (i := X) (j := X + 2) (fin3_add2_ne X).symm
    have hCcard : #C = sz a b c X := hcs X
    have hsumZ : (2 * typeCount S col X (X + 2) : ℤ) = sz a b c X * α + 2 * K X := by
      have e1 := congrArg (Nat.cast : ℕ → ℤ) hm2
      have e2 := congrArg (Nat.cast : ℕ → ℤ) hK2
      push_cast at e1 e2
      rw [← e1, ← e2, sum_congr rfl hbal, sum_add_distrib, sum_const, hCcard, ← mul_sum]
      simp only [nsmul_eq_mul]; try ring
    -- the minimum of `k`
    obtain ⟨u₀, hu₀, hmin⟩ := exists_min_image C (fun u => localCount₂ S col (X + 1) u)
      (card_pos.1 (by rw [hCcard]; exact hpos X))
    have hKmin : sz a b c X * localCount₂ S col (X + 1) u₀ ≤ K X := by
      rw [← hK2, ← hCcard, ← smul_eq_mul, ← sum_const]
      exact sum_le_sum fun u hu => hmin u hu
    have hqmin : localCount₂ S col (X + 1) u₀ ≤ q X := by
      simp only [hq]
      exact (Nat.le_div_iff_mul_le (hpos X)).2 (by rw [mul_comm]; exact hKmin)
    have hb0 := hbal u₀ hu₀
    refine ⟨by first | omega | (push_cast; omega), by rw [hsumZ]; try ring, fun hd0 hr12 => ?_⟩
    -- the exception
    have hKqr : K X = sz a b c X * q X + r X := (Nat.div_add_mod _ _).symm
    have hN : typeCount S col X (X + 2) = r X := by
      have : (2 * typeCount S col X (X + 2) : ℤ) = 2 * r X := by
        rw [hsumZ, hKqr]; push_cast
        have : (sz a b c X : ℤ) * α + 2 * (sz a b c X * q X) = sz a b c X * (α + 2 * q X) := by
          ring
        linarith [show (sz a b c X : ℤ) * (α + 2 * q X) = 0 by rw [hd0]; ring]
      omega
    refine exception_aux S col hcol X (fun u => localCount S col (X + 2) u) (fun _ _ => rfl)
      (fun u hu => by have := localCount_le S col hcol u; rwa [hu] at this) (fun u hu => ?_)
      hm2 (by rw [hN]; exact hr12)
    -- evenness: `m_u = α + 2 k_u` with `α` even
    have hu' : u ∈ C := mem_filter.2 ⟨mem_univ _, hu⟩
    have hb := hbal u hu'
    refine ⟨localCount₂ S col (X + 1) u - q X, ?_⟩
    have hk : q X ≤ localCount₂ S col (X + 1) u := by
      have : (0 : ℤ) ≤ localCount S col (X + 2) u := by positivity
      omega
    omega
  -- assemble
  refine ⟨fun X => ((sz a b c X : ℤ) - 1 - sz a b c (X + 1) + 2 * q X).toNat, q, r,
    fun X => Nat.mod_lt _ (hpos X), fun X => ?_, fun X => ?_, fun X => ?_, ?_⟩
  · exact Int.toNat_of_nonneg (key X).1
  · have k1 := (key X).1
    have k2 := (key X).2.1
    have hKqr : K X = sz a b c X * q X + r X := (Nat.div_add_mod _ _).symm
    have hKqr2 : K (X + 2) = sz a b c (X + 2) * q (X + 2) + r (X + 2) := (Nat.div_add_mod _ _).symm
    have hK2 : K (X + 2) = typeCount S col X (X + 2) := by
      simp only [hK, show X + 2 + 1 = X from fin3_add2_add1 X]
    zify
    rw [Int.toNat_of_nonneg k1]
    have : ((sz a b c (X + 2) * q (X + 2) + r (X + 2) : ℕ) : ℤ) = typeCount S col X (X + 2) := by
      rw [← hKqr2, hK2]
    push_cast at this
    rw [this]
    have hKZ : (K X : ℤ) = sz a b c X * q X + r X := by exact_mod_cast hKqr
    linarith
  · intro ⟨hd0, hr12⟩
    have k1 := (key X).1
    have : (sz a b c X : ℤ) - 1 - sz a b c (X + 1) + 2 * q X = 0 := by
      have := Int.toNat_of_nonneg k1
      dsimp only at hd0
      rw [hd0] at this; push_cast at this; linarith
    exact (key X).2.2 this hr12
  · have : K 2 = typeCount S col 0 2 := rfl
    rw [← this]
    exact Nat.div_add_mod _ _

end CDRBicolour.Absorption.Corners
