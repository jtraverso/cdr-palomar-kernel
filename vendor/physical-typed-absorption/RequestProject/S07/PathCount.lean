/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import Mathlib

@[expose] public section

/-!
# V24 / S07 §§1–2: counting walks with prescribed internal coincidences

Walks of length `m+1` from `x` to `y` are encoded by their `m` INTERNAL vertices
`intl m p : Fin m → V`, `intl m p i = p.getVert (i+1)` (injective on walks of that length).
All bad events are covered by sets of tuples with one or two prescribed coordinates, whose
cardinalities are exact powers of `N = |V|`.

* `card_nonpath_le`: at most `(m+1)² N^(m-1)` walks of length `m+1` between distinct `x,y`
  are not simple paths (S07 §1: "los que repiten un vértice").
* `card_through_le`: at most `|Z| m N^(m-1)` of them have an internal vertex in `Z`.
* `card_edgeB_le`: at most `(m+1) d N^(m-1)` of them use an edge of a graph `B` with
  maximum degree `≤ d` (S07 (2.1): endpoint steps `≤ d` choices, internal steps
  `≤ N d` oriented edges).
-/

open Finset

namespace S07V24

variable {V : Type*} [Fintype V] [DecidableEq V]

/-! ### Tuples with prescribed coordinates -/

lemma card_constr (m : ℕ) (P : Finset (Fin m)) (g : Fin m → V) :
    (univ.filter fun s : Fin m → V => ∀ i ∈ P, s i = g i).card =
      Fintype.card V ^ (m - P.card) := by
  have e : (univ.filter fun s : Fin m → V => ∀ i ∈ P, s i = g i) =
      Fintype.piFinset (fun i => if i ∈ P then {g i} else univ) := by
    ext s; simp only [mem_filter, mem_univ, true_and, Fintype.mem_piFinset]
    constructor
    · intro h i; split_ifs with hi
      · rw [mem_singleton]; exact h i hi
      · exact mem_univ _
    · intro h i hi; have := h i; rw [if_pos hi, mem_singleton] at this; exact this
  rw [e, Fintype.card_piFinset]
  have : ∀ i, (if i ∈ P then ({g i} : Finset V) else univ).card =
      if i ∈ P then 1 else Fintype.card V := by
    intro i; split_ifs <;> simp
  simp only [this]
  rw [Finset.prod_ite, Finset.prod_const_one, one_mul, Finset.prod_const]
  congr 1
  rw [Finset.filter_not, Finset.card_sdiff_of_subset (Finset.filter_subset _ _)]
  simp only [Finset.card_univ, Fintype.card_fin]
  congr 1; congr 1; ext i; simp

lemma card_hit (m : ℕ) (a : Fin m) (v : V) :
    (univ.filter fun s : Fin m → V => s a = v).card = Fintype.card V ^ (m - 1) := by
  have := card_constr m {a} (fun _ => v)
  simp only [mem_singleton, forall_eq, card_singleton] at this
  exact this

lemma card_hit2 (m : ℕ) (a b : Fin m) (hab : a ≠ b) (u w : V) :
    (univ.filter fun s : Fin m → V => s a = u ∧ s b = w).card = Fintype.card V ^ (m - 2) := by
  have := card_constr m {a, b} (fun i => if i = a then u else w)
  rw [Finset.card_pair hab] at this
  rw [← this]; congr 1; ext s
  simp only [mem_filter, mem_univ, true_and, mem_insert, mem_singleton, forall_eq_or_imp,
    forall_eq, ite_true, if_neg hab.symm]

lemma card_pair_le (m : ℕ) (a b : Fin m) (hab : a ≠ b) :
    (univ.filter fun s : Fin m → V => s a = s b).card ≤ Fintype.card V ^ (m - 1) := by
  have hm : 2 ≤ m := by
    have h1 := a.isLt; have h2 := b.isLt
    have : a.val ≠ b.val := fun h => hab (Fin.ext h); omega
  have hsub : (univ.filter fun s : Fin m → V => s a = s b) ⊆
      univ.biUnion fun z : V => univ.filter fun s : Fin m → V => s a = z ∧ s b = z := by
    intro s hs; simp only [mem_filter, mem_univ, true_and] at hs
    simp only [mem_biUnion, mem_univ, true_and, mem_filter]; exact ⟨s b, hs, rfl⟩
  refine (card_le_card hsub).trans ((card_biUnion_le).trans ?_)
  simp only [card_hit2 m a b hab, sum_const, card_univ, smul_eq_mul]
  rw [← pow_succ']; apply le_of_eq; congr 1; omega

/-! ### Walks and their internal tuples -/

variable (G : SimpleGraph V) [DecidableRel G.Adj]

/-- simple paths of length exactly `t` from `x` to `y` -/
def pathsLen (t : ℕ) (x y : V) : Finset (G.Walk x y) :=
  (G.finsetWalkLength t x y).filter fun p => p.IsPath

variable {G}

/-- internal vertices of a walk of length `m+1` -/
def intl (m : ℕ) {x y : V} (p : G.Walk x y) : Fin m → V := fun i => p.getVert (i.val + 1)

lemma card_walks_eq (t : ℕ) (x y : V) :
    ((G.adjMatrix ℝ) ^ t) x y = (G.finsetWalkLength t x y).card := by
  rw [SimpleGraph.adjMatrix_pow_apply_eq_card_walk, SimpleGraph.card_set_walk_length_eq]

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
lemma intl_injOn (m : ℕ) (x y : V) :
    Set.InjOn (intl (G := G) m (x := x) (y := y)) {p | p.length = m + 1} := by
  intro p hp q hq h
  simp only [Set.mem_setOf_eq] at hp hq
  apply SimpleGraph.Walk.ext_getVert; intro k
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · simp [SimpleGraph.Walk.getVert_zero]
  by_cases hkm : k ≤ m
  · have := congrFun h ⟨k - 1, by omega⟩
    simp only [intl] at this
    rwa [Nat.sub_add_cancel hk] at this
  · rw [SimpleGraph.Walk.getVert_of_length_le _ (by omega),
      SimpleGraph.Walk.getVert_of_length_le _ (by omega)]

omit [Fintype V] [DecidableRel G.Adj] in
lemma card_le_of_intl_mem (m : ℕ) (x y : V) (A : Finset (G.Walk x y))
    (hA : ∀ p ∈ A, p.length = m + 1) (T : Finset (Fin m → V))
    (hT : ∀ p ∈ A, intl m p ∈ T) : A.card ≤ T.card := by
  rw [← Finset.card_image_of_injOn (f := intl m) (fun p hp q hq h =>
    intl_injOn m x y (hA p hp) (hA q hq) h)]
  apply card_le_card; intro s hs; rw [mem_image] at hs
  obtain ⟨p, hp, rfl⟩ := hs; exact hT p hp

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
/-- a non-simple walk of length `m+1` between distinct ends has a repeated internal vertex
or an internal vertex equal to an end -/
lemma intl_of_not_path (m : ℕ) {x y : V} (hxy : x ≠ y) (p : G.Walk x y)
    (hl : p.length = m + 1) (hp : ¬ p.IsPath) :
    (∃ a b : Fin m, a ≠ b ∧ intl m p a = intl m p b) ∨ (∃ a : Fin m, intl m p a = x) ∨
      (∃ a : Fin m, intl m p a = y) := by
  rw [← SimpleGraph.Walk.IsPath.getVert_injOn_iff] at hp
  simp only [Set.InjOn, Set.mem_setOf_eq, not_forall] at hp
  obtain ⟨i, hi, j, hj, hij, hne⟩ := hp
  rw [hl] at hi hj
  -- wlog i < j
  have key : ∀ i j : ℕ, i ≤ m + 1 → j ≤ m + 1 → i < j → p.getVert i = p.getVert j →
      (∃ a b : Fin m, a ≠ b ∧ intl m p a = intl m p b) ∨ (∃ a : Fin m, intl m p a = x) ∨
        (∃ a : Fin m, intl m p a = y) := by
    intro i' j' hi' hj' hlt heq
    rcases Nat.eq_zero_or_pos i' with rfl | hi0
    · rw [SimpleGraph.Walk.getVert_zero] at heq
      by_cases hjm : j' = m + 1
      · rw [hjm, SimpleGraph.Walk.getVert_of_length_le p (i := m + 1) (by omega)] at heq
        exact absurd heq hxy
      · right; left; refine ⟨⟨j' - 1, by omega⟩, ?_⟩
        simp only [intl]; rw [Nat.sub_add_cancel (by omega)]; exact heq.symm
    · by_cases hjm : j' = m + 1
      · rw [hjm, SimpleGraph.Walk.getVert_of_length_le p (i := m + 1) (by omega)] at heq
        right; right; refine ⟨⟨i' - 1, by omega⟩, ?_⟩
        simp only [intl]; rw [Nat.sub_add_cancel (by omega)]; exact heq
      · left
        refine ⟨⟨i' - 1, by omega⟩, ⟨j' - 1, by omega⟩, ?_, ?_⟩
        · intro h; simp only [Fin.mk.injEq] at h; omega
        · simp only [intl]; rw [Nat.sub_add_cancel (by omega), Nat.sub_add_cancel (by omega)]
          exact heq
  rcases lt_or_gt_of_ne hne with h | h
  · exact key i j hi hj h hij
  · exact key j i hj hi h hij.symm

/-- **Non-simple walks are few**: `≤ (m+1)² N^(m-1)`. -/
theorem card_nonpath_le (m : ℕ) {x y : V} (hxy : x ≠ y) :
    ((G.finsetWalkLength (m + 1) x y).filter fun p => ¬ p.IsPath).card ≤
      (m + 1) ^ 2 * Fintype.card V ^ (m - 1) := by
  set T : Finset (Fin m → V) :=
    ((univ.filter fun ab : Fin m × Fin m => ab.1 ≠ ab.2).biUnion fun ab =>
      univ.filter fun s : Fin m → V => s ab.1 = s ab.2) ∪
    (univ.biUnion fun a : Fin m => univ.filter fun s : Fin m → V => s a = x) ∪
    (univ.biUnion fun a : Fin m => univ.filter fun s : Fin m → V => s a = y)
  have h1 := card_le_of_intl_mem m x y
    ((G.finsetWalkLength (m + 1) x y).filter fun p => ¬ p.IsPath) (fun p hp => by
      simp only [mem_filter, SimpleGraph.mem_finsetWalkLength_iff] at hp; exact hp.1) T
    (fun p hp => by
      simp only [mem_filter, SimpleGraph.mem_finsetWalkLength_iff] at hp
      rcases intl_of_not_path m hxy p hp.1 hp.2 with ⟨a, b, hab, h⟩ | ⟨a, h⟩ | ⟨a, h⟩
      · simp only [T, mem_union, mem_biUnion, mem_filter, mem_univ, true_and]
        left; left; exact ⟨(a, b), hab, h⟩
      · simp only [T, mem_union, mem_biUnion, mem_filter, mem_univ, true_and]
        left; right; exact ⟨a, h⟩
      · simp only [T, mem_union, mem_biUnion, mem_filter, mem_univ, true_and]
        right; exact ⟨a, h⟩)
  refine h1.trans ?_
  set N := Fintype.card V
  have hA : ((univ.filter fun ab : Fin m × Fin m => ab.1 ≠ ab.2).biUnion fun ab =>
      univ.filter fun s : Fin m → V => s ab.1 = s ab.2).card ≤ m * m * N ^ (m - 1) := by
    refine card_biUnion_le.trans ?_
    calc ∑ ab ∈ univ.filter (fun ab : Fin m × Fin m => ab.1 ≠ ab.2),
          (univ.filter fun s : Fin m → V => s ab.1 = s ab.2).card
        ≤ ∑ _ab ∈ univ.filter (fun ab : Fin m × Fin m => ab.1 ≠ ab.2), N ^ (m - 1) :=
          sum_le_sum fun ab hab => card_pair_le m ab.1 ab.2 (by simpa using hab)
      _ ≤ ∑ _ab : Fin m × Fin m, N ^ (m - 1) :=
          sum_le_sum_of_subset_of_nonneg (filter_subset _ _) (fun _ _ _ => Nat.zero_le _)
      _ = m * m * N ^ (m - 1) := by simp [card_univ]
  have hB : ∀ v : V, (univ.biUnion fun a : Fin m =>
      univ.filter fun s : Fin m → V => s a = v).card ≤ m * N ^ (m - 1) := by
    intro v
    refine card_biUnion_le.trans ?_
    simp [card_hit, N]
  calc T.card ≤ _ + _ := card_union_le _ _
    _ ≤ (m * m * N ^ (m - 1) + m * N ^ (m - 1)) + m * N ^ (m - 1) := by
        gcongr
        · exact (card_union_le _ _).trans (add_le_add hA (hB x))
        · exact hB y
    _ ≤ (m + 1) ^ 2 * N ^ (m - 1) := by nlinarith [Nat.zero_le (N ^ (m - 1))]

/-- **Walks to paths**: `#paths ≥ #walks - (m+1)² N^(m-1)`. -/
theorem card_paths_ge (m : ℕ) {x y : V} (hxy : x ≠ y) :
    ((G.adjMatrix ℝ) ^ (m + 1)) x y - (m + 1) ^ 2 * (Fintype.card V : ℝ) ^ (m - 1) ≤
      (pathsLen G (m + 1) x y).card := by
  rw [card_walks_eq]
  have := Finset.card_filter_add_card_filter_not
    (s := G.finsetWalkLength (m + 1) x y) (fun p => p.IsPath)
  have h2 := card_nonpath_le (G := G) m hxy
  unfold pathsLen
  have : ((G.finsetWalkLength (m + 1) x y).card : ℝ) =
      ((G.finsetWalkLength (m + 1) x y).filter fun p => p.IsPath).card +
      ((G.finsetWalkLength (m + 1) x y).filter fun p => ¬ p.IsPath).card := by
    rw [← this]; push_cast; ring
  rw [this]
  have h3 : (((G.finsetWalkLength (m + 1) x y).filter fun p => ¬ p.IsPath).card : ℝ) ≤
      (m + 1) ^ 2 * (Fintype.card V : ℝ) ^ (m - 1) := by exact_mod_cast h2
  linarith

omit [DecidableRel G.Adj] in
/-- paths with an internal vertex in `Z` -/
theorem card_through_le (m : ℕ) (x y : V) (A : Finset (G.Walk x y))
    (hA : ∀ p ∈ A, p.length = m + 1) (Z : Finset V) :
    (A.filter fun p => ∃ i : Fin m, intl m p i ∈ Z).card ≤
      Z.card * m * Fintype.card V ^ (m - 1) := by
  set T : Finset (Fin m → V) := Z.biUnion fun z =>
    univ.biUnion fun a : Fin m => univ.filter fun s : Fin m → V => s a = z
  have h1 := card_le_of_intl_mem m x y (A.filter fun p => ∃ i : Fin m, intl m p i ∈ Z)
    (fun p hp => hA p (mem_filter.1 hp).1) T
    (fun p hp => by
      obtain ⟨i, hi⟩ := (mem_filter.1 hp).2
      simp only [T, mem_biUnion, mem_univ, true_and, mem_filter]
      exact ⟨_, hi, i, rfl⟩)
  refine h1.trans (card_biUnion_le.trans ?_)
  calc ∑ z ∈ Z, (univ.biUnion fun a : Fin m =>
        univ.filter fun s : Fin m → V => s a = z).card
      ≤ ∑ _z ∈ Z, m * Fintype.card V ^ (m - 1) := by
        apply sum_le_sum; intro z _
        refine card_biUnion_le.trans ?_; simp [card_hit]
    _ = _ := by rw [sum_const, smul_eq_mul]; ring

omit [DecidableRel G.Adj] in
/-- walks using an edge of `B` (as consecutive vertices) -/
theorem card_edgeB_le (m : ℕ) (x y : V) (A : Finset (G.Walk x y))
    (hA : ∀ p ∈ A, p.length = m + 1) (B : SimpleGraph V) [DecidableRel B.Adj] (d : ℕ)
    (hB : ∀ v, B.degree v ≤ d) :
    (A.filter fun p : G.Walk x y => ∃ k ∈ Finset.range (m + 1), B.Adj (p.getVert k) (p.getVert (k + 1))).card ≤
      (m + 1) * d * Fintype.card V ^ (m - 1) := by
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · -- length one: the only step joins `x` and `y`
    have : (A.filter fun p : G.Walk x y => ∃ k ∈ Finset.range (0 + 1), B.Adj (p.getVert k) (p.getVert (k + 1))).card
        ≤ 1 := by
      apply Finset.card_le_one.2
      intro p hp q hq
      exact intl_injOn 0 x y (hA p (mem_filter.1 hp).1) (hA q (mem_filter.1 hq).1)
        (funext fun i => Fin.elim0 i)
    rcases Nat.eq_zero_or_pos d with rfl | hd
    · -- no `B`-edges at all
      have h0 : (A.filter fun p : G.Walk x y => ∃ k ∈ Finset.range (0 + 1), B.Adj (p.getVert k) (p.getVert (k + 1)))
          = ∅ := by
        apply Finset.filter_false_of_mem; intro p _ ⟨k, _, hk⟩
        have := hB (p.getVert k)
        rw [Nat.le_zero, ← SimpleGraph.card_neighborFinset_eq_degree, Finset.card_eq_zero] at this
        have hmem : p.getVert (k + 1) ∈ B.neighborFinset (p.getVert k) := by simpa using hk
        rw [this] at hmem; simp at hmem
      rw [h0]; simp
    · calc _ ≤ 1 := this
        _ ≤ (0 + 1) * d * Fintype.card V ^ (0 - 1) := by simp; omega
  set N := Fintype.card V
  -- the cover
  set nb : V → Finset V := fun v => B.neighborFinset v
  set T0 : Finset (Fin m → V) := (nb x).biUnion fun z =>
    univ.filter fun s : Fin m → V => s ⟨0, hm⟩ = z
  set TL : Finset (Fin m → V) := (nb y).biUnion fun z =>
    univ.filter fun s : Fin m → V => s ⟨m - 1, by omega⟩ = z
  set TI : Finset (Fin m → V) := (univ.filter fun k : Fin m => 0 < k.val).biUnion fun k =>
    (univ.filter fun uw : V × V => B.Adj uw.1 uw.2).biUnion fun uw =>
      univ.filter fun s : Fin m → V => s ⟨k.val - 1, by omega⟩ = uw.1 ∧ s k = uw.2
  have hcov : ∀ p ∈ A.filter (fun p : G.Walk x y => ∃ k ∈ Finset.range (m + 1), B.Adj (p.getVert k) (p.getVert (k + 1))),
      intl m p ∈ T0 ∪ TL ∪ TI := by
    intro p hp
    obtain ⟨hpA, k, hk, hadj⟩ := mem_filter.1 hp
    rw [Finset.mem_range] at hk
    have hl := hA p hpA
    simp only [T0, TL, TI, nb, mem_union, mem_biUnion, mem_filter, mem_univ, true_and,
      SimpleGraph.mem_neighborFinset]
    rcases Nat.eq_zero_or_pos k with rfl | hk0
    · left; left
      refine ⟨_, ?_, rfl⟩
      simp only [intl, zero_add]; rw [SimpleGraph.Walk.getVert_zero] at hadj; exact hadj
    by_cases hkm : k = m
    · left; right
      refine ⟨_, ?_, rfl⟩
      rw [hkm, SimpleGraph.Walk.getVert_of_length_le p (i := m + 1) (by omega)] at hadj
      simp only [intl]; rw [Nat.sub_add_cancel hm]; exact hadj.symm
    · right
      refine ⟨⟨k, by omega⟩, hk0, (intl m p ⟨k - 1, by omega⟩, intl m p ⟨k, by omega⟩), ?_,
        rfl, rfl⟩
      simp only [intl]; rw [Nat.sub_add_cancel hk0]; exact hadj
  have h1 := card_le_of_intl_mem m x y _ (fun p hp => hA p (mem_filter.1 hp).1) _ hcov
  refine h1.trans ((card_union_le _ _).trans (add_le_add (card_union_le _ _) le_rfl) |>.trans ?_)
  have hT0 : ∀ (v : V) (a : Fin m), ((nb v).biUnion fun z =>
      univ.filter fun s : Fin m → V => s a = z).card ≤ d * N ^ (m - 1) := by
    intro v a
    refine card_biUnion_le.trans ?_
    simp only [card_hit, sum_const, smul_eq_mul]
    apply Nat.mul_le_mul_right
    simp only [nb, SimpleGraph.card_neighborFinset_eq_degree]; exact hB v
  have hTI : TI.card ≤ (m - 1) * d * N ^ (m - 1) := by
    refine card_biUnion_le.trans ?_
    have hcardk : (univ.filter fun k : Fin m => 0 < k.val).card ≤ m - 1 := by
      have : (univ.filter fun k : Fin m => 0 < k.val) ⊆ univ.erase ⟨0, hm⟩ := by
        intro k hk; simp only [mem_filter, mem_univ, true_and] at hk
        simp only [mem_erase, mem_univ, and_true]; intro h; rw [h] at hk; simp at hk
      refine (card_le_card this).trans ?_; simp
    have hdarts : (univ.filter fun uw : V × V => B.Adj uw.1 uw.2).card ≤ N * d := by
      have : (univ.filter fun uw : V × V => B.Adj uw.1 uw.2) =
          univ.biUnion fun u : V => (B.neighborFinset u).map ⟨fun w => (u, w), fun a b h => by
            simpa using h⟩ := by
        ext ⟨u, w⟩
        simp only [mem_filter,mem_univ,true_and,mem_biUnion,mem_map,
          SimpleGraph.mem_neighborFinset]
        constructor
        · intro hu
          exact ⟨u,w,hu,rfl⟩
        · rintro ⟨a,b,hab,heq⟩
          have ha : a = u := congrArg Prod.fst heq
          have hb : b = w := congrArg Prod.snd heq
          simpa only [ha,hb] using hab
      rw [this]; refine card_biUnion_le.trans ?_
      calc ∑ u : V, ((B.neighborFinset u).map _).card ≤ ∑ _u : V, d := by
            apply sum_le_sum; intro u _; rw [card_map, SimpleGraph.card_neighborFinset_eq_degree]
            exact hB u
        _ = N * d := by rw [sum_const, card_univ, smul_eq_mul]
    calc ∑ k ∈ univ.filter (fun k : Fin m => 0 < k.val),
          ((univ.filter fun uw : V × V => B.Adj uw.1 uw.2).biUnion fun uw =>
            univ.filter fun s : Fin m → V => s ⟨k.val - 1, by omega⟩ = uw.1 ∧ s k = uw.2).card
        ≤ ∑ _k ∈ univ.filter (fun k : Fin m => 0 < k.val), d * N ^ (m - 1) := by
          apply sum_le_sum; intro k hk
          simp only [mem_filter, mem_univ, true_and] at hk
          refine card_biUnion_le.trans ?_
          have hne : (⟨k.val - 1, by omega⟩ : Fin m) ≠ k := by
            intro h; have := congrArg Fin.val h; simp at this; omega
          simp only [card_hit2 m _ _ hne, sum_const, smul_eq_mul]
          calc _ ≤ N * d * N ^ (m - 2) := Nat.mul_le_mul_right _ hdarts
            _ = d * N ^ (m - 1) := by
              have hm2 : 2 ≤ m := by have := k.isLt; omega
              rw [show m - 1 = (m - 2) + 1 by omega, pow_succ]; ring
      _ ≤ (m - 1) * (d * N ^ (m - 1)) := by
          rw [sum_const, smul_eq_mul]; exact Nat.mul_le_mul_right _ hcardk
      _ = (m - 1) * d * N ^ (m - 1) := by ring
  calc _ ≤ d * N ^ (m - 1) + d * N ^ (m - 1) + (m - 1) * d * N ^ (m - 1) :=
        add_le_add (add_le_add (hT0 x _) (hT0 y _)) hTI
    _ = (m + 1) * d * N ^ (m - 1) := by
        have : m + 1 = 2 + (m - 1) := by omega
        rw [this]; ring

end S07V24
