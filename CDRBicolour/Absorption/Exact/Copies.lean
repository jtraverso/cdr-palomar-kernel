/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license.
Authors: Juan Pablo Traverso Gianini
-/
module

public import CDRBicolour.Absorption.Exact.Trade
public import CDRBicolour.Absorption.AACCount
public import CDRBicolour.Absorption.ResidualHinge

/-!
# `m²` edge-disjoint copies of the trade (item 3, exact spectrum)

`m` prime, `m > 8`, every class of size `≥ 3m`.  The copy `q = (s, t) ∈ ℤ_m²` puts the model
point `i ∈ Fin 9` at position `i mod 3` of class `i / 3` (a block of `m` consecutive points) with
value `s + i·t`.  Two copies sharing an edge `{φ_q i, φ_q j}` (`i ≠ j`) satisfy
`s + i t = s' + i t'`, `s + j t = s' + j t'`, so `(i − j)(t − t') = 0` and `q = q'`.

`packP σ` takes, in copy `q`, the half `T₁` if `σ q` and `T₀` otherwise:
* it is a packing of allowed triangles (`packP_allowed`, `packP_disj`);
* its leave does not depend on `σ` (`packP_leave`) and has degree `≤ 81 m` (`degL_leave`);
* its number of `AAC` triangles is `Σ_q (σ q ? 2 : 1)` (`packP_aac`).
-/

@[expose] public section

noncomputable section

namespace CDRBicolour.Absorption.Exact

open Finset TypedTriangle CDRBicolour.Prefix CDRBicolour.Absorption

variable {a b c m : ℕ}

/-- Start of the class `k`. -/
def kst (a b : ℕ) (k : ℕ) : ℕ := if k = 0 then 0 else if k = 1 then a else a + b

/-- Size conditions. -/
structure CopyCond (a b c m : ℕ) : Prop where
  m8 : 8 < m
  ha : 3 * m ≤ a
  hb : 3 * m ≤ b
  hc : 3 * m ≤ c

theorem phi_lt (h : CopyCond a b c m) (i : Fin 9) (x : ℕ) (hx : x < m) :
    kst a b (i.val / 3) + (i.val % 3) * m + x < a + b + c := by
  obtain ⟨_, ha, hb, hc⟩ := h
  fin_cases i <;> simp [kst] <;> omega

/-- The vertex of model point `i` in copy `(s, t)`. -/
def phi [NeZero m] (h : CopyCond a b c m) (q : ZMod m × ZMod m) (i : Fin 9) : Fin (a + b + c) :=
  ⟨kst a b (i.val / 3) + (i.val % 3) * m + (q.1 + (i.val : ZMod m) * q.2).val,
    phi_lt h i _ (ZMod.val_lt _)⟩

theorem phi_val [NeZero m] (h : CopyCond a b c m) (q : ZMod m × ZMod m) (i : Fin 9) :
    (phi h q i).val = kst a b (i.val / 3) + (i.val % 3) * m + (q.1 + (i.val : ZMod m) * q.2).val :=
  rfl

/-- Decoding: equal vertices have equal model point and equal value. -/
theorem phi_eq [NeZero m] (h : CopyCond a b c m) {q q' : ZMod m × ZMod m} {i i' : Fin 9}
    (he : phi h q i = phi h q' i') :
    i = i' ∧ q.1 + (i.val : ZMod m) * q.2 = q'.1 + (i'.val : ZMod m) * q'.2 := by
  have hv := congrArg Fin.val he
  rw [phi_val, phi_val] at hv
  have x1 := ZMod.val_lt (q.1 + (i.val : ZMod m) * q.2)
  have x2 := ZMod.val_lt (q'.1 + (i'.val : ZMod m) * q'.2)
  obtain ⟨_, ha, hb, hc⟩ := h
  have hi := i.isLt
  have hi' := i'.isLt
  have hii : i = i' := by
    fin_cases i <;> fin_cases i' <;> simp [kst] at hv x1 x2 ⊢ <;> omega
  subst hii
  refine ⟨rfl, ZMod.val_injective m (by omega)⟩

theorem phi_inj [NeZero m] (h : CopyCond a b c m) (q : ZMod m × ZMod m) :
    Function.Injective (phi h q) := fun _ _ he => (phi_eq h he).1

/-- The embedding of copy `q`. -/
def phiE [NeZero m] (h : CopyCond a b c m) (q : ZMod m × ZMod m) : Fin 9 ↪ Fin (a + b + c) :=
  ⟨phi h q, phi_inj h q⟩

theorem col3_phi [NeZero m] (h : CopyCond a b c m) (q : ZMod m × ZMod m) (i : Fin 9) :
    col3 a b c (phi h q i) = mcol i := by
  have hv := phi_val h q i
  have x1 := ZMod.val_lt (q.1 + (i.val : ZMod m) * q.2)
  obtain ⟨_, ha, hb, hc⟩ := h
  have hi := i.isLt
  unfold col3
  rw [hv]
  fin_cases i <;> simp [kst, mcol] at x1 ⊢ <;> (try split_ifs) <;> omega

theorem natCast_ne [Fact m.Prime] (hm : 8 < m) {i j : Fin 9} (hij : i ≠ j) :
    ((i.val : ZMod m) - (j.val : ZMod m)) ≠ 0 := by
  intro h
  rw [sub_eq_zero] at h
  have := (ZMod.natCast_eq_natCast_iff' i.val j.val m).mp h
  rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at this
  exact hij (Fin.ext this)

/-- **Two copies sharing an edge coincide.** -/
theorem copy_edge [Fact m.Prime] (h : CopyCond a b c m) {q q' : ZMod m × ZMod m}
    {i j i' j' : Fin 9} (hij : i ≠ j)
    (he : s(phi h q i, phi h q j) = s(phi h q' i', phi h q' j')) : q = q' := by
  have key : ∀ {i j i' j' : Fin 9}, i ≠ j → phi h q i = phi h q' i' →
      phi h q j = phi h q' j' → q = q' := by
    intro i j i' j' hij h1 h2
    obtain ⟨rfl, e1⟩ := phi_eq h h1
    obtain ⟨rfl, e2⟩ := phi_eq h h2
    have ht : ((i.val : ZMod m) - (j.val : ZMod m)) * (q.2 - q'.2) = 0 := by
      linear_combination e1 - e2
    rcases mul_eq_zero.mp ht with h0 | h0
    · exact absurd h0 (natCast_ne h.m8 hij)
    · have ht' : q.2 = q'.2 := sub_eq_zero.mp h0
      have hs : q.1 = q'.1 := by rw [ht'] at e1; linear_combination e1
      exact Prod.ext hs ht'
  rw [Sym2.eq_iff] at he
  rcases he with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact key hij h1 h2
  · exact key hij h1 h2

/-- The half of copy `q` chosen by `σ`. -/
def halfOf [NeZero m] (h : CopyCond a b c m) (σ : ZMod m × ZMod m → Bool)
    (q : ZMod m × ZMod m) : Finset (Finset (Fin (a + b + c))) :=
  if σ q then half1 (phiE h q) else half0 (phiE h q)

/-- The packing of all copies. -/
def packP [NeZero m] (h : CopyCond a b c m) (σ : ZMod m × ZMod m → Bool) :
    Finset (Finset (Fin (a + b + c))) :=
  univ.biUnion (halfOf h σ)

/-- The common leave. -/
def leave [NeZero m] (h : CopyCond a b c m) : Finset (Sym2 (Fin (a + b + c))) :=
  univ.biUnion fun q => (half1 (phiE h q)).biUnion triEdges

theorem mem_halfOf [NeZero m] (h : CopyCond a b c m) {σ : ZMod m × ZMod m → Bool}
    {q : ZMod m × ZMod m} {T : Finset (Fin (a + b + c))} (hT : T ∈ halfOf h σ q) :
    ∃ T₀ : Finset (Fin 9), (T₀ ∈ T1m ∨ T₀ ∈ T0m) ∧ T = T₀.map (phiE h q) := by
  unfold halfOf half1 half0 at hT
  split_ifs at hT
  · obtain ⟨T₀, h₀, rfl⟩ := mem_image.mp hT; exact ⟨T₀, Or.inl h₀, rfl⟩
  · obtain ⟨T₀, h₀, rfl⟩ := mem_image.mp hT; exact ⟨T₀, Or.inr h₀, rfl⟩

/-- Edges of a placed model triangle. -/
theorem edge_of_map [NeZero m] (h : CopyCond a b c m) {q : ZMod m × ZMod m} {T₀ : Finset (Fin 9)}
    {e : Sym2 (Fin (a + b + c))} (he : e ∈ triEdges (T₀.map (phiE h q))) :
    ∃ i j : Fin 9, i ≠ j ∧ i ∈ T₀ ∧ j ∈ T₀ ∧ e = s(phi h q i, phi h q j) := by
  rw [triEdges_map, mem_map] at he
  obtain ⟨e', he', rfl⟩ := he
  induction e' using Sym2.ind with
  | _ i j =>
  simp only [triEdges, mem_filter, mk_mem_sym2_iff, Sym2.mk_isDiag_iff] at he'
  exact ⟨i, j, he'.2, he'.1.1, he'.1.2, rfl⟩

theorem packP_allowed [NeZero m] (h : CopyCond a b c m) (σ : ZMod m × ZMod m → Bool) :
    ∀ T ∈ packP h σ, IsAllowed (cdrHost a b c) cdrF T := by
  intro T hT
  obtain ⟨q, -, hq⟩ := mem_biUnion.mp hT
  obtain ⟨T₀, h₀, rfl⟩ := mem_halfOf h hq
  have hc3 : T₀.card = 3 := by
    rcases h₀ with h₀ | h₀
    · exact model_card.1 T₀ h₀
    · exact model_card.2 T₀ h₀
  have hbi : (T₀.image mcol).card = 2 := by
    rcases h₀ with h₀ | h₀
    · exact model_bicol.1 T₀ h₀
    · exact model_bicol.2 T₀ h₀
  refine ⟨by rw [card_map]; exact hc3, fun x _ y _ hxy => hxy, ?_⟩
  refine ⟨by simp [hc3], ?_⟩
  show ((T₀.map (phiE h q)).val.map (col3 a b c)).toFinset.card = 2
  rw [Multiset.toFinset_map, Finset.val_toFinset, Finset.map_eq_image, Finset.image_image]
  have : (col3 a b c ∘ (phiE h q)) = mcol := funext fun i => col3_phi h q i
  rw [this]
  exact hbi

theorem packP_disj [Fact m.Prime] (h : CopyCond a b c m) (σ : ZMod m × ZMod m → Bool) :
    ((packP h σ : Finset (Finset (Fin (a + b + c)))) : Set (Finset (Fin (a + b + c)))).PairwiseDisjoint
      triEdges := by
  intro T hT T' hT' hne
  simp only [mem_coe, packP, mem_biUnion, mem_univ, true_and] at hT hT'
  obtain ⟨q, hq⟩ := hT
  obtain ⟨q', hq'⟩ := hT'
  by_cases hqq : q = q'
  · subst hqq
    unfold halfOf at hq hq'
    split_ifs at hq hq'
    · exact half1_disj (phiE h q) hq hq' hne
    · exact half0_disj (phiE h q) hq hq' hne
  · show Disjoint (triEdges T) (triEdges T')
    rw [Finset.disjoint_left]
    intro e he he'
    obtain ⟨T₀, -, rfl⟩ := mem_halfOf h hq
    obtain ⟨T₀', -, rfl⟩ := mem_halfOf h hq'
    obtain ⟨i, j, hij, -, -, rfl⟩ := edge_of_map h he
    obtain ⟨i', j', -, -, -, he2⟩ := edge_of_map h he'
    exact hqq (copy_edge h hij he2)

theorem packP_leave [NeZero m] (h : CopyCond a b c m) (σ : ZMod m × ZMod m → Bool) :
    (packP h σ).biUnion triEdges = leave h := by
  unfold packP leave
  rw [biUnion_biUnion]
  refine biUnion_congr rfl fun q _ => ?_
  unfold halfOf
  split_ifs
  · rfl
  · exact (union_eq (phiE h q)).symm

set_option linter.constructorNameAsVariable false in
set_option maxHeartbeats 1000000 in
/-- Degree of the leave. -/
theorem degL_leave [NeZero m] (h : CopyCond a b c m) (v : Fin (a + b + c)) :
    degL (leave h) v ≤ 81 * m := by
  -- the neighbours of `v` are `φ_{(x - i t, t)} j` for the model point `i` of `v`
  let sOf : Fin 9 → ZMod m → ZMod m := fun i t =>
    ((v.val - kst a b (i.val / 3) - (i.val % 3) * m : ℕ) : ZMod m) - (i.val : ZMod m) * t
  have hsub : nbL (leave h) v ⊆
      (univ : Finset (Fin 9 × ZMod m × Fin 9)).image fun p => phi h (sOf p.1 p.2.1, p.2.1) p.2.2 := by
    intro w hw
    simp only [nbL, mem_filter, mem_univ, true_and] at hw
    rw [leave, mem_biUnion] at hw
    obtain ⟨q, -, hq⟩ := hw
    rw [mem_biUnion] at hq
    obtain ⟨T, hT, he⟩ := hq
    obtain ⟨T₀, -, rfl⟩ := mem_image.mp hT
    obtain ⟨i, j, -, -, -, he2⟩ := edge_of_map h he
    rw [Sym2.eq_iff] at he2
    -- `v` is `φ_q k` for some `k`, and `w` is `φ_q l`
    have main : ∀ k l : Fin 9, w = phi h q l → v = phi h q k →
        w ∈ (univ : Finset (Fin 9 × ZMod m × Fin 9)).image
          fun p => phi h (sOf p.1 p.2.1, p.2.1) p.2.2 := by
      intro k l hw hv
      refine mem_image.mpr ⟨(k, q.2, l), mem_univ _, ?_⟩
      rw [hw]
      have hs : sOf k q.2 = q.1 := by
        simp only [sOf]
        have hval := phi_val h q k
        rw [← hv] at hval
        rw [show v.val - kst a b (k.val / 3) - (k.val % 3) * m =
          (q.1 + (k.val : ZMod m) * q.2).val by omega]
        rw [ZMod.natCast_zmod_val]; ring
      simp only [hs]
    rcases he2 with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact main j i h1 h2
    · exact main i j h1 h2
  calc degL (leave h) v ≤ #((univ : Finset (Fin 9 × ZMod m × Fin 9)).image
        fun p => phi h (sOf p.1 p.2.1, p.2.1) p.2.2) := card_le_card hsub
    _ ≤ #(univ : Finset (Fin 9 × ZMod m × Fin 9)) := card_image_le
    _ = 81 * m := by simp [Fintype.card_prod, ZMod.card]; ring

/-! ### Counting `AAC` triangles -/

set_option maxRecDepth 100000 in
theorem model_aac' : (T1m.filter fun T => T.val.map mcol = aac).card = 2 ∧
    (T0m.filter fun T => T.val.map mcol = aac).card = 1 := by
  unfold aac; decide +kernel

theorem half_aac [NeZero m] (h : CopyCond a b c m) (q : ZMod m × ZMod m) (S : Finset (Finset (Fin 9))) :
    ∑ Q ∈ S.image (fun T => T.map (phiE h q)),
        (if Q.val.map (col3 a b c) = aac then (1 : ℝ) else 0) =
      ((S.filter fun T => T.val.map mcol = aac).card : ℝ) := by
  rw [sum_image (fun _ _ _ _ he => map_inj (phiE h q) he), sum_boole]
  congr 2
  refine filter_congr fun T _ => ?_
  rw [map_val, Multiset.map_map]
  have : (col3 a b c ∘ (phiE h q)) = mcol := funext fun i => col3_phi h q i
  rw [this]

theorem halves_pairwise [Fact m.Prime] (h : CopyCond a b c m) (σ : ZMod m × ZMod m → Bool) :
    ((univ : Finset (ZMod m × ZMod m)) : Set (ZMod m × ZMod m)).PairwiseDisjoint (halfOf h σ) := by
  intro q _ q' _ hqq
  rw [Function.onFun, Finset.disjoint_left]
  intro T hT hT'
  obtain ⟨T₀, h₀, rfl⟩ := mem_halfOf h hT
  obtain ⟨T₀', -, he⟩ := mem_halfOf h hT'
  -- `T` has an edge, which then lies in both copies
  have hc3 : T₀.card = 3 := by
    rcases h₀ with h₀ | h₀
    · exact model_card.1 T₀ h₀
    · exact model_card.2 T₀ h₀
  obtain ⟨x, y, z, hxy, -, -, rfl⟩ := card_eq_three.mp hc3
  have hmem : s(phiE h q x, phiE h q y) ∈ triEdges (({x, y, z} : Finset (Fin 9)).map (phiE h q)) := by
    rw [triEdges_map, mem_map]
    exact ⟨s(x, y), by simp [triEdges, hxy], rfl⟩
  rw [he] at hmem
  obtain ⟨i', j', -, -, -, he2⟩ := edge_of_map h hmem
  exact hqq (copy_edge h hxy he2)

/-- **`AAC` count of the packing.** -/
theorem packP_aac [Fact m.Prime] (h : CopyCond a b c m) (σ : ZMod m × ZMod m → Bool) :
    ∑ Q ∈ packP h σ, (if Q.val.map (col3 a b c) = aac then (1 : ℝ) else 0) =
      ∑ q : ZMod m × ZMod m, (if σ q then (2 : ℝ) else 1) := by
  unfold packP
  rw [sum_biUnion (halves_pairwise h σ)]
  refine sum_congr rfl fun q _ => ?_
  unfold halfOf half1 half0
  split_ifs
  · rw [half_aac, model_aac'.1]; norm_num
  · rw [half_aac, model_aac'.2]; norm_num

end CDRBicolour.Absorption.Exact
