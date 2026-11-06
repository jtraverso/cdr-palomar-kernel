/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import RequestProject.S10K.SourceReach
set_option maxHeartbeats 4000000 -- build option (original: -DmaxHeartbeats=1600000; raised)
set_option maxRecDepth 16384 -- build option (original: -DmaxRecDepth=8192; raised)

@[expose] public section

/-!
# V23: decoding a positive-probability outcome of one source process

An outcome is `ω : Fin 12 → Opt V`; `G12 ω j` is its `j`-th answer. The decoded choices are
`ob1, ob2, ob3` (pivot apices), `oc` (bridge), `oJ1, oJ2` (hinges), `oc1, oJ3, oJ4` and
`oc2, oJ5, oJ6` (the two one-deleted-edge transports).

* `step_mem` : answer `k` of a positive-weight outcome lies in the option set of its own
  history (as computed by `stepOpts`), with exposed set `HSk ω k`.
* `HSk_card` : at most `3 + 12h` exposed vertices.
* `reach_valid` (**main result of the file**): under H3, H4, `h ≥ 6`, `α > 0`, `n ≥ n₀`,
  every positive-weight outcome of a permitted source satisfies `SrcValid`.
-/

open Finset

noncomputable section
open Classical

namespace S10V23.Proc

open TypedTriangle.SparseEdge S10V22 S10V23

variable {V I : Type*} [Fintype V] {G : SimpleGraph V} {lab : V → I} {F : Set (Multiset I)}
  {al : ℝ} {hh : ℕ}

/-- The `j`-th answer of an outcome (dummy beyond 12). -/
def G12 (ω : Fin 12 → Opt V) (j : ℕ) : Opt V := if h : j < 12 then ω ⟨j, h⟩ else dflt

/-- Answers before query `k`. -/
def restr (k : ℕ) (g : ℕ → Opt V) (j : ℕ) : Opt V := if j < k then g j else dflt

/-- Exposed vertices before query `k`. -/
def HSk (u v a : V) (ω : Fin 12 → Opt V) (k : ℕ) : Finset V :=
  {u, v, a} ∪ (range k).biUnion (fun j => vsO (G12 ω j))

/-- Decoded choices. -/
def ob1 (u : V) (ω : Fin 12 → Opt V) : V := gv u (G12 ω 0)
def ob2 (u : V) (ω : Fin 12 → Opt V) : V := gv u (G12 ω 1)
def ob3 (u : V) (ω : Fin 12 → Opt V) : V := gv u (G12 ω 2)
def oc (u : V) (ω : Fin 12 → Opt V) : V := gv u (G12 ω 3)
def oJ1 (ω : Fin 12 → Opt V) : Finset (Sym2 V) := gJ (G12 ω 4)
def oJ2 (ω : Fin 12 → Opt V) : Finset (Sym2 V) := gJ (G12 ω 5)
def oc1 (u : V) (ω : Fin 12 → Opt V) : V := gv u (G12 ω 6)
def oJ3 (ω : Fin 12 → Opt V) : Finset (Sym2 V) := gJ (G12 ω 7)
def oJ4 (ω : Fin 12 → Opt V) : Finset (Sym2 V) := gJ (G12 ω 8)
def oc2 (u : V) (ω : Fin 12 → Opt V) : V := gv u (G12 ω 9)
def oJ5 (ω : Fin 12 → Opt V) : Finset (Sym2 V) := gJ (G12 ω 10)
def oJ6 (ω : Fin 12 → Opt V) : Finset (Sym2 V) := gJ (G12 ω 11)

omit [Fintype V] in
lemma G12_of_lt (ω : Fin 12 → Opt V) {j : ℕ} (hj : j < 12) : G12 ω j = ω ⟨j, hj⟩ := by
  simp [G12, hj]

omit [Fintype V] in
lemma getD_pre (ω : Fin 12 → Opt V) (k : ℕ) (hk : k ≤ 12) :
    (fun j => (Expo.pre ω k hk).getD j dflt) = restr k (G12 ω) := by
  funext j
  unfold restr
  by_cases hj : j < k
  · rw [if_pos hj, Expo.pre_getD ω k hk j hj, G12_of_lt]
  · rw [if_neg hj, List.getD_eq_default]
    rw [Expo.pre_length]; omega

lemma HS_pre (u v a : V) (ω : Fin 12 → Opt V) (k : ℕ) (hk : k ≤ 12) :
    HS u v a (Expo.pre ω k hk) = HSk u v a ω k := by
  ext x
  simp only [HS, HSk, Finset.mem_union, Finset.mem_biUnion, List.mem_toFinset, Expo.pre,
    List.mem_ofFn, Finset.mem_range]
  constructor
  · rintro (h | ⟨o, ⟨i, rfl⟩, hx⟩)
    · exact Or.inl h
    · right
      refine ⟨i.val, i.isLt, ?_⟩
      rw [G12_of_lt ω (by omega)]
      exact hx
  · rintro (h | ⟨j, hj, hx⟩)
    · exact Or.inl h
    · right
      refine ⟨_, ⟨⟨j, hj⟩, rfl⟩, ?_⟩
      rw [G12_of_lt ω (by omega)] at hx
      exact hx

/-- **Answer `k` lies in the option set of its own history.** -/
theorem step_mem {u v a : V} {ω : Fin 12 → Opt V}
    (hw : Expo.wt (opts G lab F al hh u v a) 12 [] ω ≠ 0) (k : ℕ) (hk : k < 12) :
    G12 ω k ∈ nz (stepOpts G lab F al hh u v a k (restr k (G12 ω)) (HSk u v a ω k)) := by
  have := Expo.mem_opts_of_wt_ne_zero (opts G lab F al hh u v a) 12 [] ω hw k hk
  rw [List.nil_append] at this
  unfold opts at this
  rw [Expo.pre_length, getD_pre, HS_pre] at this
  rw [G12_of_lt ω hk]
  exact this

/-! ## Size of the history -/

omit [Fintype V] in
lemma card_vsO_inl (y : V) [Fintype V] : (vsO (Sum.inl y : Opt V)).card = 1 := by
  simp [vsO]

/-- Every possible answer reveals at most `h` vertices (`1 ≤ h`). -/
lemma vsO_card_le (hh1 : 1 ≤ hh) (u v a : V) (k : ℕ) (g : ℕ → Opt V) (Hs : Finset V)
    {o : Opt V} (ho : o ∈ nz (stepOpts G lab F al hh u v a k g Hs)) : (vsO o).card ≤ hh := by
  -- the property for each kind of option set
  have hd : ∀ o ∈ ({dflt} : Finset (Opt V)), (vsO o).card ≤ hh := by
    intro o ho; rw [Finset.mem_singleton.1 ho, vsO_dflt]; simp
  have hA : ∀ p q excl, ∀ o ∈ apexStep G lab F al p q excl, (vsO o).card ≤ hh := by
    intro p q excl o ho
    unfold apexStep at ho
    split_ifs at ho
    · obtain ⟨y, -, rfl⟩ := Finset.mem_image.1 ho
      simp [vsO]; omega
    · simp at ho
  have hH : ∀ p q x y Hs', ∀ o ∈ hingeStep G lab F al hh p q x y Hs', (vsO o).card ≤ hh := by
    intro p q x y Hs' o ho
    unfold hingeStep at ho
    split_ifs at ho with hok
    · obtain ⟨J, hJ, rfl⟩ := Finset.mem_image.1 ho
      simp only [freshSet, Finset.mem_filter, hinges, Finset.mem_univ, true_and] at hJ
      simp only [vsO, Sum.elim_inr]
      rw [hJ.1.2]; exact hok.2.2.2.2.2.2.2.2.1
    · simp at ho
  have hI : ∀ (P : Prop) [Decidable P] (B : Finset (Opt V)),
      (∀ o ∈ B, (vsO o).card ≤ hh) → ∀ o ∈ (if P then {dflt} else B), (vsO o).card ≤ hh := by
    intro P _ B hB o ho
    split_ifs at ho
    · exact hd o ho
    · exact hB o ho
  have hall : ∀ o ∈ stepOpts G lab F al hh u v a k g Hs, (vsO o).card ≤ hh := by
    match k with
    | 0 => exact hA _ _ _
    | 1 => exact hA _ _ _
    | 2 => exact hA _ _ _
    | 3 => exact hA _ _ _
    | 4 => exact hH _ _ _ _ _
    | 5 => exact hH _ _ _ _ _
    | 6 => exact hI _ _ (hA _ _ _)
    | 7 => exact hI _ _ (hH _ _ _ _ _)
    | 8 => exact hI _ _ (hH _ _ _ _ _)
    | 9 => exact hI _ _ (hA _ _ _)
    | 10 => exact hI _ _ (hH _ _ _ _ _)
    | 11 => exact hI _ _ (hH _ _ _ _ _)
    | k + 12 => exact hd
  unfold nz at ho
  split_ifs at ho
  · exact hall o ho
  · exact hd o ho

lemma HSk_card {u v a : V} {ω : Fin 12 → Opt V} (hsmall : ∀ j < 12, (vsO (G12 ω j)).card ≤ hh)
    (k : ℕ) (hk : k ≤ 12) : ((HSk u v a ω k).card : ℝ) ≤ 12 * hh + 3 := by
  have h1 : (HSk u v a ω k).card ≤ 3 + k * hh := by
    unfold HSk
    refine (Finset.card_union_le _ _).trans (add_le_add ?_ ?_)
    · exact Finset.card_le_three
    · refine Finset.card_biUnion_le.trans ?_
      calc ∑ j ∈ range k, (vsO (G12 ω j)).card ≤ ∑ _j ∈ range k, hh :=
            Finset.sum_le_sum fun j hj => hsmall j (by simp at hj; omega)
        _ = k * hh := by simp
  have h2 : 3 + k * hh ≤ 12 * hh + 3 := by nlinarith
  exact_mod_cast h1.trans h2

omit [Fintype V] in
lemma T_subset_HSk [Fintype V] (u v a : V) (ω : Fin 12 → Opt V) (k : ℕ) :
    ({u, v, a} : Finset V) ⊆ HSk u v a ω k := Finset.subset_union_left

lemma vsO_subset_HSk (u v a : V) (ω : Fin 12 → Opt V) {j k : ℕ} (hjk : j < k) :
    vsO (G12 ω j) ⊆ HSk u v a ω k := by
  intro x hx
  exact Finset.mem_union_right _ (Finset.mem_biUnion.2 ⟨j, Finset.mem_range.2 hjk, hx⟩)

end S10V23.Proc
