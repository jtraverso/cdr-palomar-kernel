/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import RequestProject.PaschEGJ13.TupleEdge
public import RequestProject.PaschEGJ13.TupleMatching2
set_option maxHeartbeats 4000000 -- build option (original: -DmaxHeartbeats=1600000; raised)
set_option maxRecDepth 16384 -- build option (original: -DmaxRecDepth=8192; raised)

/-! # From the bounds of Steps 1–2 to the hypotheses of Step 3

If every `zSum v ≤ B`, then the influence sums `Γ_i(σ)` of Step 3 are at most `ℓ p^{ℓ-1} B`,
and the error term of Step 3 (tuples meeting fewer than `ℓ` parts) is at most
`B · ∑_v c^{|range v|} [|range v| < ℓ]`, which is bounded by counting functions with a
given range size.
-/

@[expose] public section

namespace Pseudorandom

open Finset

/-! ## Counting functions by the size of their range -/

section Count

variable {Y : Type*} [Fintype Y] [DecidableEq Y]

theorem equivFin_val_inj {R R' : Finset Y} (h : R = R') {a a' : Y} (ha : a ∈ R) (ha' : a' ∈ R')
    (he : ((R.equivFin ⟨a, ha⟩ : Fin R.card) : ℕ) = (R'.equivFin ⟨a', ha'⟩ : Fin R'.card)) :
    a = a' := by
  subst h
  have := R.equivFin.injective (Fin.ext he)
  exact congrArg Subtype.val this

theorem card_range_eq_le (ℓ k : ℕ) :
    (univ.filter (fun v : Fin ℓ → Y => (univ.image v).card = k)).card ≤
      Fintype.card Y ^ k * k ^ ℓ := by
  classical
  set Φ : (Fin ℓ → Y) → Finset Y × (Fin ℓ → ℕ) := fun v =>
    (univ.image v, fun m => ((univ.image v).equivFin ⟨v m, mem_image_of_mem v (mem_univ m)⟩ : ℕ))
    with hΦ
  have hmaps : ∀ v ∈ univ.filter (fun v : Fin ℓ → Y => (univ.image v).card = k),
      Φ v ∈ (univ.powersetCard k) ×ˢ (Fintype.piFinset fun _ : Fin ℓ => range k) := by
    intro v hv
    have hk := (mem_filter.mp hv).2
    refine mem_product.mpr ⟨mem_powersetCard.mpr ⟨subset_univ _, hk⟩, ?_⟩
    rw [Fintype.mem_piFinset]
    intro m
    rw [mem_range]
    have := ((univ.image v).equivFin ⟨v m, mem_image_of_mem v (mem_univ m)⟩).2
    simp only [hΦ]
    omega
  have hinj : Set.InjOn Φ (univ.filter (fun v : Fin ℓ → Y => (univ.image v).card = k)) := by
    intro v _ w _ hvw
    simp only [hΦ, Prod.mk.injEq] at hvw
    obtain ⟨h1, h2⟩ := hvw
    funext m
    exact equivFin_val_inj h1 _ _ (congrFun h2 m)
  refine (card_le_card_of_injOn Φ hmaps hinj).trans ?_
  rw [card_product, Fintype.card_piFinset, prod_const, card_range, card_univ, card_powersetCard,
    card_univ, Fintype.card_fin]
  exact Nat.mul_le_mul_right _ (Nat.choose_le_pow _ _)

theorem sum_range_lt_le (ℓ : ℕ) (c : ℝ) (hc : 0 ≤ c) :
    ∑ v : Fin ℓ → Y, (if (univ.image v).card < ℓ then c ^ (univ.image v).card else 0) ≤
      ∑ k ∈ range ℓ, c ^ k * ((Fintype.card Y : ℝ) ^ k * (k : ℝ) ^ ℓ) := by
  classical
  have h1 : ∀ v : Fin ℓ → Y, (if (univ.image v).card < ℓ then c ^ (univ.image v).card else 0) =
      ∑ k ∈ range ℓ, if (univ.image v).card = k then c ^ k else 0 := by
    intro v
    split_ifs with h
    · rw [sum_ite_eq (range ℓ) ((univ.image v).card) (fun k => c ^ k), if_pos (mem_range.mpr h)]
    · refine (sum_eq_zero fun k hk => ?_).symm
      rw [if_neg]
      intro hk'
      exact h (hk' ▸ mem_range.mp hk)
  simp_rw [h1]
  rw [sum_comm]
  refine sum_le_sum fun k _ => ?_
  rw [← sum_filter, sum_const, nsmul_eq_mul, mul_comm]
  refine mul_le_mul_of_nonneg_left ?_ (pow_nonneg hc k)
  exact_mod_cast card_range_eq_le ℓ k

end Count

/-! ## The influence bound -/

variable {V : Type*} [Fintype V] [DecidableEq V] {p q : ℕ}

theorem card_filter_exists_eq_le (ℓ : ℕ) (i : Fin p) :
    (univ.filter (fun u : Fin ℓ → Fin p => ∃ m, u m = i)).card ≤ ℓ * p ^ (ℓ - 1) := by
  classical
  have hsub : univ.filter (fun u : Fin ℓ → Fin p => ∃ m, u m = i) ⊆
      univ.biUnion (fun m : Fin ℓ => univ.filter (fun u : Fin ℓ → Fin p => u m = i)) := by
    intro u hu
    obtain ⟨m, hm⟩ := (mem_filter.mp hu).2
    exact mem_biUnion.mpr ⟨m, mem_univ _, mem_filter.mpr ⟨mem_univ _, hm⟩⟩
  refine (card_le_card hsub).trans (card_biUnion_le.trans ?_)
  have : ∀ m : Fin ℓ, (univ.filter (fun u : Fin ℓ → Fin p => u m = i)).card = p ^ (ℓ - 1) := by
    intro m
    have h := Fintype.card_filter_piFinset_const_eq_of_mem (univ : Finset (Fin p)) m
      (mem_univ i)
    rw [Fintype.piFinset_univ, card_univ, Fintype.card_fin, Fintype.card_fin] at h
    exact h
  rw [sum_congr rfl fun m _ => this m, sum_const, card_univ, Fintype.card_fin, smul_eq_mul]

open Classical in
/-- The influence sums `Γ_i(σ)` of Step 3 are bounded by `ℓ p^{ℓ-1} B`. -/
theorem gamma_le_of_zSum {ℓ : ℕ} (H : Finset (Finset V)) (ω : Finset (Finset V) → ℝ)
    (hω0 : ∀ S ∈ H.powersetCard ℓ, 0 ≤ ω S) (A : Fin p → Finset (Finset V))
    (fc : Finset V → Fin q) (hne : ∀ i, ∀ e ∈ A i, e.Nonempty)
    (hdisj : ∀ i i', i ≠ i' → ∀ e ∈ A i, ∀ g ∈ A i', Disjoint e g)
    (B : ℝ) (hB : 0 ≤ B) (hZ : ∀ v : Fin ℓ → Fin p × Fin q, zSum H ω A v fc ≤ B)
    (i : Fin p) (σ : Fin p → Fin q) :
    ∑ S ∈ H.powersetCard ℓ, ω S *
        ((if S ⊆ univ.biUnion (fun i' => cls A fc i' (σ i')) then 1 else 0) *
          (if ∃ e ∈ S, e ∈ A i then 1 else 0)) ≤ ℓ * (p : ℝ) ^ (ℓ - 1) * B := by
  classical
  set Ui := univ.filter (fun u : Fin ℓ → Fin p => ∃ m, u m = i) with hUi
  set vv : (Fin ℓ → Fin p) → Fin ℓ → Fin p × Fin q := fun u m => (u m, σ (u m)) with hvv
  have key : ∀ S ∈ H.powersetCard ℓ, ω S *
      ((if S ⊆ univ.biUnion (fun i' => cls A fc i' (σ i')) then 1 else 0) *
        (if ∃ e ∈ S, e ∈ A i then 1 else 0)) ≤
      ∑ u ∈ Ui, ω S * (if ∀ e ∈ S, ∃ m, e ∈ A (vv u m).1 ∧ fc e = (vv u m).2 then 1 else 0) := by
    intro S hS
    have hc := (mem_powersetCard.mp hS).2
    have hnn : ∀ u ∈ Ui, 0 ≤ ω S *
        (if ∀ e ∈ S, ∃ m, e ∈ A (vv u m).1 ∧ fc e = (vv u m).2 then (1 : ℝ) else 0) :=
      fun u _ => mul_nonneg (hω0 S hS) (by split_ifs <;> norm_num)
    by_cases h : S ⊆ univ.biUnion (fun i' => cls A fc i' (σ i')) ∧ ∃ e ∈ S, e ∈ A i
    · obtain ⟨h1, e0, he0S, he0⟩ := h
      set eS : Fin ℓ → Finset V := fun m => (S.equivFin.symm (Fin.cast hc.symm m)).1 with heS
      have heSmem : ∀ m, eS m ∈ S := fun m => (S.equivFin.symm (Fin.cast hc.symm m)).2
      have hsurj : ∀ e ∈ S, ∃ m, eS m = e := by
        intro e he
        refine ⟨Fin.cast hc (S.equivFin ⟨e, he⟩), ?_⟩
        have : Fin.cast hc.symm (Fin.cast hc (S.equivFin ⟨e, he⟩)) = S.equivFin ⟨e, he⟩ :=
          Fin.ext rfl
        show (S.equivFin.symm (Fin.cast hc.symm (Fin.cast hc (S.equivFin ⟨e, he⟩)))).1 = e
        rw [this, Equiv.symm_apply_apply]
      have hcls : ∀ m, ∃ i', eS m ∈ cls A fc i' (σ i') := by
        intro m
        obtain ⟨i', -, hi'⟩ := mem_biUnion.mp (h1 (heSmem m))
        exact ⟨i', hi'⟩
      choose u hu using hcls
      have hu' : ∀ m, eS m ∈ A (u m) ∧ fc (eS m) = σ (u m) := fun m => mem_filter.mp (hu m)
      have huUi : u ∈ Ui := by
        obtain ⟨m0, hm0⟩ := hsurj e0 he0S
        refine mem_filter.mpr ⟨mem_univ _, m0, ?_⟩
        exact part_unique hne hdisj (hu' m0).1 (hm0 ▸ he0)
      have hind : ∀ e ∈ S, ∃ m, e ∈ A (vv u m).1 ∧ fc e = (vv u m).2 := by
        intro e he
        obtain ⟨m, rfl⟩ := hsurj e he
        exact ⟨m, (hu' m).1, (hu' m).2⟩
      refine le_trans ?_ (single_le_sum hnn huUi)
      rw [if_pos hind, if_pos h1, if_pos ⟨e0, he0S, he0⟩, mul_one]
    · have : (if S ⊆ univ.biUnion (fun i' => cls A fc i' (σ i')) then (1 : ℝ) else 0) *
          (if ∃ e ∈ S, e ∈ A i then 1 else 0) = 0 := by
        rw [not_and_or] at h
        rcases h with h | h
        · rw [if_neg h, zero_mul]
        · rw [if_neg h, mul_zero]
      rw [this, mul_zero]
      exact sum_nonneg hnn
  refine (sum_le_sum key).trans ?_
  rw [sum_comm]
  calc ∑ u ∈ Ui, ∑ S ∈ H.powersetCard ℓ, ω S *
        (if ∀ e ∈ S, ∃ m, e ∈ A (vv u m).1 ∧ fc e = (vv u m).2 then (1 : ℝ) else 0)
      = ∑ u ∈ Ui, zSum H ω A (vv u) fc := by
        refine sum_congr rfl fun u _ => ?_
        unfold zSum
        rfl
    _ ≤ ∑ _u ∈ Ui, B := sum_le_sum fun u _ => hZ (vv u)
    _ = Ui.card * B := by rw [sum_const, nsmul_eq_mul]
    _ ≤ ℓ * (p : ℝ) ^ (ℓ - 1) * B := by
        refine mul_le_mul_of_nonneg_right ?_ hB
        exact_mod_cast card_filter_exists_eq_le ℓ i

/-! ## The error term -/

open Classical in
/-- The error term of Step 3 is bounded by `B · ∑_v c^{|range v|} [|range v| < ℓ]`. -/
theorem err_le_of_zSum {ℓ : ℕ} (H : Finset (Finset V)) (ω : Finset (Finset V) → ℝ)
    (hω0 : ∀ S ∈ H.powersetCard ℓ, 0 ≤ ω S) (A : Fin p → Finset (Finset V))
    (fc : Finset V → Fin q) (hne : ∀ i, ∀ e ∈ A i, e.Nonempty)
    (hdisj : ∀ i i', i ≠ i' → ∀ e ∈ A i, ∀ g ∈ A i', Disjoint e g)
    (B : ℝ) (hZ : ∀ v : Fin ℓ → Fin p × Fin q, zSum H ω A v fc ≤ B) (c : ℝ) (hc : 0 ≤ c) :
    ∑ S ∈ H.powersetCard ℓ, ω S * (c ^ (partsMet A S).card *
        if InParts A S ∧ ConsCol A fc S ∧ ¬ DistinctParts A S then 1 else 0) ≤
      B * ∑ v : Fin ℓ → Fin p × Fin q,
        (if (univ.image v).card < ℓ then c ^ (univ.image v).card else 0) := by
  classical
  set wv : (Fin ℓ → Fin p × Fin q) → ℝ :=
    fun v => if (univ.image v).card < ℓ then c ^ (univ.image v).card else 0 with hwv
  have hwv0 : ∀ v, 0 ≤ wv v := fun v => by simp only [hwv]; split_ifs <;> positivity
  have key : ∀ S ∈ H.powersetCard ℓ, ω S * (c ^ (partsMet A S).card *
      if InParts A S ∧ ConsCol A fc S ∧ ¬ DistinctParts A S then 1 else 0) ≤
      ∑ v, wv v * (ω S * if ∀ e ∈ S, ∃ m, e ∈ A (v m).1 ∧ fc e = (v m).2 then 1 else 0) := by
    intro S hS
    have hc' := (mem_powersetCard.mp hS).2
    have hnn : ∀ v ∈ (univ : Finset (Fin ℓ → Fin p × Fin q)), 0 ≤ wv v *
        (ω S * if ∀ e ∈ S, ∃ m, e ∈ A (v m).1 ∧ fc e = (v m).2 then (1 : ℝ) else 0) :=
      fun v _ => mul_nonneg (hwv0 v) (mul_nonneg (hω0 S hS) (by split_ifs <;> norm_num))
    by_cases h : InParts A S ∧ ConsCol A fc S ∧ ¬ DistinctParts A S
    · obtain ⟨hin, hcons, hnd⟩ := h
      set eS : Fin ℓ → Finset V := fun m => (S.equivFin.symm (Fin.cast hc'.symm m)).1 with heS
      have heSmem : ∀ m, eS m ∈ S := fun m => (S.equivFin.symm (Fin.cast hc'.symm m)).2
      have hsurj : ∀ e ∈ S, ∃ m, eS m = e := by
        intro e he
        refine ⟨Fin.cast hc' (S.equivFin ⟨e, he⟩), ?_⟩
        have : Fin.cast hc'.symm (Fin.cast hc' (S.equivFin ⟨e, he⟩)) = S.equivFin ⟨e, he⟩ :=
          Fin.ext rfl
        show (S.equivFin.symm (Fin.cast hc'.symm (Fin.cast hc' (S.equivFin ⟨e, he⟩)))).1 = e
        rw [this, Equiv.symm_apply_apply]
      choose π hπ using fun m => hin (eS m) (heSmem m)
      set v : Fin ℓ → Fin p × Fin q := fun m => (π m, fc (eS m)) with hv
      have hind : ∀ e ∈ S, ∃ m, e ∈ A (v m).1 ∧ fc e = (v m).2 := by
        intro e he
        obtain ⟨m, rfl⟩ := hsurj e he
        exact ⟨m, hπ m, rfl⟩
      have himπ : univ.image π = partsMet A S := by
        ext i
        simp only [mem_image, mem_univ, true_and, partsMet, mem_filter]
        constructor
        · rintro ⟨m, rfl⟩
          exact ⟨eS m, heSmem m, hπ m⟩
        · rintro ⟨e, he, hei⟩
          obtain ⟨m, rfl⟩ := hsurj e he
          exact ⟨m, part_unique hne hdisj (hπ m) hei⟩
      have himv : (univ.image v).card = (partsMet A S).card := by
        rw [← himπ]
        have : univ.image π = (univ.image v).image Prod.fst := by
          rw [image_image]; rfl
        rw [this]
        refine (card_image_of_injOn (f := Prod.fst) (s := univ.image v) (fun x hx y hy hxy => ?_)).symm
        obtain ⟨m, -, rfl⟩ := mem_image.mp (mem_coe.mp hx)
        obtain ⟨m', -, rfl⟩ := mem_image.mp (mem_coe.mp hy)
        simp only [hv] at hxy ⊢
        rw [Prod.ext_iff]
        refine ⟨hxy, hcons _ (heSmem m) _ (heSmem m') (π m) (hπ m) ?_⟩
        rw [hxy]; exact hπ m'
      have hlt : (partsMet A S).card < ℓ := by
        by_contra hge
        push_neg at hge
        have hle : (univ.image π).card ≤ ℓ := by
          simpa using (card_image_le (s := (univ : Finset (Fin ℓ))) (f := π))
        have e1 : (univ.image π).card = (partsMet A S).card := by rw [himπ]
        have hcard : (univ.image π).card = (univ : Finset (Fin ℓ)).card := by
          rw [card_univ, Fintype.card_fin]; omega
        have hπinj : Function.Injective π := by
          intro m m' h
          exact (card_image_iff.mp hcard) (mem_coe.mpr (mem_univ m)) (mem_coe.mpr (mem_univ m')) h
        apply hnd
        refine ⟨hin, fun e he e' he' i hi hi' => ?_⟩
        obtain ⟨m, rfl⟩ := hsurj e he
        obtain ⟨m', rfl⟩ := hsurj e' he'
        have h1 := part_unique hne hdisj (hπ m) hi
        have h2 := part_unique hne hdisj (hπ m') hi'
        rw [hπinj (h1.trans h2.symm)]
      refine le_trans ?_ (single_le_sum hnn (mem_univ v))
      simp only [hwv]
      rw [if_pos ⟨hin, hcons, hnd⟩, if_pos hind, himv, if_pos hlt]
      ring_nf
      exact le_rfl
    · rw [if_neg h, mul_zero, mul_zero]
      exact sum_nonneg hnn
  refine (sum_le_sum key).trans ?_
  rw [sum_comm, mul_sum]
  refine sum_le_sum fun v _ => ?_
  rw [← mul_sum, mul_comm B]
  refine mul_le_mul_of_nonneg_left ?_ (hwv0 v)
  exact hZ v

end Pseudorandom
