/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import RequestProject.PaschEGJ13.Freedman
public import RequestProject.Pseudorandom.Cylinder
set_option maxHeartbeats 4000000 -- build option (original: -DmaxHeartbeats=1600000; raised)
set_option maxRecDepth 16384 -- build option (original: -DmaxRecDepth=8192; raised)

/-! # Weighted counts of `ℓ`-sets with a prescribed colour pattern

The vertex set is `Fin n` with its natural order. Every vertex receives a colour in `Fin q`
uniformly at random (`unif (Fin n) q`). An `ℓ`-set `e = {v₁ < ⋯ < v_ℓ}` has pattern
`α : ℕ → Fin q` if `c(vᵢ) = α (i - 1)` for all `i`, i.e. `c v = α (rk e v)` where `rk e v` is
the number of elements of `e` below `v`.

`cnt ℓ w α c = ∑_{|e| = ℓ} w e · [e has pattern α]` is the random variable `ω(E_α)` of
Theorem 3.1. `Xp ℓ w α t` is its exposure martingale, where the colours of `0, …, t - 1`
have been revealed.
-/

@[expose] public section

namespace Pseudorandom

namespace Patt

open Finset

variable {n q : ℕ}

/-- The rank of `v` in `e`: the number of elements of `e` below `v`. -/
def rk (e : Finset (Fin n)) (v : Fin n) : ℕ := (e.filter (· < v)).card

/-- `e` has colour pattern `α` under the colouring `c`. -/
def Pat (α : ℕ → Fin q) (c : Fin n → Fin q) (e : Finset (Fin n)) : Prop :=
  ∀ v ∈ e, c v = α (rk e v)

open Classical in
/-- The weighted number of `ℓ`-sets with pattern `α`. -/
noncomputable def cnt (ℓ : ℕ) (w : Finset (Fin n) → ℝ) (α : ℕ → Fin q) (c : Fin n → Fin q) :
    ℝ :=
  ∑ e ∈ powersetCard ℓ univ, w e * if Pat α c e then 1 else 0

open Classical in
/-- The exposure martingale of `cnt`: colours of the vertices `< t` are revealed. -/
noncomputable def Xp (ℓ : ℕ) (w : Finset (Fin n) → ℝ) (α : ℕ → Fin q) (t : ℕ)
    (c : Fin n → Fin q) : ℝ :=
  ∑ e ∈ powersetCard ℓ univ, w e * ((1 / (q : ℝ)) ^ (e.filter (fun v : Fin n => t ≤ (v : ℕ))).card *
    if ∀ v ∈ e, (v : ℕ) < t → c v = α (rk e v) then 1 else 0)

theorem Xp_adapted (ℓ : ℕ) (w : Finset (Fin n) → ℝ) (α : ℕ → Fin q) (t : ℕ) :
    Adapted t (Xp ℓ w α t) := by
  intro c c' h
  unfold Xp
  refine sum_congr rfl fun e _ => ?_
  congr 3
  apply propext
  constructor
  · intro H v hv hvt; rw [← h v hvt]; exact H v hv hvt
  · intro H v hv hvt; rw [h v hvt]; exact H v hv hvt

theorem Xp_zero (ℓ : ℕ) (w : Finset (Fin n) → ℝ) (α : ℕ → Fin q) (c : Fin n → Fin q) :
    Xp ℓ w α 0 c = ∑ e ∈ powersetCard ℓ univ, w e * (1 / (q : ℝ)) ^ ℓ := by
  unfold Xp
  refine sum_congr rfl fun e he => ?_
  rw [mem_powersetCard] at he
  have : e.filter (fun v : Fin n => 0 ≤ (v : ℕ)) = e := filter_true_of_mem fun v _ => Nat.zero_le _
  rw [this, he.2]
  simp

theorem Xp_n (ℓ : ℕ) (w : Finset (Fin n) → ℝ) (α : ℕ → Fin q) (c : Fin n → Fin q) :
    Xp ℓ w α n c = cnt ℓ w α c := by
  unfold Xp cnt
  refine sum_congr rfl fun e _ => ?_
  have : e.filter (fun v : Fin n => n ≤ (v : ℕ)) = ∅ :=
    filter_false_of_mem fun v _ => by have := v.2; omega
  rw [this, card_empty, pow_zero, one_mul]
  congr 2
  apply propext
  constructor
  · intro H v hv; exact H v hv v.2
  · intro H v hv _; exact H v hv

theorem Xp_mart (hq : 0 < q) (ℓ : ℕ) (w : Finset (Fin n) → ℝ) (α : ℕ → Fin q) :
    IsExposureMartingale (unif (Fin n) q) (Xp ℓ w α) := by
  classical
  refine ⟨Xp_adapted ℓ w α, fun i c => ?_⟩
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  unfold Xp
  simp only [unif]
  simp_rw [mul_sum]
  rw [sum_comm]
  refine sum_congr rfl fun e _ => ?_
  by_cases hie : i ∈ e
  · -- the revealed vertex belongs to `e`
    have hfil : e.filter (fun v : Fin n => (i : ℕ) ≤ (v : ℕ)) =
        insert i (e.filter (fun v : Fin n => (i : ℕ) + 1 ≤ (v : ℕ))) := by
      ext v
      simp only [mem_filter, mem_insert]
      constructor
      · rintro ⟨hv, hiv⟩
        by_cases h : v = i
        · left; exact h
        · right; exact ⟨hv, by have : (v : ℕ) ≠ i := fun h' => h (Fin.ext h'); omega⟩
      · rintro (h | ⟨hv, hiv⟩)
        · subst h; exact ⟨hie, le_rfl⟩
        · exact ⟨hv, by omega⟩
    have hcard : (e.filter (fun v : Fin n => (i : ℕ) ≤ (v : ℕ))).card =
        (e.filter (fun v : Fin n => (i : ℕ) + 1 ≤ (v : ℕ))).card + 1 := by
      rw [hfil, card_insert_of_notMem (by simp)]
    have hcond : ∀ a, (∀ v ∈ e, (v : ℕ) < (i : ℕ) + 1 → Function.update c i a v = α (rk e v)) ↔
        ((∀ v ∈ e, (v : ℕ) < i → c v = α (rk e v)) ∧ a = α (rk e i)) := by
      intro a
      constructor
      · intro H
        refine ⟨fun v hv hvi => ?_, ?_⟩
        · have := H v hv (by omega)
          rwa [Function.update_of_ne (fun h => by subst h; omega)] at this
        · have := H i hie (by omega)
          rwa [Function.update_self] at this
      · rintro ⟨H, ha⟩ v hv hvi
        by_cases h : v = i
        · subst h; rw [Function.update_self]; exact ha
        · rw [Function.update_of_ne h]
          exact H v hv (by have : (v : ℕ) ≠ i := fun h' => h (Fin.ext h'); omega)
    simp_rw [hcond]
    rw [hcard]
    by_cases hc : ∀ v ∈ e, (v : ℕ) < i → c v = α (rk e v)
    · have h1 : ∀ a : Fin q, ((∀ v ∈ e, (v : ℕ) < i → c v = α (rk e v)) ∧ a = α (rk e i)) ↔
          a = α (rk e i) := fun a => ⟨fun h => h.2, fun h => ⟨hc, h⟩⟩
      simp_rw [h1, if_pos hc]
      rw [Fintype.sum_eq_single (α (rk e i))]
      · simp only [if_true]; rw [pow_succ]; ring
      · intro a ha; simp [ha]
    · have h1 : ∀ a : Fin q, ¬((∀ v ∈ e, (v : ℕ) < i → c v = α (rk e v)) ∧ a = α (rk e i)) :=
        fun a h => hc h.1
      simp only [h1, if_neg hc, if_false, mul_zero, sum_const_zero]
  · -- the revealed vertex is not in `e`
    have hfil : e.filter (fun v : Fin n => (i : ℕ) + 1 ≤ (v : ℕ)) =
        e.filter (fun v : Fin n => (i : ℕ) ≤ (v : ℕ)) := by
      refine filter_congr fun v hv => ?_
      have : (v : ℕ) ≠ i := fun h' => hie (by rw [show i = v from Fin.ext h'.symm]; exact hv)
      omega
    have hcond : ∀ a, (∀ v ∈ e, (v : ℕ) < (i : ℕ) + 1 → Function.update c i a v = α (rk e v)) ↔
        (∀ v ∈ e, (v : ℕ) < i → c v = α (rk e v)) := by
      intro a
      constructor
      · intro H v hv hvi
        have := H v hv (by omega)
        rwa [Function.update_of_ne (fun h => hie (by rw [← h]; exact hv))] at this
      · intro H v hv hvi
        have hne : v ≠ i := fun h => hie (by rw [← h]; exact hv)
        rw [Function.update_of_ne hne]
        exact H v hv (by have : (v : ℕ) ≠ i := fun h' => hne (Fin.ext h'); omega)
    simp_rw [hcond, hfil]
    rw [← sum_mul, sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul]
    field_simp

theorem pE_cnt (hq : 0 < q) (ℓ : ℕ) (w : Finset (Fin n) → ℝ) (α : ℕ → Fin q) :
    pE (unif (Fin n) q) (cnt ℓ w α) = ∑ e ∈ powersetCard ℓ univ, w e * (1 / (q : ℝ)) ^ ℓ := by
  have h := (Xp_mart hq ℓ w α).pE_eq (unif_isPMF q hq) (fun _ => ⟨0, hq⟩) n le_rfl
  rw [Xp_zero] at h
  rw [← h]
  congr 1
  funext c
  exact (Xp_n ℓ w α c).symm

end Patt

end Pseudorandom
