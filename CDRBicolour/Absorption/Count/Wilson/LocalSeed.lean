/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license.
Authors: Juan Pablo Traverso Gianini
-/
module

public import CDRBicolour.Absorption.Count.Wilson.Local
public import CDRBicolour.Absorption.BRIFinal
public import CDRBicolour.Absorption.Refined.Seed

/-!
# Optimal counting constant, part 4: the local seed (item 4)

On the local copy `Fin m` of a piece `W_i = G_i ∪ R` (interval colouring of the profile
`(t + r₀, t + r₁, t + r₂)`, points of offset `≥ t` in the reserve) the edge target is

    τ(e) = 1/g  if both ends are in the reserve,   τ(e) = 1  otherwise.

* `ell_tau`: `ℓ(τ) = 0` when the reserve sizes satisfy the global admissibility identity
  `Σ_{k<l} (r_k − r_l)²/2 = 3 g t + Σ r_k` (the classes of the whole profile are `g t + r_k`);
* `local_seed`: an exact seed for `τ` with weights in `[1/(C m), C/m]`: scalar weights by the
  number of reserve points of the triangle, corrected by the bounded inverse `bri_of_balanced`.
-/

@[expose] public section

noncomputable section

namespace CDRBicolour.Absorption.Count.Wilson

open Finset TypedTriangle CDRBicolour.Prefix CDRBicolour.Absorption

/-! ### Pair sums -/

section Pairs

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Ordered pairs count every unordered pair twice. -/
theorem sum_offDiag_E0 (G : Sym2 V → ℝ) :
    ∑ p ∈ (univ : Finset V).offDiag, G s(p.1, p.2) = 2 * ∑ e : E0 V, G e.1 := by
  have h1 : ∑ e : E0 V, G e.1 = ∑ f ∈ univ.filter (fun f : Sym2 V => ¬ f.IsDiag), G f := by
    rw [← Finset.sum_subtype (univ.filter fun f : Sym2 V => ¬ f.IsDiag) (by simp) G]
  rw [h1]
  rw [← sum_fiberwise_of_maps_to (s := (univ : Finset V).offDiag)
    (t := univ.filter fun f : Sym2 V => ¬ f.IsDiag) (g := fun p => s(p.1, p.2))
    (by intro p hp; simp only [mem_offDiag] at hp; simp [hp.2.2])]
  rw [mul_sum]
  refine sum_congr rfl fun f hf => ?_
  have hfd : ¬ f.IsDiag := (mem_filter.1 hf).2
  rw [sum_congr rfl fun p hp => by rw [(mem_filter.1 hp).2]]
  rw [sum_const, nsmul_eq_mul]
  congr 1
  induction f using Sym2.ind with
  | _ x y =>
  have hxy : x ≠ y := fun e => hfd (by rw [e]; exact Sym2.mk_isDiag_iff.2 rfl)
  have : (univ : Finset V).offDiag.filter (fun p => s(p.1, p.2) = s(x, y)) = {(x, y), (y, x)} := by
    ext ⟨u, v⟩
    simp only [mem_filter, mem_offDiag, mem_univ, true_and, Sym2.eq_iff, mem_insert,
      mem_singleton, Prod.mk.injEq]
    constructor
    · rintro ⟨-, h⟩; exact h
    · rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
      · exact ⟨hxy, Or.inl ⟨rfl, rfl⟩⟩
      · exact ⟨Ne.symm hxy, Or.inr ⟨rfl, rfl⟩⟩
  rw [this, card_pair (by simp [hxy])]
  norm_num

variable {I : Type*} [Fintype I] [DecidableEq I] (lab : V → I)

/-- Size of a label class. -/
def nI (X : I) : ℕ := #(univ.filter fun v => lab v = X)

theorem card_offDiag_lab (X Y : I) :
    #((univ : Finset V).offDiag.filter fun p => lab p.1 = X ∧ lab p.2 = Y) =
      nI lab X * nI lab Y - (if X = Y then nI lab X else 0) := by
  by_cases hXY : X = Y
  · subst hXY
    rw [if_pos rfl, nI, ← offDiag_card]
    congr 1
    ext p
    simp only [mem_filter, mem_offDiag, mem_univ, true_and]
    tauto
  · rw [if_neg hXY, Nat.sub_zero, nI, nI, ← card_product]
    congr 1
    ext p
    simp only [mem_filter, mem_offDiag, mem_univ, true_and, mem_product]
    constructor
    · rintro ⟨-, h1, h2⟩; exact ⟨h1, h2⟩
    · rintro ⟨h1, h2⟩; exact ⟨fun e => hXY (by rw [← h1, ← h2, e]), h1, h2⟩

/-- A sum over ordered pairs of a function of the labels. -/
theorem sum_offDiag_lab (F : I → I → ℝ) :
    ∑ p ∈ (univ : Finset V).offDiag, F (lab p.1) (lab p.2) =
      ∑ X : I, ∑ Y : I, F X Y *
        ((nI lab X : ℝ) * nI lab Y - (if X = Y then (nI lab X : ℝ) else 0)) := by
  rw [← sum_fiberwise_of_maps_to (s := (univ : Finset V).offDiag) (t := univ)
    (g := fun p => (lab p.1, lab p.2)) (fun _ _ => mem_univ _)]
  rw [← univ_product_univ, sum_product]
  refine sum_congr rfl fun X _ => sum_congr rfl fun Y _ => ?_
  rw [sum_congr rfl fun p hp => by
    obtain ⟨h1, h2⟩ := Prod.mk.inj (mem_filter.1 hp).2
    rw [h1, h2]]
  rw [sum_const, nsmul_eq_mul, mul_comm]
  congr 1
  have : (univ : Finset V).offDiag.filter (fun p => (lab p.1, lab p.2) = (X, Y)) =
      (univ : Finset V).offDiag.filter fun p => lab p.1 = X ∧ lab p.2 = Y := by
    ext p; simp [Prod.mk.injEq]
  rw [this, card_offDiag_lab]
  have hle : (if X = Y then nI lab X else 0) ≤ nI lab X * nI lab Y := by
    split_ifs with h
    · subst h
      rcases Nat.eq_zero_or_pos (nI lab X) with h0 | h0
      · rw [h0]
      · exact Nat.le_mul_of_pos_right _ h0
    · exact Nat.zero_le _
  rw [Nat.cast_sub hle]
  push_cast
  split_ifs <;> simp

end Pairs

/-! ### Counting points by offset -/

section Offsets

variable {a b c : ℕ}

theorem card_off_range (P : Fin 3) {lo hi : ℕ} (hlo : lo ≤ hi) (hhi : hi ≤ csize a b c P) :
    #(univ.filter fun v : Fin (a + b + c) => col3 a b c v = P ∧ lo ≤ off v ∧ off v < hi) =
      hi - lo := by
  rw [← card_range (hi - lo)]
  symm
  refine card_bij (fun o ho => ptAt P (lo + o) (by have := mem_range.1 ho; omega)) ?_ ?_ ?_
  · intro o ho
    have := mem_range.1 ho
    simp only [mem_filter, mem_univ, true_and]
    rw [col3_ptAt, off_ptAt]
    omega
  · intro o ho o' ho' he
    have := congrArg off he
    rw [off_ptAt, off_ptAt] at this
    omega
  · intro v hv
    simp only [mem_filter, mem_univ, true_and] at hv
    refine ⟨off v - lo, mem_range.2 (by omega), eq_of_off ?_ ?_⟩
    · rw [col3_ptAt, hv.1]
    · rw [off_ptAt]; omega

end Offsets

/-! ### The local host and `ℓ(τ) = 0` -/

section LocalHost

variable {la lb lc t : ℕ}

/-- Local reserve points: offset `≥ t`. -/
def IsRes (t : ℕ) (v : Fin (la + lb + lc)) : Prop := t ≤ off v

instance (v : Fin (la + lb + lc)) : Decidable (IsRes t v) := by unfold IsRes; infer_instance

/-- The edge target. -/
def tau' (g t : ℕ) (e : Sym2 (Fin (la + lb + lc))) : ℝ :=
  Sym2.lift ⟨fun u v => if IsRes t u ∧ IsRes t v then 1 / (g : ℝ) else 1,
    fun u v => by simp only [and_comm]⟩ e

theorem tau'_mk (g : ℕ) (u v : Fin (la + lb + lc)) :
    tau' g t s(u, v) = if IsRes t u ∧ IsRes t v then 1 / (g : ℝ) else 1 := rfl

/-- The label (class, reserve) of a local point. -/
def lab2 (t : ℕ) (v : Fin (la + lb + lc)) : Fin 3 × Bool :=
  (col3 la lb lc v, decide (IsRes t v))

theorem nI_lab2 (ht : t ≤ min la (min lb lc)) (P : Fin 3) (β : Bool) :
    nI (lab2 (la := la) (lb := lb) (lc := lc) t) (P, β) =
      if β then csize la lb lc P - t else t := by
  have hP : t ≤ csize la lb lc P := by
    unfold csize; split_ifs <;> omega
  have hsz : ∀ v : Fin (la + lb + lc), col3 la lb lc v = P → off v < csize la lb lc P :=
    fun v hv => hv ▸ off_lt v
  cases β
  · simp only [Bool.false_eq_true, ite_false]
    have hc := card_off_range (a := la) (b := lb) (c := lc) P (Nat.zero_le t) hP
    rw [Nat.sub_zero] at hc
    refine Eq.trans ?_ hc
    unfold nI lab2 IsRes
    congr 1; ext v
    simp only [mem_filter, mem_univ, true_and, Prod.mk.injEq, decide_eq_false_iff_not, not_le,
      zero_le]
  · simp only [ite_true]
    rw [← card_off_range (a := la) (b := lb) (c := lc) P (le_refl t |>.trans hP) le_rfl]
    unfold nI lab2 IsRes
    congr 1; ext v
    simp only [mem_filter, mem_univ, true_and, Prod.mk.injEq, decide_eq_true_eq]
    constructor
    · rintro ⟨h1, h2⟩; exact ⟨h1, h2, h1 ▸ off_lt v⟩
    · rintro ⟨h1, h2, -⟩; exact ⟨h1, h2⟩

/-- **`ℓ(τ) = 0`** under the admissibility identity of the reserve sizes. -/
theorem ell_tau {g : ℕ} (hg : 0 < g) (ht : t ≤ min la (min lb lc))
    (hid : ((la : ℝ) - t) ^ 2 + ((lb : ℝ) - t) ^ 2 + ((lc : ℝ) - t) ^ 2 -
      ((la : ℝ) - t) * ((lb : ℝ) - t) - ((la : ℝ) - t) * ((lc : ℝ) - t) -
      ((lb : ℝ) - t) * ((lc : ℝ) - t) =
      3 * g * t + ((la : ℝ) - t) + ((lb : ℝ) - t) + ((lc : ℝ) - t)) :
    ell (col3 la lb lc) (fun e => tau' g t e.1) = 0 := by
  set F : Fin 3 × Bool → Fin 3 × Bool → ℝ := fun X Y =>
    (if X.1 = Y.1 then (-2 : ℝ) else 1) * (if X.2 = true ∧ Y.2 = true then 1 / (g : ℝ) else 1)
    with hF
  have hpt : ∀ u v : Fin (la + lb + lc),
      wl (col3 la lb lc) s(u, v) * tau' g t s(u, v) = F (lab2 t u) (lab2 t v) := by
    intro u v
    simp only [wl, Sym2.lift_mk, tau'_mk, hF, lab2, decide_eq_true_eq]
  have h2 : 2 * ell (col3 la lb lc) (fun e => tau' g t e.1) =
      ∑ p ∈ (univ : Finset (Fin (la + lb + lc))).offDiag, F (lab2 t p.1) (lab2 t p.2) := by
    rw [sum_congr rfl fun p _ => (hpt p.1 p.2).symm]
    rw [sum_offDiag_E0 (fun e => wl (col3 la lb lc) e * tau' g t e)]
    rfl
  rw [sum_offDiag_lab (lab2 t) F] at h2
  simp only [hF] at h2
  simp only [Fintype.sum_prod_type, Fin.sum_univ_three, Fintype.sum_bool, nI_lab2 ht] at h2
  have hla : t ≤ la := by omega
  have hlb : t ≤ lb := by omega
  have hlc : t ≤ lc := by omega
  simp only [csize, Fin.isValue, ite_true, Bool.false_eq_true, ite_false, and_true, and_false, Prod.mk.injEq, and_self, Fin.reduceEq, Bool.true_eq_false] at h2
  push_cast [Nat.cast_sub hla, Nat.cast_sub hlb, Nat.cast_sub hlc] at h2
  have hg' : (g : ℝ) ≠ 0 := by exact_mod_cast hg.ne'
  have h3 : 2 * ell (col3 la lb lc) (fun e => tau' g t e.1) * g = 0 := by
    rw [h2]
    field_simp
    first
      | linear_combination (-2 : ℝ) * hid
      | linear_combination (2 : ℝ) * hid
  rcases mul_eq_zero.1 h3 with h | h
  · linarith
  · exact absurd h hg'

end LocalHost

end CDRBicolour.Absorption.Count.Wilson
