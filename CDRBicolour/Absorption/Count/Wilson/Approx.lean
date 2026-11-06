/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license.
Authors: Juan Pablo Traverso Gianini
-/
module

public import CDRBicolour.Absorption.Count.Wilson.LocalSeed

/-!
# Optimal counting constant, part 5: the approximate local seed (item 4)

Scalar weights `w_k` for triangles with `k` reserve points, with `x = 2t`, `y = (2/3)|R|`:

    x w₀ + y w₁ = 1,   x w₁ + y w₂ = 1,   x w₂ + y w₃ = 1/g,

all in `[1/(2 g x), 2/x]` when `x/4 ≤ y ≤ x` (`wK_bounds`).  An edge with `ρ` reserve ends has
`2t − O(1)` allowed thirds in the group part and `(2/3)|R| + O(D)` in the reserve, `D` the
spread of the reserve sizes; so the deficit of `μ₀(T) = w_{#reserve(T)}` is `O((1 + D)/x)`
(`mu0_deficit`).
-/

@[expose] public section

noncomputable section

namespace CDRBicolour.Absorption.Count.Wilson

open Finset TypedTriangle CDRBicolour.Prefix CDRBicolour.Absorption

/-! ### Scalar weights -/

section Weights

/-- Weight of a triangle with `2` reserve points. -/
def w2 (g : ℕ) (x : ℝ) : ℝ := 1 / (2 * g * x)
/-- Weight with `1` reserve point. -/
def w1 (g : ℕ) (x y : ℝ) : ℝ := (1 - y * w2 g x) / x
/-- Weight with no reserve point. -/
def w0 (g : ℕ) (x y : ℝ) : ℝ := (1 - y * w1 g x y) / x
/-- Weight with `3` reserve points. -/
def w3 (g : ℕ) (y : ℝ) : ℝ := 1 / (2 * g * y)

/-- Weight by number of reserve points. -/
def wK (g : ℕ) (x y : ℝ) : ℕ → ℝ
  | 0 => w0 g x y
  | 1 => w1 g x y
  | 2 => w2 g x
  | _ => w3 g y

variable {g : ℕ} {x y : ℝ}

theorem wK_eq0 (hx : 0 < x) : x * wK g x y 0 + y * wK g x y 1 = 1 := by
  simp only [wK, w0]; field_simp; ring

theorem wK_eq1 (hx : 0 < x) : x * wK g x y 1 + y * wK g x y 2 = 1 := by
  simp only [wK, w1]; field_simp; ring

theorem wK_eq2 (hg : 1 ≤ g) (hx : 0 < x) (hy : 0 < y) :
    x * wK g x y 2 + y * wK g x y 3 = 1 / g := by
  have hg' : (0 : ℝ) < g := by exact_mod_cast hg
  simp only [wK, w2, w3]; field_simp; ring

theorem wK_bounds (hg : 1 ≤ g) (hx : 0 < x) (hy1 : x / 4 ≤ y) (hy2 : y ≤ x) (k : ℕ) (hk : k ≤ 3) :
    1 / (2 * g * x) ≤ wK g x y k ∧ wK g x y k ≤ 2 / x := by
  have hg' : (1 : ℝ) ≤ g := by exact_mod_cast hg
  have hy : 0 < y := by linarith
  have h2gx : 0 < 2 * g * x := by positivity
  have hyw2 : y * w2 g x = y / x / (2 * g) := by unfold w2; field_simp
  have hs0 : 0 < y / x := div_pos hy hx
  have hs1 : y / x ≤ 1 := (div_le_one hx).2 hy2
  have hyw1 : y * w1 g x y = y / x * (1 - y / x / (2 * g)) := by
    unfold w1; rw [mul_div_assoc', hyw2]; field_simp
  have k1 : y / x / (2 * g) ≤ 1 / 2 := by
    have h2g : (2 : ℝ) ≤ 2 * g := by linarith
    calc y / x / (2 * g) ≤ 1 / (2 * g) := by gcongr
      _ ≤ 1 / 2 := one_div_le_one_div_of_le (by norm_num) h2g
  have k2 : 1 / (2 * g) ≤ 1 - y / x * (1 - y / x / (2 * g)) := by
    have e : 1 - y / x * (1 - y / x / (2 * g)) - 1 / (2 * g) =
        (1 - y / x) * (1 - (1 + y / x) / (2 * g)) := by field_simp; ring
    have f1 : 0 ≤ 1 - y / x := by linarith
    have f2 : 0 ≤ 1 - (1 + y / x) / (2 * g) := by
      rw [sub_nonneg, div_le_one (by positivity)]; linarith
    nlinarith [mul_nonneg f1 f2]
  have hgx : 1 / (2 * g * x) ≤ 1 / x :=
    one_div_le_one_div_of_le hx (le_mul_of_one_le_left hx.le (by linarith))
  have hsplit : 1 / (2 * g * x) = 1 / (2 * g) / x := by field_simp
  interval_cases k
  · simp only [wK, w0]
    rw [hyw1]
    constructor
    · rw [hsplit]; exact div_le_div_of_nonneg_right k2 hx.le
    · have : 1 - y / x * (1 - y / x / (2 * g)) ≤ 2 := by nlinarith
      exact div_le_div_of_nonneg_right this hx.le
  · simp only [wK, w1]
    rw [hyw2]
    constructor
    · rw [hsplit]
      refine div_le_div_of_nonneg_right ?_ hx.le
      have : 1 / (2 * (g : ℝ)) ≤ 1 / 2 := by
        rw [div_le_div_iff₀ (by positivity) (by norm_num)]; linarith
      linarith
    · refine div_le_div_of_nonneg_right ?_ hx.le
      have : 0 ≤ y / x / (2 * g) := by positivity
      linarith
  · simp only [wK, w2]
    exact ⟨le_rfl, hgx.trans (div_le_div_of_nonneg_right (by norm_num : (1 : ℝ) ≤ 2) hx.le)⟩
  · simp only [wK, w3]
    constructor
    · rw [div_le_div_iff₀ h2gx (by positivity)]; nlinarith
    · rw [div_le_div_iff₀ (by positivity) hx]; nlinarith

end Weights

/-! ### The approximate seed and its deficit -/

section Approx

variable {la lb lc t g : ℕ}

/-- Reserve size of class `k` (real). -/
def rr (la lb lc t : ℕ) (k : Fin 3) : ℝ := (csize la lb lc k : ℝ) - t

/-- `x = 2t`. -/
def xx (t : ℕ) : ℝ := 2 * t
/-- `y = (2/3) |R|`. -/
def yy (la lb lc t : ℕ) : ℝ := 2 / 3 * (rr la lb lc t 0 + rr la lb lc t 1 + rr la lb lc t 2)

/-- The approximate seed. -/
def mu0 (la lb lc t g : ℕ) (T : Finset (Fin (la + lb + lc))) : ℝ :=
  wK g (xx t) (yy la lb lc t) #(T.filter fun v => IsRes t v)

theorem card_filter_triple {V : Type*} [DecidableEq V] (p : V → Prop) [DecidablePred p]
    {u v w : V} (huv : u ≠ v) (huw : u ≠ w) (hvw : v ≠ w) :
    #(({u, v, w} : Finset V).filter p) =
      (if p u then 1 else 0) + (if p v then 1 else 0) + (if p w then 1 else 0) := by
  rw [filter_insert, filter_insert, filter_singleton]
  by_cases hu : p u <;> by_cases hv : p v <;> by_cases hw : p w <;>
    simp [hu, hv, hw, huv, huw, hvw, card_insert_of_notMem]

open Classical in
theorem two_colours (c1 c2 : Fin 3) :
    #(univ.filter fun k : Fin 3 => ({c1, c2, k} : Multiset (Fin 3)) ∈ cdrF) = 2 := by
  have key : ∀ c1 c2 : Fin 3, #(univ.filter fun k : Fin 3 =>
      Multiset.card ({c1, c2, k} : Multiset (Fin 3)) = 3 ∧
        (({c1, c2, k} : Multiset (Fin 3)).toFinset).card = 2) = 2 := by decide
  convert key c1 c2 using 2
  ext k; simp [cdrF]

theorem pair_set (Z : Finset (Fin 3)) (hZ : #Z = 2) : ∃ k, Z = univ.erase k := by
  revert Z; decide

/-- Points of class in `Z` and of a given kind (group or reserve). -/
theorem card_kind (ht : t ≤ min la (min lb lc)) (Z : Finset (Fin 3)) (β : Bool) :
    #(univ.filter fun w : Fin (la + lb + lc) => col3 la lb lc w ∈ Z ∧ decide (IsRes t w) = β) =
      ∑ k ∈ Z, (if β then csize la lb lc k - t else t) := by
  rw [card_eq_sum_card_fiberwise (f := col3 la lb lc) (t := Z)
    (by intro w hw; exact (mem_filter.1 hw).2.1)]
  refine sum_congr rfl fun k hk => ?_
  rw [← nI_lab2 ht k β]
  unfold nI lab2
  congr 1; ext w
  simp only [mem_filter, mem_univ, true_and, Prod.mk.injEq]
  constructor
  · rintro ⟨⟨-, h2⟩, h3⟩; exact ⟨h3, h2⟩
  · rintro ⟨h1, h2⟩; exact ⟨⟨h1 ▸ hk, h2⟩, h1⟩

theorem card_sdiff_two {V : Type*} [DecidableEq V] (s : Finset V) (u v : V) :
    (#s : ℝ) - 2 ≤ #(s \ {u, v}) ∧ (#(s \ {u, v}) : ℝ) ≤ #s := by
  have h1 := le_card_sdiff ({u, v} : Finset V) s
  have h2 := card_le_card (sdiff_subset (s := s) (t := {u, v}))
  have h3 : #({u, v} : Finset V) ≤ 2 := card_le_two
  constructor
  · have : #s ≤ #(s \ {u, v}) + 2 := by omega
    have := Nat.cast_le (α := ℝ) |>.2 this; push_cast at this; linarith
  · exact_mod_cast h2

open Classical in
/-- **Deficit of the approximate seed.** -/
theorem mu0_deficit (hg : 1 ≤ g) (ht0 : 0 < t) (ht : t ≤ min la (min lb lc))
    (hy1 : xx t / 4 ≤ yy la lb lc t) (hy2 : yy la lb lc t ≤ xx t) {D : ℝ}
    (hD : ∀ k l, |rr la lb lc t k - rr la lb lc t l| ≤ D) (e : E0 (Fin (la + lb + lc))) :
    |Minc (col3 la lb lc) (mu0 la lb lc t g) e - tau' g t e.1| ≤ 2 / xx t * (4 + D) := by
  obtain ⟨f, hf⟩ := e
  induction f using Sym2.ind with
  | _ u v =>
  have huv : u ≠ v := fun e => hf (by rw [e]; exact Sym2.mk_isDiag_iff.2 rfl)
  set x := xx t with hxdef
  set y := yy la lb lc t with hydef
  have hx : 0 < x := by simp only [x, xx]; positivity
  have hyp : 0 < y := by linarith
  set ρ : ℕ := (if IsRes t u then 1 else 0) + (if IsRes t v then 1 else 0) with hρ
  have hρ2 : ρ ≤ 2 := by simp only [hρ]; split_ifs <;> omega
  set th := univ.filter fun w : Fin (la + lb + lc) => w ≠ u ∧ w ≠ v ∧
    ({col3 la lb lc u, col3 la lb lc v, col3 la lb lc w} : Multiset (Fin 3)) ∈ cdrF with hth
  have hsum : Minc (col3 la lb lc) (mu0 la lb lc t g) ⟨s(u, v), hf⟩ =
      ∑ w ∈ th, wK g x y (ρ + if IsRes t w then 1 else 0) := by
    simp only [Minc, LinearMap.coe_mk, AddHom.coe_mk]
    rw [Refined.sum_tri_edge huv]
    refine sum_congr rfl fun w hw => ?_
    obtain ⟨hwu, hwv, -⟩ := (mem_filter.1 hw).2
    simp only [mu0]
    rw [card_filter_triple _ huv (Ne.symm hwu) (Ne.symm hwv)]
  rw [hsum, ← sum_filter_add_sum_filter_not th fun w => IsRes t w]
  have s1 : ∑ w ∈ th.filter (fun w => IsRes t w), wK g x y (ρ + if IsRes t w then 1 else 0) =
      ∑ w ∈ th.filter (fun w => IsRes t w), wK g x y (ρ + 1) :=
    sum_congr rfl fun w hw => by rw [if_pos (mem_filter.1 hw).2]
  have s2 : ∑ w ∈ th.filter (fun w => ¬ IsRes t w), wK g x y (ρ + if IsRes t w then 1 else 0) =
      ∑ w ∈ th.filter (fun w => ¬ IsRes t w), wK g x y ρ :=
    sum_congr rfl fun w hw => by rw [if_neg (mem_filter.1 hw).2, Nat.add_zero]
  rw [s1, s2, sum_const, sum_const, nsmul_eq_mul, nsmul_eq_mul]
  -- the two counts
  set Z := univ.filter fun k : Fin 3 =>
    ({col3 la lb lc u, col3 la lb lc v, k} : Multiset (Fin 3)) ∈ cdrF with hZ
  have hZ2 : #Z = 2 := two_colours _ _
  set SG := univ.filter fun w : Fin (la + lb + lc) =>
    col3 la lb lc w ∈ Z ∧ decide (IsRes t w) = false with hSG
  set SR := univ.filter fun w : Fin (la + lb + lc) =>
    col3 la lb lc w ∈ Z ∧ decide (IsRes t w) = true with hSR
  have cG : (#SG : ℝ) = x := by
    rw [hSG, card_kind ht Z false]; simp [hZ2, x, xx]
  have cR : (#SR : ℝ) = ∑ k ∈ Z, rr la lb lc t k := by
    rw [hSR, card_kind ht Z true]
    push_cast
    refine sum_congr rfl fun k _ => ?_
    simp only [ite_true, rr]
    have : t ≤ csize la lb lc k := by unfold csize; split_ifs <;> omega
    push_cast [Nat.cast_sub this]; ring
  have eA : th.filter (fun w => ¬ IsRes t w) = SG \ {u, v} := by
    ext w; simp only [hth, hSG, hZ, mem_filter, mem_univ, true_and, mem_sdiff, mem_insert,
      mem_singleton, decide_eq_false_iff_not, not_or]; tauto
  have eB : th.filter (fun w => IsRes t w) = SR \ {u, v} := by
    ext w; simp only [hth, hSR, hZ, mem_filter, mem_univ, true_and, mem_sdiff, mem_insert,
      mem_singleton, decide_eq_true_eq, not_or]; tauto
  have bA : |(#(th.filter fun w => ¬ IsRes t w) : ℝ) - x| ≤ 2 := by
    rw [eA]
    obtain ⟨r1, r2⟩ := card_sdiff_two SG u v
    rw [cG] at r1 r2
    rw [abs_le]; constructor <;> linarith
  have hZsum : |∑ k ∈ Z, rr la lb lc t k - y| ≤ D := by
    obtain ⟨k, hk⟩ := pair_set Z hZ2
    rw [hk, sum_erase_eq_sub (mem_univ k), Fin.sum_univ_three]
    simp only [y, yy]
    have h0 := hD 0 k; have h1 := hD 1 k; have h2 := hD 2 k
    rw [abs_le] at h0 h1 h2 ⊢
    constructor <;> linarith [h0.1, h0.2, h1.1, h1.2, h2.1, h2.2]
  have bB : |(#(th.filter fun w => IsRes t w) : ℝ) - y| ≤ 2 + D := by
    rw [eB]
    obtain ⟨r1, r2⟩ := card_sdiff_two SR u v
    rw [cR] at r1 r2
    rw [abs_le] at hZsum ⊢
    constructor <;> linarith [hZsum.1, hZsum.2]
  -- the target
  have htarget : x * wK g x y ρ + y * wK g x y (ρ + 1) = tau' g t s(u, v) := by
    rw [tau'_mk]
    by_cases hu : IsRes t u <;> by_cases hv : IsRes t v
    · rw [if_pos ⟨hu, hv⟩, show ρ = 2 by simp [hρ, hu, hv]]; exact wK_eq2 hg hx hyp
    · rw [if_neg (fun h => hv h.2), show ρ = 1 by simp [hρ, hu, hv]]; exact wK_eq1 hx
    · rw [if_neg (fun h => hu h.1), show ρ = 1 by simp [hρ, hu, hv]]; exact wK_eq1 hx
    · rw [if_neg (fun h => hu h.1), show ρ = 0 by simp [hρ, hu, hv]]; exact wK_eq0 hx
  obtain ⟨l0, u0⟩ := wK_bounds hg hx hy1 hy2 ρ (by omega)
  obtain ⟨l1, u1⟩ := wK_bounds hg hx hy1 hy2 (ρ + 1) (by omega)
  have p0 : 0 ≤ wK g x y ρ := le_trans (by positivity) l0
  have p1 : 0 ≤ wK g x y (ρ + 1) := le_trans (by positivity) l1
  show |_ - tau' g t s(u, v)| ≤ _
  rw [← htarget]
  set nA : ℝ := (#(th.filter fun w => ¬ IsRes t w) : ℝ)
  set nB : ℝ := (#(th.filter fun w => IsRes t w) : ℝ)
  have e1 : nB * wK g x y (ρ + 1) + nA * wK g x y ρ - (x * wK g x y ρ + y * wK g x y (ρ + 1)) =
      (nA - x) * wK g x y ρ + (nB - y) * wK g x y (ρ + 1) := by ring
  rw [e1]
  have hD0 : 0 ≤ D := le_trans (abs_nonneg _) (hD 0 0)
  calc _ ≤ |(nA - x) * wK g x y ρ| + |(nB - y) * wK g x y (ρ + 1)| := abs_add_le _ _
    _ = |nA - x| * wK g x y ρ + |nB - y| * wK g x y (ρ + 1) := by
        rw [abs_mul, abs_mul, abs_of_nonneg p0, abs_of_nonneg p1]
    _ ≤ 2 * (2 / x) + (2 + D) * (2 / x) := by
        gcongr
    _ = 2 / x * (4 + D) := by ring

end Approx

end CDRBicolour.Absorption.Count.Wilson
