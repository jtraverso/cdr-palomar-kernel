/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import RequestProject.S07V35.Ball

/-!
# Gauge lemma for signed link matrices with a supplied radius bound (V35, layer 1)

Setting. `R`, `E` finite; `B : R → E → ℤ` with entries in `{-1,0,1}` and at most two nonzero
entries per column (`LinkMatrix B`). `supp B e` is the support of column `e`. A row is
`Anchored` if some column has support exactly `{i}`. `linkGraph B` is the simple graph on `R`
with `i ~ j` iff `i ≠ j` and some column is nonzero at both. `dat B t e = ∑ᵢ B i e * t i`
is the data `Bᵀ t`.

* `propagate`: along BFS balls, `t x = s * c + q` with `s = ±1`, `|q| ≤ L0 + k L`, and `q` in any
  additive subgroup `A` containing all data (used with `A = ⊤` and with quarter-integers).
* `gauge_core`: if every vertex of an anchored component lies in the radius-`K` ball of the
  anchors and every anchor-free component has `K`-bounded balls around each of its vertices,
  then some `t'` has the same data and `|t' i| ≤ (2K+1) L`, with `2 t' i ∈ A`.
* `gauge_of_dist`: the same with the radius hypotheses stated through Mathlib's
  `SimpleGraph.dist`.

Construction of `t'`, component by component (no tree, no matrix inverse):
anchored components keep `t`; in an anchor-free component with root `r` (a chosen
representative), each vertex has `t x = s_x t r + q_x`, `|q_x| ≤ K L`. If the signs `s` are
consistent on every edge of the component, `s` is a kernel vector and `t' = t - s · t r = q`;
otherwise an inconsistent edge yields `|2 t r| ≤ (2K+1) L` and `t` is kept.
-/

@[expose] public section

namespace S07V35

open Finset

variable {R E : Type*} [Fintype R] [DecidableEq R] [Fintype E]

/-- Support of column `e`. -/
def supp (B : R → E → ℤ) (e : E) : Finset R := univ.filter (fun i => B i e ≠ 0)

/-- Signed link matrix: entries in `{-1,0,1}`, at most two nonzero entries per column. -/
structure LinkMatrix (B : R → E → ℤ) : Prop where
  entries : ∀ i e, B i e = -1 ∨ B i e = 0 ∨ B i e = 1
  two : ∀ e, (supp B e).card ≤ 2

/-- Row `i` is anchored if some column has exactly one nonzero entry, at `i`. -/
def Anchored (B : R → E → ℤ) (i : R) : Prop := ∃ e, supp B e = {i}

/-- The link graph: `i ~ j` iff `i ≠ j` and some column is nonzero in both rows. -/
def linkGraph (B : R → E → ℤ) : SimpleGraph R where
  Adj i j := i ≠ j ∧ ∃ e, B i e ≠ 0 ∧ B j e ≠ 0
  symm := ⟨fun _ _ ⟨h, e, h1, h2⟩ => ⟨h.symm, e, h2, h1⟩⟩
  loopless := ⟨fun _ h => h.1 rfl⟩

noncomputable instance (B : R → E → ℤ) : DecidableRel (linkGraph B).Adj := Classical.decRel _

/-- Data `Bᵀ t`. -/
def dat (B : R → E → ℤ) (t : R → ℝ) (e : E) : ℝ := ∑ i, (B i e : ℝ) * t i

/-- The anchored rows, as a finset. -/
noncomputable def anchors (B : R → E → ℤ) : Finset R := by
  classical exact univ.filter (Anchored B)

/-- `x` lies in a component containing an anchor. -/
def AnchComp (B : R → E → ℤ) (x : R) : Prop := ∃ a, Anchored B a ∧ (linkGraph B).Reachable a x

/-- `s = ±1`. -/
def PM (s : ℝ) : Prop := s = 1 ∨ s = -1

theorem PM.mul_self {s : ℝ} (h : PM s) : s * s = 1 := by rcases h with rfl | rfl <;> norm_num

theorem PM.mul {a b : ℝ} (ha : PM a) (hb : PM b) : PM (a * b) := by
  rcases ha with rfl | rfl <;> rcases hb with rfl | rfl <;> norm_num [PM]

theorem PM.neg {a : ℝ} (ha : PM a) : PM (-a) := by
  rcases ha with rfl | rfl <;> norm_num [PM]

theorem PM.abs_mul {s : ℝ} (h : PM s) (x : ℝ) : |s * x| = |x| := by
  rcases h with rfl | rfl <;> simp

theorem PM.mul_mem {s : ℝ} (h : PM s) {A : AddSubgroup ℝ} {q : ℝ} (hq : q ∈ A) : s * q ∈ A := by
  rcases h with rfl | rfl
  · simpa using hq
  · simpa using A.neg_mem hq

theorem PM.eq_of_add_ne_zero {a b : ℝ} (ha : PM a) (hb : PM b) (h : a + b ≠ 0) : b = a := by
  rcases ha with rfl | rfl <;> rcases hb with rfl | rfl <;> first | rfl | (exfalso; norm_num at h)

variable {B : R → E → ℤ}

omit [DecidableEq R] [Fintype E] in
theorem pm_entry (hB : LinkMatrix B) {i : R} {e : E} (h : B i e ≠ 0) : PM (B i e : ℝ) := by
  rcases hB.entries i e with h1 | h1 | h1
  · right; simp [h1]
  · exact absurd h1 h
  · left; simp [h1]

omit [DecidableEq R] [Fintype E] in
theorem dat_eq_sum_supp (t : R → ℝ) (e : E) : dat B t e = ∑ i ∈ supp B e, (B i e : ℝ) * t i := by
  unfold dat supp
  rw [Finset.sum_filter_of_ne]
  intro x _ hx h0
  apply hx; simp [h0]

omit [Fintype E] in
theorem supp_pair (hB : LinkMatrix B) {i j : R} {e : E} (hij : i ≠ j) (hi : B i e ≠ 0)
    (hj : B j e ≠ 0) : supp B e = {i, j} := by
  symm
  apply Finset.eq_of_subset_of_card_le
  · intro x hx
    simp only [mem_insert, mem_singleton] at hx
    rcases hx with rfl | rfl <;> simp [supp, *]
  · rw [Finset.card_pair hij]; exact hB.two e

omit [Fintype E] in
theorem dat_pair (hB : LinkMatrix B) {i j : R} {e : E} (hij : i ≠ j) (hi : B i e ≠ 0)
    (hj : B j e ≠ 0) (t : R → ℝ) : dat B t e = B i e * t i + B j e * t j := by
  rw [dat_eq_sum_supp, supp_pair hB hij hi hj, Finset.sum_pair hij]

omit [DecidableEq R] [Fintype E] in
theorem dat_single {i : R} {e : E} (h : supp B e = {i}) (t : R → ℝ) :
    dat B t e = B i e * t i := by
  rw [dat_eq_sum_supp, h, Finset.sum_singleton]

omit [Fintype E] in
/-- **Propagation along BFS balls.** -/
theorem propagate (hB : LinkMatrix B) {t : R → ℝ} {L : ℝ} (hL : 0 ≤ L)
    (hd : ∀ e, |dat B t e| ≤ L) {A : AddSubgroup ℝ} (hA : ∀ e, dat B t e ∈ A)
    {S : Finset R} {c L0 : ℝ}
    (hS : ∀ x ∈ S, ∃ s q, PM s ∧ t x = s * c + q ∧ |q| ≤ L0 ∧ q ∈ A) :
    ∀ k : ℕ, ∀ x ∈ ball (linkGraph B) S k,
      ∃ s q, PM s ∧ t x = s * c + q ∧ |q| ≤ L0 + k * L ∧ q ∈ A := by
  intro k
  induction k with
  | zero =>
    intro x hx
    obtain ⟨s, q, hs, hx, hq, hqA⟩ := hS x hx
    exact ⟨s, q, hs, hx, by simpa using hq, hqA⟩
  | succ k ih =>
    intro y hy
    rcases (mem_ball_succ _).1 hy with hy | ⟨x, hx, hxy⟩
    · obtain ⟨s, q, hs, hty, hq, hqA⟩ := ih y hy
      exact ⟨s, q, hs, hty, by push_cast; nlinarith, hqA⟩
    · obtain ⟨s, q, hs, htx, hq, hqA⟩ := ih x hx
      obtain ⟨hne, e, hxe, hye⟩ := hxy
      have hdat := dat_pair hB hne hxe hye t
      have pa := pm_entry hB hxe
      have pb := pm_entry hB hye
      refine ⟨-((B y e : ℝ) * B x e * s), (B y e : ℝ) * dat B t e - (B y e : ℝ) * B x e * q,
        ((pb.mul pa).mul hs).neg, ?_, ?_, ?_⟩
      · have hb2 := pb.mul_self
        have : t y = (B y e : ℝ) * dat B t e - (B y e) * (B x e) * t x := by
          rw [hdat]; linear_combination (-t y) * hb2
        rw [this, htx]; ring
      · calc |(B y e : ℝ) * dat B t e - (B y e : ℝ) * B x e * q|
            ≤ |(B y e : ℝ) * dat B t e| + |(B y e : ℝ) * B x e * q| := abs_sub _ _
          _ = |dat B t e| + |q| := by rw [pb.abs_mul, (pb.mul pa).abs_mul]
          _ ≤ L + (L0 + k * L) := add_le_add (hd e) hq
          _ = L0 + ((k + 1 : ℕ) : ℝ) * L := by push_cast; ring
      · exact sub_mem (pb.mul_mem (hA e)) ((pb.mul pa).mul_mem hqA)

/-- A chosen root of the connected component of `x`. -/
noncomputable def root (G : SimpleGraph R) (x : R) : R := (G.connectedComponentMk x).out

omit [Fintype R] [DecidableEq R] in
theorem root_reach (G : SimpleGraph R) (x : R) : G.Reachable (root G x) x :=
  SimpleGraph.ConnectedComponent.exact (Quot.out_eq _)

omit [Fintype R] [DecidableEq R] in
theorem root_eq (G : SimpleGraph R) {x y : R} (h : G.Reachable x y) : root G x = root G y := by
  unfold root; rw [SimpleGraph.ConnectedComponent.sound h]

omit [DecidableEq R] [Fintype E] in
theorem anchComp_of_reach {x y : R} (hx : AnchComp B x) (h : (linkGraph B).Reachable x y) :
    AnchComp B y := by
  obtain ⟨a, ha, hax⟩ := hx; exact ⟨a, ha, hax.trans h⟩

/-- **Gauge lemma, layer 1 (supplied radius bound, ball form).** -/
theorem gauge_core (hB : LinkMatrix B) (t : R → ℝ) (L : ℝ) (hL : 0 ≤ L)
    (hd : ∀ e, |dat B t e| ≤ L) (A : AddSubgroup ℝ) (hA : ∀ e, dat B t e ∈ A) (K : ℕ)
    (hanch : ∀ x, AnchComp B x → x ∈ ball (linkGraph B) (anchors B) K)
    (hfree : ∀ x y, ¬ AnchComp B x → (linkGraph B).Reachable x y →
      y ∈ ball (linkGraph B) {x} K) :
    ∃ t' : R → ℝ, (∀ e, dat B t' e = dat B t e) ∧ (∀ i, |t' i| ≤ (2 * K + 1) * L) ∧
      ∀ i, 2 * t' i ∈ A := by
  classical
  set G := linkGraph B with hG
  have hKL : 0 ≤ (K : ℝ) * L := mul_nonneg (Nat.cast_nonneg _) hL
  -- anchored components
  have hanchData : ∀ x, AnchComp B x → |t x| ≤ L + K * L ∧ t x ∈ A := by
    intro x hx
    obtain ⟨s, q, -, h1, h2, h3⟩ := propagate hB hL hd hA (S := anchors B) (c := 0) (L0 := L)
      (by
        intro y hy
        have hy' : Anchored B y := by simpa [anchors] using hy
        obtain ⟨e, he⟩ := hy'
        have hyy : y ∈ supp B e := by rw [he]; exact mem_singleton_self y
        have pb := pm_entry hB (mem_filter.1 hyy).2
        have hdt := dat_single he t
        refine ⟨1, t y, Or.inl rfl, by ring, ?_, ?_⟩
        · have : t y = (B y e : ℝ) * dat B t e := by
            rw [hdt, ← mul_assoc, pb.mul_self, one_mul]
          rw [this, pb.abs_mul]; exact hd e
        · have : t y = (B y e : ℝ) * dat B t e := by
            rw [hdt, ← mul_assoc, pb.mul_self, one_mul]
          rw [this]; exact pb.mul_mem (hA e))
      K x (hanch x hx)
    rw [h1]; simp only [mul_zero, zero_add]; exact ⟨h2, h3⟩
  -- anchor-free components: sign and offset relative to the root
  have hdata : ∀ x, ∃ s q : ℝ, ¬ AnchComp B x →
      (PM s ∧ t x = s * t (root G x) + q ∧ |q| ≤ K * L ∧ q ∈ A) := by
    intro x
    by_cases hx : AnchComp B x
    · exact ⟨1, 0, fun h => absurd hx h⟩
    · have hr : ¬ AnchComp B (root G x) := fun h => hx (anchComp_of_reach h (root_reach G x))
      obtain ⟨s, q, hs, h1, h2, h3⟩ := propagate hB hL hd hA (S := {root G x})
        (c := t (root G x)) (L0 := 0)
        (by
          intro y hy
          rw [mem_singleton] at hy
          subst hy
          exact ⟨1, 0, Or.inl rfl, by ring, by simp, A.zero_mem⟩)
        K x (hfree _ _ hr (root_reach G x))
      exact ⟨s, q, fun _ => ⟨hs, h1, by simpa using h2, h3⟩⟩
  choose sg q hsq using hdata
  let Cons : R → Prop := fun r => ∀ (e : E) (i j : R), i ≠ j → B i e ≠ 0 → B j e ≠ 0 →
    root G i = r → ¬ AnchComp B i → (B i e : ℝ) * sg i + B j e * sg j = 0
  let t' : R → ℝ := fun x =>
    if AnchComp B x then t x else if Cons (root G x) then t x - sg x * t (root G x) else t x
  refine ⟨t', ?_, ?_⟩
  · -- every column, including anchors and zero columns
    intro e
    by_cases hpair : ∃ i j, i ≠ j ∧ B i e ≠ 0 ∧ B j e ≠ 0
    · obtain ⟨i, j, hij, hi, hj⟩ := hpair
      have hadj : G.Adj i j := ⟨hij, e, hi, hj⟩
      have hreach : G.Reachable i j := hadj.reachable
      have hroot : root G j = root G i := (root_eq G hreach).symm
      rw [dat_pair hB hij hi hj, dat_pair hB hij hi hj]
      by_cases ha : AnchComp B i
      · have hb : AnchComp B j := anchComp_of_reach ha hreach
        simp only [t', if_pos ha, if_pos hb]
      · have hb : ¬ AnchComp B j := fun h => ha (anchComp_of_reach h hreach.symm)
        by_cases hc : Cons (root G i)
        · have hc' : Cons (root G j) := by rw [hroot]; exact hc
          have hk := hc e i j hij hi hj rfl ha
          simp only [t', if_neg ha, if_neg hb, if_pos hc, hroot]
          linear_combination (-(t (root G i))) * hk
        · have hc' : ¬ Cons (root G j) := by rw [hroot]; exact hc
          simp only [t', if_neg ha, if_neg hb, if_neg hc, if_neg hc']
    · push_neg at hpair
      rw [dat_eq_sum_supp, dat_eq_sum_supp]
      refine Finset.sum_congr rfl (fun i hi => ?_)
      have hi0 : B i e ≠ 0 := (mem_filter.1 hi).2
      have hsingle : supp B e = {i} := by
        rw [eq_singleton_iff_unique_mem]
        refine ⟨hi, fun j hj => ?_⟩
        by_contra hji
        exact (mem_filter.1 hj).2 (hpair i j (Ne.symm hji) hi0)
      have ha : AnchComp B i := ⟨i, ⟨e, hsingle⟩, SimpleGraph.Reachable.refl i⟩
      simp only [t', if_pos ha]
  · suffices key : ∀ i, |t' i| ≤ (2 * K + 1) * L ∧ 2 * t' i ∈ A from
      ⟨fun i => (key i).1, fun i => (key i).2⟩
    intro i
    by_cases ha : AnchComp B i
    · obtain ⟨h1, h2⟩ := hanchData i ha
      simp only [t', if_pos ha]
      refine ⟨by nlinarith, ?_⟩
      rw [two_mul]; exact add_mem h2 h2
    · obtain ⟨hs, h1, h2, h3⟩ := hsq i ha
      by_cases hc : Cons (root G i)
      · simp only [t', if_neg ha, if_pos hc]
        have : t i - sg i * t (root G i) = q i := by rw [h1]; ring
        rw [this]
        refine ⟨by nlinarith, ?_⟩
        rw [two_mul]; exact add_mem h3 h3
      · simp only [t', if_neg ha, if_neg hc]
        -- an inconsistent edge in the component bounds the root value
        simp only [Cons, not_forall] at hc
        obtain ⟨e, a, b, hab, hae, hbe, hra, hna, hne⟩ := hc
        have hreach : G.Reachable a b := (show G.Adj a b from ⟨hab, e, hae, hbe⟩).reachable
        have hnb : ¬ AnchComp B b := fun h => hna (anchComp_of_reach h hreach.symm)
        have hrb : root G b = root G i := by rw [← root_eq G hreach, hra]
        obtain ⟨hsa, ha1, ha2, ha3⟩ := hsq a hna
        obtain ⟨hsb, hb1, hb2, hb3⟩ := hsq b hnb
        rw [hra] at ha1
        rw [hrb] at hb1
        have pa := pm_entry hB hae
        have pb := pm_entry hB hbe
        have hpa2 := pa.mul_self
        have hne' : sg a + (B a e : ℝ) * B b e * sg b ≠ 0 := by
          intro h0; apply hne
          linear_combination (B a e : ℝ) * h0 - (B b e : ℝ) * sg b * hpa2
        have hsign := hsa.eq_of_add_ne_zero ((pa.mul pb).mul hsb) hne'
        have hdat := dat_pair hB hab hae hbe t
        set r := root G i
        set w : ℝ := (B a e : ℝ) * dat B t e - q a - (B a e : ℝ) * B b e * q b
        have h2r : 2 * t r = sg a * w := by
          have hsa2 := hsa.mul_self
          have : (B a e : ℝ) * dat B t e = 2 * sg a * t r + q a + (B a e : ℝ) * B b e * q b := by
            rw [hdat, ha1, hb1]
            have : (B a e : ℝ) * B b e * sg b = sg a := hsign
            linear_combination (t r) * this + (sg a * t r + q a) * hpa2
          simp only [w]
          rw [this]
          linear_combination (-(2 * t r)) * hsa2
        have hwA : w ∈ A :=
          sub_mem (sub_mem (pa.mul_mem (hA e)) ha3) ((pa.mul pb).mul_mem hb3)
        have hwL : |w| ≤ L + K * L + K * L := by
          calc |w| ≤ |(B a e : ℝ) * dat B t e - q a| + |(B a e : ℝ) * B b e * q b| := abs_sub _ _
            _ ≤ |(B a e : ℝ) * dat B t e| + |q a| + |(B a e : ℝ) * B b e * q b| := by
                gcongr; exact abs_sub _ _
            _ = |dat B t e| + |q a| + |q b| := by rw [pa.abs_mul, (pa.mul pb).abs_mul]
            _ ≤ L + K * L + K * L := by gcongr; exact hd e
        have h2rabs : |2 * t r| ≤ L + K * L + K * L := by rw [h2r, hsa.abs_mul]; exact hwL
        have h2rA : 2 * t r ∈ A := by rw [h2r]; exact hsa.mul_mem hwA
        constructor
        · have hti : |t i| ≤ |t r| + K * L := by
            rw [h1]
            calc |sg i * t r + q i| ≤ |sg i * t r| + |q i| := abs_add_le _ _
              _ ≤ |t r| + K * L := by rw [hs.abs_mul]; gcongr
          rw [abs_mul, abs_two] at h2rabs
          nlinarith
        · have : 2 * t i = sg i * (2 * t r) + (q i + q i) := by rw [h1]; ring
          rw [this]; exact add_mem (hs.mul_mem h2rA) (add_mem h3 h3)

/-- **Gauge lemma, layer 1 (supplied distance / diameter bound, `SimpleGraph.dist` form).**
Every vertex of a component containing an anchor is within distance `K` of some anchor, and
any two vertices of an anchor-free component are within distance `K`. -/
theorem gauge_of_dist (hB : LinkMatrix B) (t : R → ℝ) (L : ℝ) (hL : 0 ≤ L)
    (hd : ∀ e, |dat B t e| ≤ L) (A : AddSubgroup ℝ) (hA : ∀ e, dat B t e ∈ A) (K : ℕ)
    (hanch : ∀ x, AnchComp B x → ∃ a, Anchored B a ∧ (linkGraph B).Reachable a x ∧
      (linkGraph B).dist a x ≤ K)
    (hfree : ∀ x y, ¬ AnchComp B x → (linkGraph B).Reachable x y → (linkGraph B).dist x y ≤ K) :
    ∃ t' : R → ℝ, (∀ e, dat B t' e = dat B t e) ∧ (∀ i, |t' i| ≤ (2 * K + 1) * L) ∧
      ∀ i, 2 * t' i ∈ A := by
  classical
  refine gauge_core hB t L hL hd A hA K (fun x hx => ?_) (fun x y hx hxy => ?_)
  · obtain ⟨a, ha, hr, hdist⟩ := hanch x hx
    obtain ⟨p, hp⟩ := hr.exists_walk_length_eq_dist
    have ha' : a ∈ ball (linkGraph B) (anchors B) 0 := by simpa [ball_zero, anchors] using ha
    have := mem_ball_of_walk (linkGraph B) p ha'
    exact ball_mono _ _ (by omega) this
  · obtain ⟨p, hp⟩ := hxy.exists_walk_length_eq_dist
    have hx0 : x ∈ ball (linkGraph B) {x} 0 := by simp [ball_zero]
    have := mem_ball_of_walk (linkGraph B) p hx0
    rw [zero_add] at this
    have hK := hfree x y hx hxy
    exact ball_mono _ _ (by omega) this

end S07V35
