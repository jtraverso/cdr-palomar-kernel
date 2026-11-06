/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license.
Authors: Juan Pablo Traverso Gianini
-/
module

public import CDRBicolour.Absorption.Count.Wilson.Cross
public import CDRBicolour.Absorption.Count.Wilson.Reserve

/-!
# Optimal counting constant, part 3: the residual host and the local pieces (item 4)

The *offset* of a point is its position inside its class.  Group `i` holds the offsets
`[i t, (i+1) t)` of every class, the reserve `R` the offsets `≥ g t`.

* `adj_iff`: in the residual graph of the cross blocks two points are adjacent unless they lie in
  different groups;
* `exists_W`: every allowed triangle of the residual host lies in some `W_i = G_i ∪ R`;
* `embV i : Fin m ↪ Fin n`: the local copy of `W_i`, `m = 3t + |R|`, with the interval colouring of
  the profile `(t + r_A, t + r_B, t + r_C)` (`col3_embV`); local offsets `< t` go to `G_i`, the
  others to `R`.
-/

@[expose] public section

noncomputable section

namespace CDRBicolour.Absorption.Count.Wilson

open Finset TypedTriangle CDRBicolour.Prefix CDRBicolour.Absorption

variable {a b c g t : ℕ}

/-! ### Offsets -/

/-- Position of a point inside its class. -/
def off (v : Fin (a + b + c)) : ℕ := v.val - cbase a b (col3 a b c v)

theorem cbase_col3_le (v : Fin (a + b + c)) : cbase a b (col3 a b c v) ≤ v.val := by
  unfold cbase col3; split_ifs <;> simp_all <;> omega

theorem val_eq_off (v : Fin (a + b + c)) : v.val = cbase a b (col3 a b c v) + off v := by
  have := cbase_col3_le v; unfold off; omega

theorem off_lt (v : Fin (a + b + c)) : off v < csize a b c (col3 a b c v) := by
  have hv := v.isLt
  unfold off csize cbase col3; split_ifs <;> simp_all <;> omega

theorem eq_of_off {u v : Fin (a + b + c)} (hc : col3 a b c u = col3 a b c v) (ho : off u = off v) :
    u = v := by
  apply Fin.ext; rw [val_eq_off u, val_eq_off v, hc, ho]

theorem off_gv (h : WCond a b c g t) (i : Fin g) (P : Fin 3) (α : Fin t) :
    off (gv h i P α) = i.val * t + α.val := by
  unfold off; rw [col3_gv, gv_val]; omega

/-- The point of class `P` and offset `o`. -/
def ptAt (P : Fin 3) (o : ℕ) (ho : o < csize a b c P) : Fin (a + b + c) :=
  ⟨cbase a b P + o, by have := cbase_add_csize (a := a) (b := b) (c := c) P; omega⟩

theorem col3_ptAt (P : Fin 3) (o : ℕ) (ho : o < csize a b c P) :
    col3 a b c (ptAt P o ho) = P := by
  unfold col3 ptAt
  fin_cases P <;> simp [cbase, csize] at ho ⊢ <;> omega

theorem off_ptAt (P : Fin 3) (o : ℕ) (ho : o < csize a b c P) : off (ptAt P o ho) = o := by
  unfold off; rw [col3_ptAt]; simp [ptAt]

/-- `v` is in group `i`. -/
def InG (t : ℕ) (i : ℕ) (v : Fin (a + b + c)) : Prop := i * t ≤ off v ∧ off v < i * t + t

/-- `v` is in the reserve. -/
def InR (g t : ℕ) (v : Fin (a + b + c)) : Prop := g * t ≤ off v

instance (i : ℕ) (v : Fin (a + b + c)) : Decidable (InG t i v) := by unfold InG; infer_instance
instance (v : Fin (a + b + c)) : Decidable (InR g t v) := by unfold InR; infer_instance

theorem it_add {i t : ℕ} : i * t + t = (i + 1) * t := by ring

theorem InG_gv (h : WCond a b c g t) (i : Fin g) (P : Fin 3) (α : Fin t) :
    InG t i.val (gv h i P α) := by
  unfold InG; rw [off_gv]; have := α.isLt; omega

theorem InG_unique (ht : 0 < t) {i j : ℕ} {v : Fin (a + b + c)} (hi : InG t i v)
    (hj : InG t j v) : i = j := by
  unfold InG at hi hj
  by_contra hne
  rcases Nat.lt_or_gt_of_ne hne with hlt | hlt
  · have : (i + 1) * t ≤ j * t := Nat.mul_le_mul_right t hlt
    rw [← it_add] at this; omega
  · have : (j + 1) * t ≤ i * t := Nat.mul_le_mul_right t hlt
    rw [← it_add] at this; omega

theorem not_InR_of_InG {i : ℕ} (hi : i < g) {v : Fin (a + b + c)} (h : InG t i v) :
    ¬ InR g t v := by
  unfold InG at h; unfold InR
  have : (i + 1) * t ≤ g * t := Nat.mul_le_mul_right t hi
  rw [← it_add] at this; omega

/-- A point outside the reserve is in some group. -/
theorem InG_of_not_InR (ht : 0 < t) {v : Fin (a + b + c)} (h : ¬ InR g t v) :
    ∃ i < g, InG t i v := by
  unfold InR at h
  refine ⟨off v / t, (Nat.div_lt_iff_lt_mul ht).2 (by omega), ?_⟩
  unfold InG
  have h1 := Nat.div_add_mod (off v) t
  have h2 := Nat.mod_lt (off v) ht
  constructor
  · rw [Nat.mul_comm]; omega
  · rw [Nat.mul_comm]; omega

/-- A point of group `i` is a group point. -/
theorem eq_gv_of_InG (h : WCond a b c g t) {i : Fin g} {v : Fin (a + b + c)} (hv : InG t i.val v) :
    ∃ α : Fin t, v = gv h i (col3 a b c v) α := by
  unfold InG at hv
  refine ⟨⟨off v - i.val * t, by omega⟩, eq_of_off (col3_gv h _ _ _).symm ?_⟩
  rw [off_gv]; simp only; omega

/-! ### Adjacency in the residual host -/

section Adj

variable (h : WCond a b c g t) {S : Finset (Finset (Fin g))}

/-- The edges of the cross blocks. -/
abbrev LX (Λ : LFam S t) : Finset (Sym2 (Fin (a + b + c))) := (crossP h Λ).biUnion triEdges

theorem adj_iff (hS : _root_.STS.IsSTS S) (Λ : LFam S t) {u v : Fin (a + b + c)} :
    (rG (LX h Λ)).Adj u v ↔ u ≠ v ∧ ¬ ∃ i j : Fin g, i ≠ j ∧ InG t i.val u ∧ InG t j.val v := by
  rw [rG_adj, mem_crossEdges h hS]
  constructor
  · rintro ⟨hn, huv⟩
    refine ⟨huv, ?_⟩
    rintro ⟨i, j, hij, hu, hv⟩
    obtain ⟨α, hα⟩ := eq_gv_of_InG h hu
    obtain ⟨β, hβ⟩ := eq_gv_of_InG h hv
    exact hn ⟨i, j, _, _, α, β, hij, hα, hβ⟩
  · rintro ⟨huv, hn⟩
    refine ⟨?_, huv⟩
    rintro ⟨p, q, P, Q, α, β, hpq, rfl, rfl⟩
    exact hn ⟨p, q, hpq, InG_gv h p P α, InG_gv h q Q β⟩

/-- The pieces `W_i = G_i ∪ R`. -/
def InW (i : ℕ) (v : Fin (a + b + c)) : Prop := InG t i v ∨ InR g t v

/-- Two points of the same piece are adjacent. -/
theorem adj_of_InW (hS : _root_.STS.IsSTS S) (Λ : LFam S t) {i : Fin g} {u v : Fin (a + b + c)}
    (hu : InW (g := g) (t := t) i.val u) (hv : InW (g := g) (t := t) i.val v) (huv : u ≠ v) :
    (rG (LX h Λ)).Adj u v := by
  rw [adj_iff h hS]
  refine ⟨huv, ?_⟩
  rintro ⟨p, q, hpq, hpu, hqv⟩
  rcases hu with hu | hu
  · rcases hv with hv | hv
    · exact hpq (Fin.ext ((InG_unique h.ht hpu hu).trans (InG_unique h.ht hv hqv)))
    · exact not_InR_of_InG q.isLt hqv hv
  · exact not_InR_of_InG p.isLt hpu hu

/-- The reserve is universal. -/
theorem univ_reserve (hS : _root_.STS.IsSTS S) (Λ : LFam S t) :
    Univ (LX h Λ) (univ.filter fun v : Fin (a + b + c) => InR g t v) := by
  intro w hw p hpw
  rw [mem_filter] at hw
  rw [adj_iff h hS]
  refine ⟨Ne.symm hpw, ?_⟩
  rintro ⟨i, j, -, hi, -⟩
  exact not_InR_of_InG i.isLt hi hw.2

/-- **Every allowed triangle of the residual host lies in one piece.** -/
theorem exists_W (hS : _root_.STS.IsSTS S) (Λ : LFam S t) (hg : 0 < g) {T : Finset (Fin (a + b + c))}
    (hT : IsAllowed (rHost (col3 a b c) (LX h Λ)) cdrF T) :
    ∃ i : Fin g, ∀ v ∈ T, InW (g := g) (t := t) i.val v := by
  by_cases hG : ∃ u ∈ T, ¬ InR g t u
  · obtain ⟨u, huT, huR⟩ := hG
    obtain ⟨i, hi, hu⟩ := InG_of_not_InR h.ht huR
    refine ⟨⟨i, hi⟩, fun v hv => ?_⟩
    by_cases hvR : InR g t v
    · exact Or.inr hvR
    · obtain ⟨j, hj, hvj⟩ := InG_of_not_InR h.ht hvR
      by_cases huv : u = v
      · subst huv; exact Or.inl hu
      · have hadj : (rG (LX h Λ)).Adj u v := hT.2.1 u huT v hv huv
        rw [adj_iff h hS] at hadj
        by_cases hij : i = j
        · subst hij; exact Or.inl hvj
        · exact absurd ⟨⟨i, hi⟩, ⟨j, hj⟩, fun e => hij (congrArg Fin.val e), hu, hvj⟩ hadj.2
  · push Not at hG
    exact ⟨⟨0, hg⟩, fun v hv => Or.inr (hG v hv)⟩

end Adj

/-! ### The local copies -/

/-- Reserve size of class `P`. -/
def rsz (a b c g t : ℕ) (P : Fin 3) : ℕ := csize a b c P - g * t

/-- Local profile. -/
def la (a b c g t : ℕ) : ℕ := t + rsz a b c g t 0
def lb (a b c g t : ℕ) : ℕ := t + rsz a b c g t 1
def lc (a b c g t : ℕ) : ℕ := t + rsz a b c g t 2

theorem csize_loc (P : Fin 3) :
    csize (la a b c g t) (lb a b c g t) (lc a b c g t) P = t + rsz a b c g t P := by
  fin_cases P <;> rfl

theorem gm1 {g t : ℕ} (hg : 1 ≤ g) : (g - 1) * t + t = g * t := by
  rw [← Nat.succ_mul, Nat.succ_eq_add_one, Nat.sub_add_cancel hg]

variable (h : WCond a b c g t)

/-- Global offset of the local offset `o` in piece `i`. -/
def goff (g t i o : ℕ) : ℕ := if o < t then i * t + o else (g - 1) * t + o

include h in
theorem goff_lt (i : Fin g) {P : Fin 3} {o : ℕ} (ho : o < t + rsz a b c g t P) :
    goff g t i o < csize a b c P := by
  have hgP := gt_le_csize h P
  have hi := i.isLt
  have e := gm1 (t := t) (show 1 ≤ g by omega)
  unfold goff rsz at *
  split_ifs with h1
  · have : (i.val + 1) * t ≤ g * t := Nat.mul_le_mul_right t hi
    rw [← it_add] at this; omega
  · omega

/-- The local point `j` of piece `i`. -/
def embF (i : Fin g) (j : Fin (la a b c g t + lb a b c g t + lc a b c g t)) : Fin (a + b + c) :=
  let P := col3 (la a b c g t) (lb a b c g t) (lc a b c g t) j
  ptAt P (goff g t i (off j)) (goff_lt h i (by
    have := off_lt (a := la a b c g t) (b := lb a b c g t) (c := lc a b c g t) j
    rwa [csize_loc] at this))

theorem col3_embF (i : Fin g) (j : Fin (la a b c g t + lb a b c g t + lc a b c g t)) :
    col3 a b c (embF h i j) = col3 (la a b c g t) (lb a b c g t) (lc a b c g t) j := by
  unfold embF; exact col3_ptAt _ _ _

theorem off_embF (i : Fin g) (j : Fin (la a b c g t + lb a b c g t + lc a b c g t)) :
    off (embF h i j) = goff g t i (off j) := by
  unfold embF; exact off_ptAt _ _ _

theorem embF_inj (i : Fin g) : Function.Injective (embF h i) := by
  intro j j' he
  have hc := congrArg (col3 a b c) he
  rw [col3_embF, col3_embF] at hc
  have ho := congrArg off he
  rw [off_embF, off_embF] at ho
  refine eq_of_off hc ?_
  have hi := i.isLt
  have e := gm1 (t := t) (show 1 ≤ g by omega)
  have : (i.val + 1) * t ≤ g * t := Nat.mul_le_mul_right t hi
  rw [← it_add] at this
  unfold goff at ho
  split_ifs at ho <;> omega

/-- **The local copy of `W_i`.** -/
def embV (i : Fin g) : Fin (la a b c g t + lb a b c g t + lc a b c g t) ↪ Fin (a + b + c) :=
  ⟨embF h i, embF_inj h i⟩

theorem embV_apply (i : Fin g) (j) : embV h i j = embF h i j := rfl

/-- Local offsets `< t` go to group `i`, the others to the reserve. -/
theorem InW_embV (i : Fin g) (j : Fin (la a b c g t + lb a b c g t + lc a b c g t)) :
    InW (g := g) (t := t) i.val (embV h i j) := by
  rw [embV_apply]
  unfold InW InG InR
  rw [off_embF]
  have hi := i.isLt
  have e := gm1 (t := t) (show 1 ≤ g by omega)
  unfold goff
  split_ifs <;> omega

theorem InR_embV_iff (i : Fin g) (j : Fin (la a b c g t + lb a b c g t + lc a b c g t)) :
    InR g t (embV h i j) ↔ t ≤ off j := by
  rw [embV_apply]
  unfold InR
  rw [off_embF]
  have hi := i.isLt
  have e := gm1 (t := t) (show 1 ≤ g by omega)
  have : (i.val + 1) * t ≤ g * t := Nat.mul_le_mul_right t hi
  rw [← it_add] at this
  unfold goff
  split_ifs <;> omega

/-- Every point of `W_i` is a local point. -/
theorem exists_embV (i : Fin g) {v : Fin (a + b + c)} (hv : InW (g := g) (t := t) i.val v) :
    ∃ j, embV h i j = v := by
  set P := col3 a b c v
  have hi := i.isLt
  have e := gm1 (t := t) (show 1 ≤ g by omega)
  have hvo : off v < csize a b c P := off_lt v
  have hgP := gt_le_csize h P
  have hsz : csize (la a b c g t) (lb a b c g t) (lc a b c g t) P = t + (csize a b c P - g * t) :=
    csize_loc P
  unfold InW InG at hv
  by_cases hR : InR g t v
  · unfold InR at hR
    have hoP : off v - (g - 1) * t < csize (la a b c g t) (lb a b c g t) (lc a b c g t) P := by
      rw [hsz]; omega
    refine ⟨ptAt P _ hoP, eq_of_off ?_ ?_⟩
    · rw [embV_apply, col3_embF, col3_ptAt]
    · rw [embV_apply, off_embF, off_ptAt]
      unfold goff
      rw [if_neg (by omega)]
      omega
  · unfold InR at hR hv
    have hG : i.val * t ≤ off v ∧ off v < i.val * t + t := by
      rcases hv with hv | hv
      · exact hv
      · exact absurd hv hR
    have hoP : off v - i.val * t < csize (la a b c g t) (lb a b c g t) (lc a b c g t) P := by
      rw [hsz]; omega
    refine ⟨ptAt P _ hoP, eq_of_off ?_ ?_⟩
    · rw [embV_apply, col3_embF, col3_ptAt]
    · rw [embV_apply, off_embF, off_ptAt]
      unfold goff
      rw [if_pos (by omega)]
      omega

end CDRBicolour.Absorption.Count.Wilson
