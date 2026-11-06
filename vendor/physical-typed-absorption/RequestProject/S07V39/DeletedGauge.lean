/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module
public import RequestProject.S07V39.LiftPotential
set_option maxHeartbeats 4000000 -- build option (original: -DmaxHeartbeats=1600000; raised)
set_option maxRecDepth 16384 -- build option (original: -DmaxRecDepth=8192; raised)
@[expose] public section

/-!
# V39 — the native gauge and matching potential on the deleted host `G − Z`

The deleted host `J = G − Z` does NOT satisfy H3 (pairs inside `Z` have no common neighbours),
so V36 `native_gauge_alpha` / V38 `matching_potential_bounded` cannot be applied to `J`
verbatim. Their only use of H3 is the link-degree bound `link_degree_ge`. Here:

* `LinkDeg G lab F β` — every active vertex of every link has link degree `≥ β n`. This is NOT
  a new host assumption: it is a consequence (`linkDeg_of_H3`) of the original H3, and
  `linkDeg_delG` proves it for `G − Z` with `β = α/2` from H3 of `G` and `|Z| ≤ delOf α h · n`.
* `side_card_ge_ld`, `comp_card_ge_ld`, `card_rows_at_le_ld`, `card_nrow_le_ld`, `native_hdeg_ld`
  — V36 statements with `LinkDeg` in place of H3 (same proofs);
* `native_gauge_ld` — V35 gauge on `natB` with the `β`-only constant `3/(2β²) + 1`;
* `matching_potential_ld` — V38 bounded matching potential under `LinkDeg`;
* `matching_potential_delG` — the instance on `G − Z`: constant `(6/α² + 1) · 2A`.
-/

open Finset Classical

noncomputable section

namespace S07V39

open TypedTriangle.SparseEdge TypedTriangle.ComponentRows TypedTriangle.ActiveCover
  TypedTriangle.ComponentCount
open S07V25 S07V36 S07V37

variable {V I : Type*} [Fintype V] {lab : V → I} {F : Set (Multiset I)}

/-- Link-degree bound: active link vertices have link degree `≥ β n`. A consequence of H3. -/
def LinkDeg (G : SimpleGraph V) (lab : V → I) (F : Set (Multiset I)) (β : ℝ) : Prop :=
  ∀ v w, LinkActive G lab F v w → β * Fintype.card V ≤ (link G lab F v).degree w

variable {G : SimpleGraph V}

/-- H3 gives `LinkDeg` with the same `α` (V25 `link_degree_ge`). -/
theorem linkDeg_of_H3 {α : ℝ} (hH3 : CommonNbrCond G lab F α) : LinkDeg G lab F α :=
  fun v w hw => link_degree_ge hH3 v w hw

/-- **The deleted host inherits `LinkDeg` with `α/2`** (from H3 of `G` and a small `Z`). -/
theorem linkDeg_delG {α : ℝ} {h : ℕ} (hα : 0 < α) (hH3 : CommonNbrCond G lab F α) {Z : Finset V}
    (hZ : (Z.card : ℝ) ≤ delOf α h * Fintype.card V) : LinkDeg (delG G Z) lab F (α / 2) := by
  intro v w hw
  obtain ⟨hv, hwZ, hact⟩ := (linkActive_delG_iff hα hH3 hZ).1 hw
  have h1 := link_degree_ge hH3 v w hact
  have hsub : (link G lab F v).neighborFinset w \ Z ⊆ (link (delG G Z) lab F v).neighborFinset w := by
    intro y hy
    rw [Finset.mem_sdiff, SimpleGraph.mem_neighborFinset] at hy
    rw [SimpleGraph.mem_neighborFinset]
    exact link_delG_adj.2 ⟨hv, hy.1, hwZ, hy.2⟩
  have h2 := card_le_card hsub
  have h3 := Finset.card_le_card_sdiff_add_card (s := (link G lab F v).neighborFinset w) (t := Z)
  rw [SimpleGraph.card_neighborFinset_eq_degree] at h2 h3
  have h4 : ((link G lab F v).degree w : ℝ) ≤ (link (delG G Z) lab F v).degree w + Z.card := by
    exact_mod_cast h3.trans (by omega)
  have h5 := two_card_le hα h hZ
  linarith

/-! ### V36 counting under `LinkDeg` -/

theorem side_card_ge_ld {β : ℝ} (hLD : LinkDeg G lab F β) {j : Row V}
    (hj : IsNRow G lab F j) (c : Bool) : β * Fintype.card V ≤ (side G lab F j c).card := by
  obtain ⟨x, hxK, hxc⟩ : ∃ x ∈ j.2, TypedTriangle.ComponentRows.col G lab F j x ≠ c := by
    obtain ⟨a, ⟨w, haw⟩, ha⟩ := hj.1
    have haK : a ∈ j.2 := ha ▸ S07V38.mem_comp_self' _ a
    have hwK : w ∈ j.2 := by
      rw [← ha, S07V25.mem_comp_iff]; exact haw.reachable
    have hne := col_proper hj.2 haK hwK haw
    by_cases h : TypedTriangle.ComponentRows.col G lab F j a = c
    · exact ⟨w, hwK, fun h' => hne (h.trans h'.symm)⟩
    · exact ⟨a, haK, h⟩
  have hdeg := hLD j.1 x (linkActive_of_mem hj.1 hxK)
  have hsub : (link G lab F j.1).neighborFinset x ⊆ side G lab F j c := by
    intro y hy
    rw [SimpleGraph.mem_neighborFinset] at hy
    have hyK : y ∈ j.2 := by
      rw [active_eq_comp hj.1 hxK, S07V25.mem_comp_iff]; exact hy.reachable
    have hcol := col_proper hj.2 hxK hyK hy
    simp only [side, mem_filter]
    refine ⟨hyK, ?_⟩
    cases h1 : TypedTriangle.ComponentRows.col G lab F j y <;>
      cases h2 : TypedTriangle.ComponentRows.col G lab F j x <;> cases c <;> simp_all
  have := card_le_card hsub
  rw [SimpleGraph.card_neighborFinset_eq_degree] at this
  exact hdeg.trans (by exact_mod_cast this)

theorem comp_card_ge_ld {β : ℝ} (hLD : LinkDeg G lab F β) {j : Row V}
    (hj : IsNRow G lab F j) : 2 * β * Fintype.card V ≤ j.2.card := by
  have h1 := side_card_ge_ld hLD hj true
  have h2 := side_card_ge_ld hLD hj false
  have h3 : ((side G lab F j true).card : ℝ) + (side G lab F j false).card = j.2.card := by
    exact_mod_cast side_card_add j
  linarith

theorem card_rows_at_le_ld {β : ℝ} (hβ : 0 < β) (hLD : LinkDeg G lab F β) (v : V) :
    (univ.filter (fun j : NRow G lab F => j.1.1 = v)).card ≤ ⌊1 / (2 * β)⌋₊ := by
  set S := univ.filter (fun j : NRow G lab F => j.1.1 = v)
  have hn : (0 : ℝ) < Fintype.card V := by exact_mod_cast Fintype.card_pos_iff.2 ⟨v⟩
  have hsum : ∑ j ∈ S, j.1.2.card ≤ Fintype.card V := by
    have hmap : ∑ j ∈ S, j.1.2.card = ∑ r ∈ S.map (Function.Embedding.subtype _), r.2.card := by
      rw [Finset.sum_map]; rfl
    rw [hmap]
    refine le_trans (Finset.sum_le_sum_of_subset ?_) (sum_card_activeRowsAt_le G lab F v)
    intro r hr
    obtain ⟨j, hj, rfl⟩ := Finset.mem_map.1 hr
    rw [mem_activeRowsAt]
    exact ⟨(mem_filter.1 hj).2, j.2.1⟩
  have hlow : (S.card : ℝ) * (2 * β * Fintype.card V) ≤ Fintype.card V := by
    have h1 : (S.card : ℝ) * (2 * β * Fintype.card V) ≤ ∑ j ∈ S, (j.1.2.card : ℝ) := by
      have := Finset.card_nsmul_le_sum S (fun j => (j.1.2.card : ℝ)) (2 * β * Fintype.card V)
        (fun j _ => comp_card_ge_ld hLD j.2)
      simpa [nsmul_eq_mul] using this
    have h2 : ∑ j ∈ S, (j.1.2.card : ℝ) ≤ Fintype.card V := by exact_mod_cast hsum
    linarith
  apply Nat.le_floor
  rw [le_div_iff₀ (by positivity)]
  have : (S.card : ℝ) * (2 * β) * Fintype.card V ≤ 1 * Fintype.card V := by linarith
  exact le_of_mul_le_mul_right this hn

theorem card_nrow_le_ld {β : ℝ} (hβ : 0 < β) (hLD : LinkDeg G lab F β) :
    Fintype.card (NRow G lab F) ≤ nativeN V β := by
  unfold nativeN
  rw [← Finset.card_univ, Finset.card_eq_sum_card_fiberwise (f := fun j : NRow G lab F => j.1.1)
    (t := univ) (fun _ _ => mem_univ _)]
  calc ∑ v, (univ.filter (fun j : NRow G lab F => j.1.1 = v)).card
      ≤ ∑ _v : V, ⌊1 / (2 * β)⌋₊ := Finset.sum_le_sum fun v _ => card_rows_at_le_ld hβ hLD v
    _ = Fintype.card V * ⌊1 / (2 * β)⌋₊ := by simp

theorem native_hdeg_ld {β : ℝ} (hβ : 0 < β) (hLD : LinkDeg G lab F β)
    (i : NRow G lab F) (hi : ¬ S07V35.Anchored (natB G lab F) i) :
    nativeM V β ≤ (S07V35.nbrs (S07V35.linkGraph (natB G lab F)) i).card := by
  have hn : (0 : ℝ) < Fintype.card V := by exact_mod_cast Fintype.card_pos_iff.2 ⟨i.1.1⟩
  have hpos : 0 < ⌈2 * β * Fintype.card V⌉₊ := Nat.ceil_pos.2 (by positivity)
  have hK : ⌈2 * β * Fintype.card V⌉₊ ≤ i.1.2.card := Nat.ceil_le.2 (comp_card_ge_ld hLD i.2)
  have hle := card_comp_le_nbrs i hi
  unfold nativeM
  rw [max_eq_right hpos]
  exact hK.trans hle

/-- **Native gauge under `LinkDeg`** with the `β`-only constant `3/(2β²) + 1`. -/
theorem native_gauge_ld {β : ℝ} (hβ : 0 < β) (hLD : LinkDeg G lab F β)
    (t : NRow G lab F → ℝ) (L : ℝ) (hL : 0 ≤ L)
    (hd : ∀ e, |S07V35.dat (natB G lab F) t e| ≤ L) :
    ∃ t' : NRow G lab F → ℝ, (∀ e, S07V35.dat (natB G lab F) t' e =
        S07V35.dat (natB G lab F) t e) ∧
      ∀ i, |t' i| ≤ (3 / (2 * β ^ 2) + 1) * L := by
  obtain ⟨t', h1, h2⟩ := S07V35.gauge_bound natB_linkMatrix (one_le_nativeM β)
    (card_nrow_le_ld hβ hLD) (native_hdeg_ld hβ hLD) t L hL hd
  refine ⟨t', h1, fun i => (h2 i).trans (mul_le_mul_of_nonneg_right ?_ hL)⟩
  exact native_const_le hβ (Fintype.card_pos_iff.2 ⟨i.1.1⟩)

/-- **Bounded matching potential under `LinkDeg`** (V38 `matching_potential_bounded` with
`LinkDeg` in place of H3). -/
theorem matching_potential_ld {β : ℝ} (hβ : 0 < β) (hLD : LinkDeg G lab F β)
    (lam0 lamH : NCol G lab F → ℝ) {A : ℝ} (hA : 0 ≤ A) (h0 : ∀ e, |lam0 e| ≤ A)
    (hH : ∀ e, |lamH e| ≤ A)
    (hagree : ∀ x : Sym2 V → ℤ, IsLocalProfile G lab F x →
      ∑ e : NCol G lab F, lamH e * (x e.1 : ℝ) = ∑ e : NCol G lab F, lam0 e * (x e.1 : ℝ)) :
    ∃ t : NRow G lab F → ℝ, (∀ e, S07V35.dat (natB G lab F) t e = lamH e - lam0 e) ∧
      ∀ i, |t i| ≤ (3 / (2 * β ^ 2) + 1) * (2 * A) := by
  obtain ⟨t0, ht0⟩ := S07V38.rowSpan_of_annihilates (fun e => lamH e - lam0 e) (fun x hx => by
    simp only [sub_mul, Finset.sum_sub_distrib]
    rw [hagree x hx, sub_self])
  obtain ⟨t, h1, h2⟩ := native_gauge_ld hβ hLD t0 (2 * A) (by linarith) (fun e => by
    rw [ht0]; exact (abs_sub _ _).trans (by linarith [h0 e, hH e]))
  exact ⟨t, fun e => (h1 e).trans (ht0 e), h2⟩

/-- **Matching potential on the deleted host `G − Z`** (H3 of `G`, small `Z`): constant
`(6/α² + 1) · 2A`. -/
theorem matching_potential_delG {α : ℝ} {h : ℕ} (hα : 0 < α) (hH3 : CommonNbrCond G lab F α)
    {Z : Finset V} (hZ : (Z.card : ℝ) ≤ delOf α h * Fintype.card V)
    (lam0 lamH : NCol (delG G Z) lab F → ℝ) {A : ℝ} (hA : 0 ≤ A) (h0 : ∀ e, |lam0 e| ≤ A)
    (hH : ∀ e, |lamH e| ≤ A)
    (hagree : ∀ x : Sym2 V → ℤ, IsLocalProfile (delG G Z) lab F x →
      ∑ e : NCol (delG G Z) lab F, lamH e * (x e.1 : ℝ) =
        ∑ e : NCol (delG G Z) lab F, lam0 e * (x e.1 : ℝ)) :
    ∃ t : NRow (delG G Z) lab F → ℝ,
      (∀ e, S07V35.dat (natB (delG G Z) lab F) t e = lamH e - lam0 e) ∧
      ∀ i, |t i| ≤ (6 / α ^ 2 + 1) * (2 * A) := by
  obtain ⟨t, h1, h2⟩ := matching_potential_ld (by positivity) (linkDeg_delG hα hH3 hZ)
    lam0 lamH hA h0 hH hagree
  have hc : 3 / (2 * (α / 2) ^ 2) = 6 / α ^ 2 := by field_simp; ring
  exact ⟨t, h1, fun i => by rw [← hc]; exact h2 i⟩

end S07V39
