/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module
public import RequestProject.S07V42.PolarizeBasic
set_option maxHeartbeats 4000000 -- build option (original: -DmaxHeartbeats=1600000; raised)
set_option maxRecDepth 16384 -- build option (original: -DmaxRecDepth=8192; raised)
@[expose] public section

/-!
# V42 §7b — one polarization step

For a signed copy `± 1_{uv}` of an edge `uv` of `H[W \ Z]` that lies in an allowed triangle, the
step produces an ACTUAL edge set `Yp` of the deleted core host with
`1_{Yp} ∓ 1_{uv} ∈ Λ(H[W \ Z])`, avoiding the forbidden set `B`, using only fresh vertices of
`W \ Z`:

* `−1_{uv}`: `Yp = {uw, wv}` (triangle `uvw`);
* `+1_{uv}`: `Yp = {uw', w'w, wv', v'v}` (triangles `uww'`, `wvv'` minus `uvw`).

The original edge `uv` is never used, so `Yp` avoids `B` even when `uv ∈ B`.
-/

open Finset Classical

noncomputable section

namespace S07V42

open TypedTriangle.SparseEdge

variable {V I : Type*} [Fintype V]

/-- a signed unit edge vector -/
def sgnInd (s : Bool) (e : Sym2 V) : Sym2 V → ℤ := if s then ind {e} else -ind {e}

omit [Fintype V] in
lemma tri_mem {G : SimpleGraph V} {lab : V → I} {F : Set (Multiset I)} {T : Finset V}
    (hT : IsAllowed G lab F T) : ind (triEdges T) ∈ lattice G lab F :=
  Submodule.subset_span ⟨T, hT, rfl⟩

lemma mem_edges_indG {H : SimpleGraph V} {U : Finset V} {a b : V} (h : H.Adj a b) (ha : a ∈ U)
    (hb : b ∈ U) : s(a, b) ∈ edges (indG H U) := by
  rw [mem_edges, SimpleGraph.mem_edgeSet]; exact ⟨h, ha, hb⟩

variable {H : SimpleGraph V} {lab : V → I} {F : Set (Multiset I)} {W : Finset V} {β : ℝ}

/-- **one polarization step** -/
theorem polar_step
    (hH3 : CommonNbrCond (H.comap (Subtype.val : {x // x ∈ W} → V)) (lab ∘ Subtype.val) F β)
    (Z : Finset V) {B : Finset (Sym2 V)} {b : ℕ} (hB : ∀ v, degIn B v ≤ b) {u v : V}
    (hu : u ∈ W \ Z) (hv : v ∈ W \ Z) (huvA : H.Adj u v) {k : I}
    (hk : ({lab u, lab v, k} : Multiset I) ∈ F) (s : Bool) (Used : Finset V) (huU : u ∈ Used)
    (hvU : v ∈ Used) (hroom : (Used.card : ℝ) + 2 + Z.card + 2 * b < β * W.card) :
    ∃ Yp : Finset (Sym2 V), ∃ Fp : Finset V, Fp.card ≤ 3 ∧
      ind Yp - sgnInd s s(u, v) ∈ lattice (indG H (W \ Z)) lab F ∧ Disjoint Yp B ∧
      (∀ e ∈ Yp, e ∈ edges (indG H (W \ Z))) ∧ Yp.card ≤ 4 ∧
      (∀ e ∈ Yp, ∃ x ∈ e, x ∉ Used) ∧ (∀ e ∈ Yp, ∀ x ∈ e, x ∈ Used ∪ Fp) := by
  have huv : u ≠ v := huvA.ne
  have hu' := Finset.mem_sdiff.1 hu
  have hv' := Finset.mem_sdiff.1 hv
  obtain ⟨w, hwW, hwZ, hwU, huw, hvw, hlw, huwB, hwvB⟩ :=
    exists_fresh hH3 Z hB hu'.1 hv'.1 huv hk Used (by linarith)
  have hwu : w ≠ u := fun h => hwU (h ▸ huU)
  have hwv : w ≠ v := fun h => hwU (h ▸ hvU)
  have hwWZ : w ∈ W \ Z := Finset.mem_sdiff.2 ⟨hwW, hwZ⟩
  have hF0 : ({lab u, lab v, lab w} : Multiset I) ∈ F := hlw ▸ hk
  have hT0 : IsAllowed (indG H (W \ Z)) lab F {u, v, w} :=
    allowed_indG hu hv hwWZ huvA huw hvw hF0
  have hind0 := ind_triangle huv (Ne.symm hwu) (Ne.symm hwv)
  cases s with
  | false =>
    refine ⟨{s(u, w), s(w, v)}, {w}, by simp, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · have hne : s(u, w) ∉ ({s(w, v)} : Finset (Sym2 V)) := by
        simp [huv, Ne.symm hwu]
      rw [ind_insert hne]
      have hmem := tri_mem hT0
      rw [hind0] at hmem
      have e1 : s(w, v) = s(v, w) := Sym2.eq_swap
      convert hmem using 1
      rw [e1]; simp only [sgnInd, Bool.false_eq_true, ite_false]; abel
    · rw [Finset.disjoint_left]
      intro e he
      simp only [Finset.mem_insert, Finset.mem_singleton] at he
      rcases he with rfl | rfl
      exacts [huwB, hwvB]
    · intro e he
      simp only [Finset.mem_insert, Finset.mem_singleton] at he
      rcases he with rfl | rfl
      · exact mem_edges_indG huw hu hwWZ
      · exact mem_edges_indG hvw.symm hwWZ hv
    · exact (Finset.card_insert_le _ _).trans (by simp)
    · intro e he
      simp only [Finset.mem_insert, Finset.mem_singleton] at he
      rcases he with rfl | rfl
      · exact ⟨w, Sym2.mem_mk_right _ _, hwU⟩
      · exact ⟨w, Sym2.mem_mk_left _ _, hwU⟩
    · intro e he x hx
      simp only [Finset.mem_insert, Finset.mem_singleton] at he
      rcases he with rfl | rfl <;> rw [Sym2.mem_iff] at hx <;>
        rcases hx with rfl | rfl <;> simp [huU, hvU]
  | true =>
    have hk1 : ({lab u, lab w, lab v} : Multiset I) ∈ F := by rw [← mset_swap23]; exact hF0
    obtain ⟨w', hw'W, hw'Z, hw'U, huw', hww', hlw', huw'B, hw'wB⟩ :=
      exists_fresh hH3 Z hB hu'.1 hwW (Ne.symm hwu) hk1 (insert w Used) (by
        have := Finset.card_insert_le w Used
        have : ((insert w Used).card : ℝ) ≤ Used.card + 1 := by exact_mod_cast this
        linarith)
    simp only [Finset.mem_insert, not_or] at hw'U
    obtain ⟨hw'w, hw'U⟩ := hw'U
    have hw'u : w' ≠ u := fun h => hw'U (h ▸ huU)
    have hw'v : w' ≠ v := fun h => hw'U (h ▸ hvU)
    have hk2 : ({lab w, lab v, lab u} : Multiset I) ∈ F := by
      rw [mset_swap12, mset_swap23, mset_swap12]; exact hF0
    obtain ⟨v', hv'W, hv'Z, hv'U, hwv', hvv', hlv', hwv'B, hv'vB⟩ :=
      exists_fresh hH3 Z hB hwW hv'.1 hwv hk2 (insert w' (insert w Used)) (by
        have h1 := Finset.card_insert_le w' (insert w Used)
        have h2 := Finset.card_insert_le w Used
        have : ((insert w' (insert w Used)).card : ℝ) ≤ Used.card + 2 := by
          exact_mod_cast (h1.trans (Nat.add_le_add_right h2 1))
        linarith)
    simp only [Finset.mem_insert, not_or] at hv'U
    obtain ⟨hv'w', hv'w, hv'U⟩ := hv'U
    have hv'u : v' ≠ u := fun h => hv'U (h ▸ huU)
    have hv'v : v' ≠ v := fun h => hv'U (h ▸ hvU)
    have hw'WZ : w' ∈ W \ Z := Finset.mem_sdiff.2 ⟨hw'W, hw'Z⟩
    have hv'WZ : v' ∈ W \ Z := Finset.mem_sdiff.2 ⟨hv'W, hv'Z⟩
    have hT1 : IsAllowed (indG H (W \ Z)) lab F {u, w, w'} :=
      allowed_indG hu hwWZ hw'WZ huw huw' hww' (by rw [hlw']; exact hk1)
    have hT2 : IsAllowed (indG H (W \ Z)) lab F {w, v, v'} :=
      allowed_indG hwWZ hv hv'WZ hvw.symm hwv' hvv' (by rw [hlv']; exact hk2)
    have hind1 := ind_triangle (Ne.symm hwu) (Ne.symm hw'u) (Ne.symm hw'w)
    have hind2 := ind_triangle hwv (Ne.symm hv'w) (Ne.symm hv'v)
    refine ⟨{s(u, w'), s(w', w), s(w, v'), s(v', v)}, {w, w', v'}, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · exact (Finset.card_insert_le _ _).trans (by
        exact Nat.succ_le_succ ((Finset.card_insert_le _ _).trans (by simp)))
    · have n1 : s(u, w') ∉ ({s(w', w), s(w, v'), s(v', v)} : Finset (Sym2 V)) := by
        simp [huv, Ne.symm hwu, Ne.symm hw'u, Ne.symm hv'u, hw'w]
      have n2 : s(w', w) ∉ ({s(w, v'), s(v', v)} : Finset (Sym2 V)) := by
        simp [Ne.symm hv'w', hw'v, hwv, Ne.symm hv'w]
      have n3 : s(w, v') ∉ ({s(v', v)} : Finset (Sym2 V)) := by
        simp [hwv, hv'v]
      rw [ind_insert n1, ind_insert n2, ind_insert n3]
      have hmem := sub_mem (add_mem (tri_mem hT1) (tri_mem hT2)) (tri_mem hT0)
      rw [hind0, hind1, hind2] at hmem
      convert hmem using 1
      have e1 : s(w', w) = s(w, w') := Sym2.eq_swap
      have e2 : s(v', v) = s(v, v') := Sym2.eq_swap
      have e3 : s(w, v) = s(v, w) := Sym2.eq_swap
      rw [e1, e2, e3]; simp only [sgnInd, ite_true]; abel
    · rw [Finset.disjoint_left]
      intro e he
      simp only [Finset.mem_insert, Finset.mem_singleton] at he
      rcases he with rfl | rfl | rfl | rfl
      exacts [huw'B, hw'wB, hwv'B, hv'vB]
    · intro e he
      simp only [Finset.mem_insert, Finset.mem_singleton] at he
      rcases he with rfl | rfl | rfl | rfl
      · exact mem_edges_indG huw' hu hw'WZ
      · exact mem_edges_indG hww'.symm hw'WZ hwWZ
      · exact mem_edges_indG hwv' hwWZ hv'WZ
      · exact mem_edges_indG hvv'.symm hv'WZ hv
    · refine (Finset.card_insert_le _ _).trans (Nat.succ_le_succ ?_)
      refine (Finset.card_insert_le _ _).trans (Nat.succ_le_succ ?_)
      exact (Finset.card_insert_le _ _).trans (by simp)
    · intro e he
      simp only [Finset.mem_insert, Finset.mem_singleton] at he
      rcases he with rfl | rfl | rfl | rfl
      · exact ⟨w', Sym2.mem_mk_right _ _, hw'U⟩
      · exact ⟨w', Sym2.mem_mk_left _ _, hw'U⟩
      · exact ⟨v', Sym2.mem_mk_right _ _, hv'U⟩
      · exact ⟨v', Sym2.mem_mk_left _ _, hv'U⟩
    · intro e he x hx
      simp only [Finset.mem_insert, Finset.mem_singleton] at he
      rcases he with rfl | rfl | rfl | rfl <;> rw [Sym2.mem_iff] at hx <;>
        rcases hx with rfl | rfl <;> simp [huU, hvU]

end S07V42
