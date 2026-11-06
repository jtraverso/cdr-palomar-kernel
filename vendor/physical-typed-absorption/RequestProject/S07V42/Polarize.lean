/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module
public import RequestProject.S07V42.PolarizeStep
public import RequestProject.S07V28.AbsorberPlacement
set_option maxHeartbeats 4000000 -- build option (original: -DmaxHeartbeats=1600000; raised)
set_option maxRecDepth 16384 -- build option (original: -DmaxRecDepth=8192; raised)
@[expose] public section

/-!
# V42 §7c — integer charge polarization inside `W \ Z`

`polarize`: let `x ∈ M(H[W \ Z])` (zero-extended) with `l1E x ≤ n`, and let `B` have maximum
degree `≤ b`. If `5 n + |Z| + 2 b < β |W|` (`β` from the H3 of the TRUE core subtype), there is an
ACTUAL edge set `Y` of the deleted core host `indG H (W \ Z)` (so `Y` lies inside `W` and avoids
every vertex of `Z`) with

* `1_Y − x ∈ Λ(H[W \ Z])` (zero-extended), hence `[1_Y] = [x]` in `Q` and `1_Y ∈ Λ(H − Z)`
  whenever `x ∈ Λ(H − Z)`;
* `Y ∩ B = ∅` and `|Y| ≤ 4 n`.

Each signed unit of `x` is replaced by a path of length 2 or 4 through fresh vertices
(`polar_step`); induction on `l1E x` (`polar_aux`).
-/

open Finset Classical

noncomputable section

namespace S07V42

open TypedTriangle.SparseEdge TypedTriangle.Dispersal

variable {V I : Type*} [Fintype V]

omit [Fintype V] in
lemma sgnInd_apply (s : Bool) (e f : Sym2 V) :
    sgnInd s e f = if f = e then (if s then 1 else -1) else 0 := by
  unfold sgnInd ind
  by_cases h : f = e <;> cases s <;> simp [h]

lemma l1E_sub_sgn (x : Sym2 V → ℤ) (e : Sym2 V) (hx : x e ≠ 0) :
    l1E (x - sgnInd (decide (0 < x e)) e) = l1E x - 1 := by
  unfold l1E
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ e), ← Finset.add_sum_erase _ _ (Finset.mem_univ e)]
  have hrest : ∑ f ∈ univ.erase e, |(x - sgnInd (decide (0 < x e)) e) f| =
      ∑ f ∈ univ.erase e, |x f| := by
    refine Finset.sum_congr rfl fun f hf => ?_
    have hfe : f ≠ e := Finset.ne_of_mem_erase hf
    simp [sgnInd_apply, hfe]
  rw [hrest]
  simp only [Pi.sub_apply, sgnInd_apply, ite_true]
  rcases lt_or_gt_of_ne hx with h | h
  · have : ¬ (0 < x e) := by omega
    simp only [this, decide_false, Bool.false_eq_true, ite_false]
    rw [abs_of_nonpos (by omega), abs_of_neg h]; ring
  · simp only [h, decide_true, ite_true]
    rw [abs_of_nonneg (by omega), abs_of_pos h]; ring

variable {H : SimpleGraph V} {lab : V → I} {F : Set (Multiset I)} {W : Finset V} {β : ℝ}

/-- **polarization, induction on the ℓ¹ size** -/
theorem polar_aux
    (hH3 : CommonNbrCond (H.comap (Subtype.val : {x // x ∈ W} → V)) (lab ∘ Subtype.val) F β)
    (Z : Finset V) {B : Finset (Sym2 V)} {b : ℕ} (hB : ∀ v, degIn B v ≤ b) :
    ∀ (n : ℕ) (x : Sym2 V → ℤ) (Used : Finset V), l1E x ≤ n →
      (∀ e, x e ≠ 0 → S07V36.IsNCol (indG H (W \ Z)) lab F e ∧ ∀ y ∈ e, y ∈ Used) →
      (Used.card : ℝ) + 3 * n + Z.card + 2 * b < β * W.card →
      ∃ Y : Finset (Sym2 V), ind Y - x ∈ lattice (indG H (W \ Z)) lab F ∧ Disjoint Y B ∧
        (∀ e ∈ Y, e ∈ edges (indG H (W \ Z))) ∧ Y.card ≤ 4 * n ∧
        (∀ e ∈ Y, ∃ y ∈ e, y ∉ Used) := by
  intro n
  induction n with
  | zero =>
    intro x Used hl _ _
    have hx0 : x = 0 := by
      funext e
      have h1 : |x e| ≤ l1E x :=
        Finset.single_le_sum (f := fun e => |x e|) (fun _ _ => abs_nonneg _) (Finset.mem_univ e)
      have : |x e| ≤ 0 := by push_cast at hl; linarith
      simpa using this
    refine ⟨∅, ?_, Finset.disjoint_empty_left _, by simp, by simp, by simp⟩
    rw [hx0, ind_empty', sub_zero]; exact zero_mem _
  | succ n ih =>
    intro x Used hl hsupp hroom
    by_cases hx0 : x = 0
    · refine ⟨∅, ?_, Finset.disjoint_empty_left _, by simp, by simp, by simp⟩
      rw [hx0, ind_empty', sub_zero]; exact zero_mem _
    obtain ⟨e, he⟩ := Function.ne_iff.1 hx0
    obtain ⟨⟨T, hT, heT⟩, hends⟩ := hsupp e he
    induction e using Sym2.ind with
    | h u v =>
      obtain ⟨huT, hvT, huv⟩ := mem_triEdges.1 heT
      obtain ⟨hA, hu, hv⟩ := hT.2.1 u huT v hvT huv
      obtain ⟨w0, -, -, -, -, hk⟩ := triple_of_allowed hT huT hvT huv
      have huU := hends u (Sym2.mem_mk_left u v)
      have hvU := hends v (Sym2.mem_mk_right u v)
      obtain ⟨Yp, Fp, hFp, hYpL, hYpB, hYpE, hYpc, hYpf, hYpv⟩ :=
        polar_step hH3 Z hB hu hv hA hk (decide (0 < x s(u, v))) Used huU hvU (by
          have : (0 : ℝ) ≤ n := Nat.cast_nonneg n
          push_cast at hroom; linarith)
      set x' := x - sgnInd (decide (0 < x s(u, v))) s(u, v) with hx'
      have hl' : l1E x' ≤ n := by
        rw [hx', l1E_sub_sgn x _ he]; push_cast at hl; linarith
      have hsupp' : ∀ f, x' f ≠ 0 →
          S07V36.IsNCol (indG H (W \ Z)) lab F f ∧ ∀ y ∈ f, y ∈ Used ∪ Fp := by
        intro f hf
        by_cases hfe : f = s(u, v)
        · subst hfe
          exact ⟨⟨T, hT, heT⟩, fun y hy => Finset.mem_union_left _ (hends y hy)⟩
        · have : x f ≠ 0 := by
            intro h0; apply hf; simp [hx', sgnInd_apply, hfe, h0]
          obtain ⟨h1, h2⟩ := hsupp f this
          exact ⟨h1, fun y hy => Finset.mem_union_left _ (h2 y hy)⟩
      have hcardU : ((Used ∪ Fp).card : ℝ) ≤ Used.card + 3 := by
        have := (Finset.card_union_le Used Fp).trans (Nat.add_le_add_left hFp _)
        exact_mod_cast this
      obtain ⟨YL, hYLL, hYLB, hYLE, hYLc, hYLf⟩ := ih x' (Used ∪ Fp) hl' hsupp' (by
        push_cast at hroom; linarith)
      have hdisj : Disjoint Yp YL := by
        rw [Finset.disjoint_left]
        intro f hfp hfl
        obtain ⟨y, hy, hyU⟩ := hYLf f hfl
        exact hyU (hYpv f hfp y hy)
      refine ⟨Yp ∪ YL, ?_, Finset.disjoint_union_left.2 ⟨hYpB, hYLB⟩, ?_, ?_, ?_⟩
      · rw [ind_union hdisj]
        have : ind Yp + ind YL - x = (ind Yp - sgnInd (decide (0 < x s(u, v))) s(u, v)) +
            (ind YL - x') := by rw [hx']; abel
        rw [this]; exact add_mem hYpL hYLL
      · intro f hf
        rcases Finset.mem_union.1 hf with h | h
        exacts [hYpE f h, hYLE f h]
      · refine (Finset.card_union_le _ _).trans ?_
        omega
      · intro f hf
        rcases Finset.mem_union.1 hf with h | h
        · exact hYpf f h
        · obtain ⟨y, hy, hyU⟩ := hYLf f h
          exact ⟨y, hy, fun h' => hyU (Finset.mem_union_left _ h')⟩

/-- **Integer charge polarization inside `W \ Z`.** -/
theorem polarize
    (hH3 : CommonNbrCond (H.comap (Subtype.val : {x // x ∈ W} → V)) (lab ∘ Subtype.val) F β)
    (Z : Finset V) {B : Finset (Sym2 V)} {b : ℕ} (hB : ∀ v, degIn B v ≤ b)
    {x : Sym2 V → ℤ} (hx : x ∈ MZ H lab F W Z) {n : ℕ} (hn : l1E x ≤ n)
    (hroom : 5 * (n : ℝ) + Z.card + 2 * b < β * W.card) :
    ∃ Y : Finset (Sym2 V), ind Y - x ∈ lattice (indG H (W \ Z)) lab F ∧ Disjoint Y B ∧
      (∀ e ∈ Y, e ∈ edges (indG H (W \ Z))) ∧ Y.card ≤ 4 * n := by
  set Sx := univ.filter (fun e : Sym2 V => x e ≠ 0) with hSx
  have hSx_card : (Sx.card : ℤ) ≤ l1E x := by
    unfold l1E
    calc (Sx.card : ℤ) = ∑ e ∈ Sx, (1 : ℤ) := by simp
      _ ≤ ∑ e ∈ Sx, |x e| := Finset.sum_le_sum fun e he => by
          have := (Finset.mem_filter.1 he).2
          exact Int.one_le_abs this
      _ ≤ ∑ e, |x e| := Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
          (fun _ _ _ => abs_nonneg _)
  have hU0 : (support Sx).card ≤ 2 * n := by
    have h1 := S07V28.card_support_le Sx
    have h2 : Sx.card ≤ n := by
      have := hSx_card.trans hn
      exact_mod_cast this
    omega
  have hsupp : ∀ e, x e ≠ 0 →
      S07V36.IsNCol (indG H (W \ Z)) lab F e ∧ ∀ y ∈ e, y ∈ support Sx := by
    intro e he
    refine ⟨?_, fun y hy => mem_support_of_mem (Finset.mem_filter.2 ⟨Finset.mem_univ _, he⟩) hy⟩
    by_contra hn'
    exact he (S07V38.localProfile_supp hx e hn')
  obtain ⟨Y, hYL, hYB, hYE, hYc, -⟩ := polar_aux hH3 Z hB n x (support Sx) hn hsupp (by
    have : ((support Sx).card : ℝ) ≤ 2 * n := by exact_mod_cast hU0
    linarith)
  exact ⟨Y, hYL, hYB, hYE, hYc⟩

end S07V42
