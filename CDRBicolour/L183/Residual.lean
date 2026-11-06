/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license.
Authors: Juan Pablo Traverso Gianini
-/
module

public import CDRBicolour.EdgeColouring.Restrict
public import CDRBicolour.EdgeColouring.CCJSBridge
public import CDRBicolour.EdgeColouring.PlantholtBridge
public import CDRBicolour.EdgeColouring.Counting
public import Mathlib.Combinatorics.SimpleGraph.DeleteEdges

/-!
# L183: the new residual is `a`-edge-colourable (conditional on CCJS and Plantholt)

`F` is a simple graph of ODD order `c` with one root `w` of degree `s`, a set `P` of `s/2`
vertices of degree `a-2`, and all other vertices of degree `a`.  Under the numerical
conditions of the P2 family (`P2Family.lean`, `y ≥ 33`) `F` is `a`-edge-colourable.

Proof (candidate L183, audited):
1. `H = F - w` lives on `C - w` (even order `c-1`), `δ(H) ≥ a-3`.  If `Δ(H) < a`, Vizing.
   Otherwise Plantholt's Corollary 1.7 reduces colourability to the absence of `a`-overfull odd
   sets; by Plantholt's Lemma 1.3 (formalized) the only candidates are `H - x`, and
   `2e(H-x) ≤ a(c-3)` because `s ≥ 3`.
2. `F` has no `a`-overfull odd set: sets avoiding `w` live in the colourable `F - w`; sets of
   size `≤ a` by the complete-graph bound; larger sets by counting through the complement.
3. A minimal non-`a`-colourable subgraph `G` would contain `w` (step 1), so `δ ≤ s`; on its
   support it is critical with `Δ = a`, and Cao–Chen–Jing–Shan makes it overfull — impossible
   by step 2.

The two external theorems enter ONLY as the hypotheses `CCJS_Theorem_1_2` and
`Plantholt_Corollary_1_7` (literal statements, `EdgeColouring/Defs.lean`).
-/

@[expose] public section

namespace CDRBicolour.L183

open Finset

universe u

variable {W : Type u} [Fintype W] [DecidableEq W]

/-- `F` without the edges at `w`. -/
def deleteAt (F : SimpleGraph W) (w : W) : SimpleGraph W := F.deleteEdges (F.incidenceSet w)

variable (F : SimpleGraph W) [DecidableRel F.Adj] (w : W)

instance : DecidableRel (deleteAt F w).Adj := by
  unfold deleteAt; infer_instance

theorem deleteAt_adj {x y : W} :
    (deleteAt F w).Adj x y ↔ F.Adj x y ∧ x ≠ w ∧ y ≠ w := by
  simp only [deleteAt, SimpleGraph.deleteEdges_adj, SimpleGraph.incidenceSet, Set.mem_setOf_eq,
    SimpleGraph.mem_edgeSet, Sym2.mem_iff]
  constructor
  · rintro ⟨h, hn⟩
    refine ⟨h, fun hx => hn ⟨h, Or.inl hx.symm⟩, fun hy => hn ⟨h, Or.inr hy.symm⟩⟩
  · rintro ⟨h, hx, hy⟩
    refine ⟨h, fun ⟨_, hw⟩ => ?_⟩
    rcases hw with hw | hw
    · exact hx hw.symm
    · exact hy hw.symm

theorem deleteAt_le : deleteAt F w ≤ F := fun _ _ h => ((deleteAt_adj F w).1 h).1

theorem supported_deleteAt : Supported (deleteAt F w) (univ.erase w) := by
  intro x y h
  exact mem_erase.2 ⟨((deleteAt_adj F w).1 h).2.1, mem_univ _⟩

theorem degree_deleteAt_le (v : W) : (deleteAt F w).degree v ≤ F.degree v := by
  rw [← SimpleGraph.card_neighborFinset_eq_degree, ← SimpleGraph.card_neighborFinset_eq_degree]
  refine card_le_card fun y hy => ?_
  rw [SimpleGraph.mem_neighborFinset] at hy ⊢
  exact ((deleteAt_adj F w).1 hy).1

theorem degree_deleteAt_ge {v : W} (hv : v ≠ w) : F.degree v - 1 ≤ (deleteAt F w).degree v := by
  rw [← SimpleGraph.card_neighborFinset_eq_degree, ← SimpleGraph.card_neighborFinset_eq_degree]
  have : (F.neighborFinset v).erase w ⊆ (deleteAt F w).neighborFinset v := by
    intro y hy
    rw [mem_erase, SimpleGraph.mem_neighborFinset] at hy
    rw [SimpleGraph.mem_neighborFinset, deleteAt_adj]
    exact ⟨hy.2, hv, hy.1⟩
  have h1 := card_le_card this
  have h2 := pred_card_le_card_erase (s := F.neighborFinset v) (a := w)
  omega

theorem card_edgeFinset_deleteAt :
    (deleteAt F w).edgeFinset.card + F.degree w = F.edgeFinset.card := by
  have hE : (deleteAt F w).edgeFinset = F.edgeFinset.filter fun e => w ∉ e := by
    ext e
    induction e using Sym2.ind with
    | _ x y =>
      simp only [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet, mem_filter, deleteAt_adj,
        Sym2.mem_iff, not_or]
      constructor
      · rintro ⟨h, hx, hy⟩; exact ⟨h, fun h' => hx h'.symm, fun h' => hy h'.symm⟩
      · rintro ⟨h, hx, hy⟩; exact ⟨h, fun h' => hx h'.symm, fun h' => hy h'.symm⟩
  have hI : F.edgeFinset.filter (fun e => w ∈ e) = F.incidenceFinset w :=
    (SimpleGraph.incidenceFinset_eq_filter F w).symm
  have := card_filter_add_card_filter_not (s := F.edgeFinset) (fun e => w ∈ e)
  rw [hI, SimpleGraph.card_incidenceFinset_eq_degree, hE] at *
  omega

/-- Edges inside a set avoiding `w` are the same in `F` and `F - w`. -/
theorem edgesIn_deleteAt {S : Finset W} (hw : w ∉ S) :
    edgesIn (deleteAt F w) S = edgesIn F S := by
  ext e
  induction e using Sym2.ind with
  | _ x y =>
    simp only [edgesIn, mem_filter, SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet,
      deleteAt_adj, Sym2.mem_iff, forall_eq_or_imp, forall_eq]
    constructor
    · rintro ⟨⟨h, -, -⟩, hx, hy⟩; exact ⟨h, hx, hy⟩
    · rintro ⟨h, hx, hy⟩
      exact ⟨⟨h, fun h' => hw (h' ▸ hx), fun h' => hw (h' ▸ hy)⟩, hx, hy⟩


/-- Step 1: `F - w` is `a`-edge-colourable (Plantholt's Corollary 1.7 + Lemma 1.3). -/
theorem step1 (a s : ℕ)
    (hle : ∀ v, (deleteAt F w).degree v ≤ a)
    (hge : ∀ v, v ≠ w → a - 3 ≤ (deleteAt F w).degree v)
    (hE : 2 * F.edgeFinset.card = a * (Fintype.card W - 1))
    (hFwE : (deleteAt F w).edgeFinset.card + s = F.edgeFinset.card)
    (hodd : Odd (Fintype.card W)) (hc3 : 3 ≤ Fintype.card W)
    (hpl : 12 * (Fintype.card W - 1) + 63 ≤ 14 * a)
    (hhalf : Fintype.card W - 1 < 2 * (a - 3)) (hs : 3 ≤ s) (ha : 4 ≤ a) :
    EdgeColourable (deleteAt F w) a := by
  classical
  by_cases hlt : (deleteAt F w).maxDegree < a
  · exact edgeColourable_of_maxDegree_lt _ hlt
  have hΔ : (deleteAt F w).maxDegree = a := by
    have := SimpleGraph.maxDegree_le_of_forall_degree_le (deleteAt F w) a hle
    omega
  have hsupp := supported_deleteAt F w
  apply edgeColourable_of_edgeColourable_restrict hsupp
  have hHΔ : (restrict (deleteAt F w) (univ.erase w)).maxDegree = a := by
    rw [maxDegree_restrict hsupp, hΔ]
  have hHcard : Fintype.card (univ.erase w) = Fintype.card W - 1 := by
    rw [Fintype.card_coe, card_erase_of_mem (mem_univ w), card_univ]
  have hNe : Nonempty (univ.erase w) := by
    apply Fintype.card_pos_iff.1
    rw [hHcard]; omega
  have hHδ : a - 3 ≤ (restrict (deleteAt F w) (univ.erase w)).minDegree := by
    apply SimpleGraph.le_minDegree_of_forall_le_degree
    intro x
    rw [degree_restrict hsupp]
    exact hge x.1 (mem_erase.1 x.2).1
  have hEven : Even (Fintype.card (univ.erase w)) := by
    rw [hHcard]; obtain ⟨m, hm⟩ := hodd; exact ⟨m, by omega⟩
  have hdens : 12 * Fintype.card (univ.erase w) ≤
      7 * (3 * (restrict (deleteAt F w) (univ.erase w)).minDegree -
        (restrict (deleteAt F w) (univ.erase w)).maxDegree) := by
    rw [hHcard, hHΔ]; omega
  by_contra hcol
  obtain ⟨S, hS⟩ := plantholt_67 _ hEven hdens (by rw [hHΔ]; exact hcol)
  rw [hHΔ] at hS
  have hhalf2 : Fintype.card (univ.erase w) <
      2 * (restrict (deleteAt F w) (univ.erase w)).minDegree := by
    rw [hHcard]; omega
  have hS2 : InducesFullOrOverfull (restrict (deleteAt F w) (univ.erase w))
      (restrict (deleteAt F w) (univ.erase w)).maxDegree S := by
    rw [hHΔ]; exact ⟨hS.1, hS.2.1, hS.2.2.le⟩
  obtain ⟨x, rfl⟩ := plantholt_lemma_1_3 _ _ hEven hhalf2 S hS2
  have herase := edgesIn_erase_identity (restrict (deleteAt F w) (univ.erase w)) x
  have hHE := card_edgeFinset_restrict hsupp
  have hdx : a - 3 ≤ (restrict (deleteAt F w) (univ.erase w)).degree x := by
    rw [degree_restrict hsupp]; exact hge x.1 (mem_erase.1 x.2).1
  have hScard : (univ.erase x).card = Fintype.card W - 2 := by
    rw [card_erase_of_mem (mem_univ x), card_univ, hHcard]; omega
  have hov := hS.2.2
  rw [hScard] at hov
  zify [show 2 ≤ Fintype.card W by omega, show 1 ≤ Fintype.card W - 2 by omega] at hov
  zify [show 1 ≤ Fintype.card W by omega] at hE
  zify [show 3 ≤ a by omega] at hdx
  zify at herase hHE hFwE hs
  nlinarith

/-- Step 2: `F` has no `a`-overfull odd set. -/
theorem step2 (a s : ℕ) (hFw : EdgeColourable (deleteAt F w) a)
    (hge : ∀ v, v ≠ w → a - 2 ≤ F.degree v)
    (hE : 2 * F.edgeFinset.card = a * (Fintype.card W - 1))
    (hc3 : 3 ≤ Fintype.card W) (hca : Fintype.card W + 2 ≤ 2 * a) (ha : 4 ≤ a) :
    ∀ S : Finset W, ¬ InducesOverfull F a S := by
  classical
  intro S hS
  obtain ⟨hoddS, h3S, hlt⟩ := hS
  by_cases hwS : w ∈ S
  · by_cases hSa : S.card ≤ a
    · have hb := two_mul_edgesIn_le F S
      have h1 : S.card * S.card - S.card = S.card * (S.card - 1) := by rw [Nat.mul_sub_one]
      have h2 : S.card * (S.card - 1) ≤ a * (S.card - 1) := Nat.mul_le_mul_right _ hSa
      omega
    · push_neg at hSa
      have hid := edgesIn_compl_identity F S
      have hX : ∀ v ∈ Sᶜ, a - 2 ≤ F.degree v := by
        intro v hv
        exact hge v (fun h => (mem_compl.1 hv) (h ▸ hwS))
      have hsumX : (a - 2) * Sᶜ.card ≤ ∑ v ∈ Sᶜ, F.degree v := by
        calc (a - 2) * Sᶜ.card = ∑ _v ∈ Sᶜ, (a - 2) := by rw [sum_const, smul_eq_mul, mul_comm]
          _ ≤ ∑ v ∈ Sᶜ, F.degree v := sum_le_sum hX
      have heX := two_mul_edgesIn_le F Sᶜ
      have hcardS : S.card + Sᶜ.card = Fintype.card W := card_add_card_compl S
      have ht : Sᶜ.card + 3 ≤ a := by omega
      zify [show 2 ≤ a by omega] at hsumX
      zify [Nat.le_mul_self Sᶜ.card] at heX
      zify at hid hcardS ht
      zify [show 1 ≤ Fintype.card W by omega] at hE
      zify [show 1 ≤ S.card by omega] at hlt
      have w8 : (Sᶜ.card : ℤ) * ((Sᶜ.card : ℤ) + 3 - a) ≤ 0 :=
        mul_nonpos_of_nonneg_of_nonpos (by positivity) (by linarith)
      nlinarith
  · apply not_inducesOverfull_of_edgeColourable hFw S
    refine ⟨hoddS, h3S, ?_⟩
    rw [edgesIn_deleteAt F w hwS]
    exact hlt

/-- **L183**, conditional on the two external theorems (literal statements). -/
theorem l183 (hCCJS : CCJS_Theorem_1_2_large.{u})
    (a s : ℕ) (P : Finset W)
    (hdw : F.degree w = s) (hwP : w ∉ P) (hdP : ∀ v ∈ P, F.degree v = a - 2)
    (hdR : ∀ v, v ≠ w → v ∉ P → F.degree v = a) (hPs : 2 * P.card = s)
    (hodd : Odd (Fintype.card W))
    (hpl : 12 * (Fintype.card W - 1) + 63 ≤ 14 * a)
    (hhalf : Fintype.card W - 1 < 2 * (a - 3))
    (hs : 3 ≤ s) (hsa : s ≤ a) (hca : Fintype.card W + 2 ≤ 2 * a)
    (hccjs : 3 * Fintype.card W + 7 * s ≤ 4 * a + 17) (ha : 4 ≤ a) (ha27 : 26 ≤ a) :
    EdgeColourable F a := by
  classical
  have hdeg_le : ∀ v, F.degree v ≤ a := by
    intro v
    by_cases hvw : v = w
    · rw [hvw, hdw]; exact hsa
    by_cases hvP : v ∈ P
    · rw [hdP v hvP]; omega
    · rw [hdR v hvw hvP]
  have hdeg_ge : ∀ v, v ≠ w → a - 2 ≤ F.degree v := by
    intro v hvw
    by_cases hvP : v ∈ P
    · rw [hdP v hvP]
    · rw [hdR v hvw hvP]; omega
  have hc3 : 3 ≤ Fintype.card W := by
    have h1 : (insert w P).card ≤ Fintype.card W := card_le_univ _
    rw [card_insert_of_notMem hwP] at h1
    omega
  have hE : 2 * F.edgeFinset.card = a * (Fintype.card W - 1) := by
    rw [← F.sum_degrees_eq_twice_card_edges, ← add_sum_erase _ _ (mem_univ w), hdw]
    have h1 : ∀ v ∈ univ.erase w, F.degree v + 2 * (if v ∈ P then 1 else 0) = a := by
      intro v hv
      have hvw : v ≠ w := (mem_erase.1 hv).1
      by_cases hvP : v ∈ P
      · simp only [hvP, if_true, hdP v hvP]; omega
      · simp only [hvP, if_false, hdR v hvw hvP]; omega
    have h2 : ∑ v ∈ univ.erase w, (F.degree v + 2 * (if v ∈ P then 1 else 0)) =
        a * (Fintype.card W - 1) := by
      rw [sum_congr rfl h1, sum_const, card_erase_of_mem (mem_univ w), card_univ, smul_eq_mul,
        mul_comm]
    have hf : (univ.erase w).filter (fun v => v ∈ P) = P := by
      ext v
      simp only [mem_filter, mem_erase, mem_univ, and_true]
      constructor
      · rintro ⟨-, h⟩; exact h
      · intro h; exact ⟨fun h2 => hwP (h2 ▸ h), h⟩
    have h3 : ∑ v ∈ univ.erase w, 2 * (if v ∈ P then (1 : ℕ) else 0) = 2 * P.card := by
      rw [← mul_sum, sum_boole, hf]
      simp
    rw [sum_add_distrib, h3] at h2
    omega
  have hFw_le : ∀ v, (deleteAt F w).degree v ≤ a :=
    fun v => (degree_deleteAt_le F w v).trans (hdeg_le v)
  have hFw_ge : ∀ v, v ≠ w → a - 3 ≤ (deleteAt F w).degree v := by
    intro v hvw
    have := degree_deleteAt_ge F w hvw
    have := hdeg_ge v hvw
    omega
  have hFwE : (deleteAt F w).edgeFinset.card + s = F.edgeFinset.card := by
    rw [← hdw]; exact card_edgeFinset_deleteAt F w
  have h1 := step1 F w a s hFw_le hFw_ge hE hFwE hodd hc3 hpl hhalf hs ha
  have h2 := step2 F w a s h1 hdeg_ge hE hc3 hca ha
  -- STEP 3
  by_contra hcol
  obtain ⟨H0, hH0F, hH0, hcrit⟩ := exists_critical_subgraph F hcol
  have hdegH0 : ∀ v, H0.degree v ≤ F.degree v := by
    intro v
    rw [← SimpleGraph.card_neighborFinset_eq_degree, ← SimpleGraph.card_neighborFinset_eq_degree]
    refine card_le_card fun y hy => ?_
    rw [SimpleGraph.mem_neighborFinset] at hy ⊢
    exact hH0F hy
  have hΔle : H0.maxDegree ≤ a :=
    SimpleGraph.maxDegree_le_of_forall_degree_le _ _ fun v => (hdegH0 v).trans (hdeg_le v)
  have hΔ : H0.maxDegree = a := by
    by_contra hne
    exact hH0 (edgeColourable_of_maxDegree_lt H0 (lt_of_le_of_ne hΔle hne))
  have hsuppU : Supported H0 (univ.filter fun v => 0 < H0.degree v) := by
    intro x y hxy
    exact mem_filter.2 ⟨mem_univ _, (SimpleGraph.degree_pos_iff_exists_adj H0 x).2 ⟨y, hxy⟩⟩
  have hwU : w ∈ univ.filter fun v => 0 < H0.degree v := by
    by_contra hwU
    apply hH0
    refine edgeColourable_of_le ?_ h1
    intro x y hxy
    rw [deleteAt_adj]
    refine ⟨hH0F hxy, ?_, ?_⟩
    · rintro rfl; exact hwU (hsuppU _ _ hxy)
    · rintro rfl; exact hwU (hsuppU _ _ hxy.symm)
  have hRΔ : (restrict H0 (univ.filter fun v => 0 < H0.degree v)).maxDegree = a := by
    rw [maxDegree_restrict hsuppU, hΔ]
  have hRcrit : IsCritical (restrict H0 (univ.filter fun v => 0 < H0.degree v)) := by
    refine ⟨?_, ?_, ?_⟩
    · intro x; rw [degree_restrict hsuppU]; exact (mem_filter.1 x.2).2
    · rw [hRΔ]; intro hRcol
      exact hH0 (edgeColourable_of_edgeColourable_restrict hsuppU hRcol)
    · intro K hK
      rw [hRΔ]
      have hKle : K.map (Function.Embedding.subtype (· ∈ univ.filter
          fun v => 0 < H0.degree v)) ≤ H0 := by
        intro x y h
        rw [SimpleGraph.map_adj] at h
        obtain ⟨u, v, huv, rfl, rfl⟩ := h
        exact hK.le huv
      have hback : (K.map (Function.Embedding.subtype (· ∈ univ.filter
          fun v => 0 < H0.degree v))).comap
          (Function.Embedding.subtype (· ∈ univ.filter fun v => 0 < H0.degree v)) = K :=
        SimpleGraph.comap_map_eq _ _
      have hKlt : K.map (Function.Embedding.subtype (· ∈ univ.filter
          fun v => 0 < H0.degree v)) < H0 := by
        refine lt_of_le_of_ne hKle ?_
        intro heq
        apply hK.ne
        rw [← hback, heq]
        rfl
      have h3 := edgeColourable_restrict_of_edgeColourable
        (U := univ.filter fun v => 0 < H0.degree v) (hcrit _ hKlt)
      exact hback ▸ h3
  have hδ : (restrict H0 (univ.filter fun v => 0 < H0.degree v)).minDegree ≤ s := by
    calc (restrict H0 (univ.filter fun v => 0 < H0.degree v)).minDegree
        ≤ (restrict H0 (univ.filter fun v => 0 < H0.degree v)).degree ⟨w, hwU⟩ :=
          SimpleGraph.minDegree_le_degree _ _
      _ = H0.degree w := degree_restrict hsuppU _
      _ ≤ F.degree w := hdegH0 w
      _ = s := hdw
  have hUc : (univ.filter fun v => 0 < H0.degree v).card ≤ Fintype.card W := card_le_univ _
  have hov := hCCJS _ _ hRcrit (by
    rw [hRΔ, Fintype.card_coe]
    have q1 : ((restrict H0 (univ.filter fun v => 0 < H0.degree v)).minDegree : ℤ) ≤ s := by
      exact_mod_cast hδ
    have q2 : ((univ.filter fun v => 0 < H0.degree v).card : ℤ) ≤ Fintype.card W := by
      exact_mod_cast hUc
    have q3 : 3 * (Fintype.card W : ℤ) + 7 * s ≤ 4 * a + 17 := by exact_mod_cast hccjs
    linarith) (by
    have hNe : Nonempty ↥(univ.filter fun v => 0 < H0.degree v) := ⟨⟨w, hwU⟩⟩
    have hlt := SimpleGraph.maxDegree_lt_card_verts
      (G := restrict H0 (univ.filter fun v => 0 < H0.degree v))
    rw [hRΔ] at hlt
    omega)
  unfold IsOverfull at hov
  rw [hRΔ, Fintype.card_coe, card_edgeFinset_restrict hsuppU] at hov
  have h2e : 2 * H0.edgeFinset.card ≤ a * (univ.filter fun v => 0 < H0.degree v).card := by
    rw [← H0.sum_degrees_eq_twice_card_edges]
    calc ∑ v, H0.degree v = ∑ v ∈ univ.filter (fun v => 0 < H0.degree v), H0.degree v := by
          refine (sum_subset (subset_univ _) fun v _ hv => ?_).symm
          simp only [mem_filter, mem_univ, true_and, not_lt] at hv
          omega
      _ ≤ ∑ _v ∈ univ.filter (fun v => 0 < H0.degree v), a :=
          sum_le_sum fun v _ => (hdegH0 v).trans (hdeg_le v)
      _ = a * (univ.filter fun v => 0 < H0.degree v).card := by
          rw [sum_const, smul_eq_mul, mul_comm]
  have hsub : H0.edgeFinset ⊆ edgesIn F (univ.filter fun v => 0 < H0.degree v) := by
    intro e he
    simp only [edgesIn, mem_filter]
    refine ⟨SimpleGraph.edgeFinset_mono hH0F he, fun v hv => ?_⟩
    induction e using Sym2.ind with
    | _ x y =>
      have hxy : H0.Adj x y := (SimpleGraph.mem_edgeFinset).1 he
      rcases Sym2.mem_iff.1 hv with rfl | rfl
      · exact mem_filter.1 (hsuppU _ _ hxy)
      · exact mem_filter.1 (hsuppU _ _ hxy.symm)
  have hcardsub := card_le_card hsub
  rcases Nat.even_or_odd (univ.filter fun v => 0 < H0.degree v).card with ⟨m, hm⟩ | ⟨m, hm⟩
  · rw [hm, show (m + m) / 2 = m by omega] at hov
    rw [hm] at h2e
    nlinarith
  · apply h2 (univ.filter fun v => 0 < H0.degree v)
    rw [inducesOverfull_iff]
    refine ⟨⟨m, hm⟩, ?_⟩
    rw [hm, show (2 * m + 1) / 2 = m by omega] at hov
    rw [hm, show 2 * m + 1 - 1 = 2 * m by omega]
    nlinarith

end CDRBicolour.L183
