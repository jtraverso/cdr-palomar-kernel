/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module
public import RequestProject.S07V49.HingeCountB
public import RequestProject.TypedTriangle.G4GraphDeleteAdapter
set_option maxHeartbeats 4000000 -- build option (original: -DmaxHeartbeats=1600000; raised)
set_option maxRecDepth 16384 -- build option (original: -DmaxRecDepth=8192; raised)

@[expose] public section

/-! Direct H4 persistence under sparse edge deletion, with no seed on the
input host. The S07V49 edge hinge count is used at q=1 and U=univ. -/

open Finset Classical
noncomputable section

namespace TypedTriangle.Vortex

theorem hinge_after_edge_deletion_no_seed {V I : Type*} [Fintype V]
    (H : Host V I) (F : Set (Multiset I)) (α : ℝ) (h : ℕ)
    (hα : 0 < α) (hh : 6 ≤ h)
    (hH3 : CommonNbrCond H F α) (hH4 : HingeCond H F α h)
    (B : SimpleGraph V) [DecidableRel B.Adj] (d : ℕ)
    (hB : ∀ x, B.degree x ≤ d)
    (hw1 : 2 + 4 * (d : ℝ) ≤ α * Fintype.card V / 8)
    (hw2 : (5 * (d : ℝ) + h + 1) * 2 ^ (h.choose 2) ≤
      α * Fintype.card V / 8) :
    HingeCond (⟨H.G \ B, H.lab⟩ : Host V I) F
      (S07V49.hingeConstB α 1 h) (2*h-3) := by
  have h4s : SparseEdge.HingeCond H.G H.lab F α h :=
    (hingeCond_iff_sparseEdge H F α h).mp hH4
  have hhinge : ∀ u v a b : V,
      S07V24.HingeTest H.G H.lab F u v a b →
      α * (1 : ℝ) ^ (S07V24.hOrd h4s u v a b - 4) *
        (Fintype.card V : ℝ) ^ (S07V24.hOrd h4s u v a b - 4) / 4 ≤
      ((SparseEdge.hinges H.G H.lab F u v a b
        (S07V24.hOrd h4s u v a b)).filter
          (fun J => S07V24.freeV u v a b J ⊆ (univ : Finset V))).card := by
    intro u v a b ht
    have hc := (S07V24.hOrd_spec h4s ht).2.2
    simp only [one_pow, mul_one]
    have hf : (SparseEdge.hinges H.G H.lab F u v a b
        (S07V24.hOrd h4s u v a b)).filter
          (fun J => S07V24.freeV u v a b J ⊆ (univ : Finset V)) =
        SparseEdge.hinges H.G H.lab F u v a b
          (S07V24.hOrd h4s u v a b) := by simp
    rw [hf]
    have hn : (0 : ℝ) ≤ (Fintype.card V : ℝ) ^
        (S07V24.hOrd h4s u v a b - 4) := by positivity
    nlinarith
  have hpool : ∀ u v : V, u ≠ v → ∀ k : I,
      ({H.lab u, H.lab v, k} : Multiset I) ∈ F →
      (1:ℝ) * α * Fintype.card V / 4 ≤
        ((SparseEdge.commonNbrs H.G H.lab k u v) ∩
          (univ : Finset V)).card := by
    intro u v huv k hk
    have hc := hH3 u v huv k hk
    have hc' : α * Fintype.card V ≤
        (SparseEdge.commonNbrs H.G H.lab k u v).card := hc
    simpa only [one_mul, Finset.inter_univ] using
      (show α * Fintype.card V / 4 ≤
          (SparseEdge.commonNbrs H.G H.lab k u v).card from by
        have hn : (0:ℝ) ≤ α * Fintype.card V := by positivity
        nlinarith [hc'])
  intro u v a b hab hTa hTb
  have ht : S07V24.HingeTest (H.G \ B) H.lab F u v a b := ⟨hab,hTa,hTb⟩
  obtain ⟨i,hi9,hiMax,hiCount⟩ :=
    S07V49.edge_hinge_count hα (by norm_num : (0:ℝ)<1)
      (by norm_num : (1:ℝ)≤1) hh h4s hhinge hpool B d hB
      (by simpa only [one_mul] using hw1)
      (by simpa only [one_pow, mul_one] using hw2) ht
  refine ⟨i,by omega,hiMax,?_⟩
  change S07V49.hingeConstB α 1 h * (Fintype.card V:ℝ) ^ (i-4) ≤
    (SparseEdge.hinges (H.G\B) H.lab F u v a b i).card
  exact hiCount.trans (by exact_mod_cast (Finset.card_filter_le _ _))

#print axioms hinge_after_edge_deletion_no_seed

/-- The same no-seed hinge transfer in the edge-set interface used by the
actual paid child.  No physicality or fractional H1 premise enters this step. -/
theorem hinge_after_edge_set_deletion_no_seed {V I : Type*} [Fintype V]
    (H : Host V I) (F : Set (Multiset I)) (α : ℝ) (h : ℕ)
    (hα : 0 < α) (hh : 6 ≤ h)
    (hH3 : CommonNbrCond H F α) (hH4 : HingeCond H F α h)
    (C : Finset (Sym2 V)) (d : ℕ)
    (hCE : C ⊆ edges H) (hDeg : ∀ v, SparseEdge.degIn C v ≤ d)
    (hw1 : 2 + 4 * (d : ℝ) ≤ α * Fintype.card V / 8)
    (hw2 : (5 * (d : ℝ) + h + 1) * 2 ^ (h.choose 2) ≤
      α * Fintype.card V / 8) :
    HingeCond (subHost H (edges H \ C)) F
      (S07V49.hingeConstB α 1 h) (2*h-3) := by
  let B := SimpleGraph.fromEdgeSet (C : Set (Sym2 V))
  letI : DecidableRel B.Adj := Classical.decRel _
  have hDiag : ∀ e ∈ C, ¬e.IsDiag := TypedTriangle.CorePaid.edges_diagonal_free hCE
  have hBDeg : ∀ v, B.degree v ≤ d := by
    intro v
    rw [← SimpleGraph.card_incidenceFinset_eq_degree,
      SimpleGraph.incidenceFinset_eq_filter, TypedTriangle.CorePaid.edgeFinset_fromEdges C hDiag]
    exact hDeg v
  have h' := hinge_after_edge_deletion_no_seed H F α h hα hh hH3 hH4 B d hBDeg hw1 hw2
  rw [TypedTriangle.StockEntry.g4_graph_sdiff_eq_subHost H C] at h'
  simpa only [subHost] using h'

#print axioms hinge_after_edge_set_deletion_no_seed

/-- A uniform sparse-deletion window for H4 on the actual paid child.  The
constants depend only on the original H3/H4 parameters, not on a seed. -/
theorem hinge_after_edge_set_deletion_no_seed_uniform (α : ℝ) (h : ℕ)
    (hα : 0 < α) (hh : 6 ≤ h) :
    ∃ η : ℝ, 0 < η ∧ ∃ n₀ : ℕ,
      ∀ {V I : Type*} [Fintype V] (H : Host V I) (F : Set (Multiset I)),
        n₀ ≤ Fintype.card V →
        CommonNbrCond H F α → HingeCond H F α h →
        ∀ (C : Finset (Sym2 V)) (d : ℕ), C ⊆ edges H →
          (∀ v, SparseEdge.degIn C v ≤ d) →
          (d : ℝ) ≤ η * Fintype.card V →
          HingeCond (subHost H (edges H \ C)) F
            (S07V49.hingeConstB α 1 h) (2*h-3) := by
  let M : ℝ := 2 ^ (h.choose 2)
  have hM : 1 ≤ M := by dsimp [M]; exact one_le_pow₀ (by norm_num)
  let η : ℝ := α / (64*M)
  have hη : 0 < η := by dsimp [η]; positivity
  let n₀ : ℕ := ⌈128*(h+2)*M/α⌉₊ + 1
  refine ⟨η,hη,n₀,?_⟩
  intro V I _ H F hn hH3 hH4 C d hCE hDeg hd
  let n : ℝ := Fintype.card V
  have hnLower : 128*(h+2)*M/α < n := by
    have hc : 128*(h+2)*M/α ≤ (⌈128*(h+2)*M/α⌉₊ : ℝ) :=
      Nat.le_ceil _
    have hn' : (n₀ : ℝ) ≤ n := by
      have hc : (n₀ : ℝ) ≤ (Fintype.card V : ℝ) := by exact_mod_cast hn
      simpa only [n] using hc
    dsimp [n₀] at hn'
    push_cast at hn'
    linarith
  have hnPos : 0 < n := by
    have hlow : 0 ≤ 128*(h+2)*M/α := by positivity
    linarith
  have hlarge : 128*(h+2)*M < α*n := by
    have := (div_lt_iff₀ hα).mp hnLower
    nlinarith
  have hd' : (d : ℝ) ≤ α*n/(64*M) := by
    calc
      (d : ℝ) ≤ α/(64*M)*n := by simpa only [η,n] using hd
      _ = α*n/(64*M) := by ring
  have hMpos : 0 < M := lt_of_lt_of_le (by norm_num) hM
  have hdn : 64*M*(d : ℝ) ≤ α*n := by
    apply (le_div_iff₀ (by positivity : 0 < 64*M)).mp at hd'
    nlinarith [hd']
  have hw1 : 2 + 4*(d : ℝ) ≤ α*n/8 := by
    have hbase : 32 ≤ α*n := by nlinarith [hlarge,hM]
    nlinarith [mul_nonneg (show (0:ℝ) ≤ 64*M-64 by nlinarith [hM])
      (show (0:ℝ) ≤ (d:ℝ) by positivity)]
  have hw2 : (5*(d : ℝ) + h + 1)*2^(h.choose 2) ≤ α*n/8 := by
    change (5*(d : ℝ) + h + 1)*M ≤ α*n/8
    nlinarith [hlarge,hdn]
  exact hinge_after_edge_set_deletion_no_seed H F α h hα hh hH3 hH4 C d
    hCE hDeg (by simpa only [n] using hw1) (by simpa only [n] using hw2)

#print axioms hinge_after_edge_set_deletion_no_seed_uniform

end TypedTriangle.Vortex
