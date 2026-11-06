/-
Copyright (c) 2026 Juan Pablo Traverso Gianini.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module
public import RequestProject.TypedTriangle.CoreForkBridge
public import RequestProject.TypedTriangle.PhysicalSelectorEntry
public import RequestProject.TypedTriangle.SlotPairing
set_option maxHeartbeats 1600000 -- build option (original: -DmaxHeartbeats=1600000)
set_option maxRecDepth 8192 -- build option (original: -DmaxRecDepth=8192)
@[expose] public section

/-! Build forks on the SAME preselected core as the paid selectors. -/
open Finset Classical
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace TypedTriangle.CorePaid
open S07V26
variable {V I : Type*} [Fintype V]

theorem forks_on_core_pool {H : Host V I} {F : Set (Multiset I)}
    (W : Finset V) {κ : ℝ} (hκ : 0 < κ)
    (hpool : ∀ u v : V, u ≠ v → ∀ k : I,
      ({H.lab u,H.lab v,k}:Multiset I) ∈ F →
        κ*Fintype.card V ≤ ((commonNbrs H k u v) ∩ W).card)
    (h2 : IsPhysical H F (edges H))
    (X P : Finset (Sym2 V)) (hXG : X ⊆ edges H) {r b : ℕ}
    (hX : ∀ v, SparseEdge.degIn X v ≤ r) (hP : ∀ v, SparseEdge.degIn P v ≤ b)
    (hr : (r:ℝ) ≤ forkEps κ*Fintype.card V)
    (hb : (b:ℝ) ≤ forkEps κ*Fintype.card V)
    (hn : 32 ≤ κ*Fintype.card V) :
    ∃ fk : Sym2 V → Fork V, ForkSystem H.G H.lab F W X P fk ∧
      ∀ v, SparseEdge.degIn (forkUnion (XZ X W) fk) v ≤ 2*r+forkQ κ r+4 := by
  have hcovG : EdgeCovered H.G H.lab F := H2Phys.edgeCovered h2
  let m := ⌈κ*Fintype.card V⌉₊
  have hpool' : ∀ u v : V, u ≠ v → ∀ k : I,
      ({H.lab u,H.lab v,k}:Multiset I) ∈ F →
        m ≤ ((SparseEdge.commonNbrs H.G H.lab k u v) ∩ W).card := by
    intro u v huv k hk
    exact Nat.ceil_le.mpr (hpool u v huv k hk)
  have hcov : ∀ e ∈ XZ X W, ∃ T,
      SparseEdge.IsAllowed H.G H.lab F T ∧ e ∈ SparseEdge.triEdges T :=
    fun e he => hcovG e (hXG (XZ_subset X W he))
  have hloop : ∀ e ∈ XZ X W, ¬ e.IsDiag := fun e he =>
    SparseEdge.not_isDiag_of_mem_edges (hXG (XZ_subset X W he))
  have hdegXZ : ∀ v, SparseEdge.degIn (XZ X W) v ≤ r := fun v =>
    (S07V26.degIn_mono (XZ_subset X W) v).trans (hX v)
  have hI : 2*((XZ X W).card:ℝ) ≤ Fintype.card V*r := by
    exact_mod_cast two_card_le hloop hdegXZ
  have hwin := fork_window hκ (Nat.cast_nonneg _) hn hr hb hI (Nat.le_ceil _)
  obtain ⟨fk,hFS,hroot,haux,hmax,hunused⟩ :=
    fork_greedy (one_le_forkQ κ r) hpool' hcov hX hP hwin
  exact ⟨fk,hFS,hmax⟩

theorem fork_union_basal {H : Host V I} {F : Set (Multiset I)} {W : Finset V}
    {X P : Finset (Sym2 V)} {fk : Sym2 V → Fork V}
    (hFS : ForkSystem H.G H.lab F W X P fk) :
    Basal H F (forkUnion (XZ X W) fk) := by
  have h := (hFS.fork_modes (I' := ∅) (empty_subset _)).1
  simp only [QU,biUnion_empty,sdiff_empty,union_empty] at h
  exact ⟨_,h⟩

theorem fork_mode_basal {H : Host V I} {F : Set (Multiset I)} {W : Finset V}
    {X P L : Finset (Sym2 V)} {fk : Sym2 V → Fork V}
    (hFS : ForkSystem H.G H.lab F W X P fk) (hL : L ⊆ X) :
    Basal H F ((forkUnion (XZ X W) fk \ QU fk (L ∩ XZ X W)) ∪ (L ∩ XZ X W)) :=
  ⟨_,(hFS.fork_modes inter_subset_right).1⟩

lemma forkQ_linear {κ : ℝ} (hκ : 0 < κ) :
    ∃ D : ℕ, 1 ≤ D ∧ ∀ r, forkQ κ r ≤ D*(r+1) := by
  let D := ⌈128/κ⌉₊+1
  refine ⟨D,by omega,?_⟩
  intro r
  have h1 := forkQ_upper hκ r
  have heq : 128*(r:ℝ)/κ = (128/κ)*r := by ring
  rw [heq] at h1
  have h2 : 128/κ+1 ≤ (D:ℝ) := by dsimp [D]; push_cast; linarith [Nat.le_ceil (128/κ)]
  have h3 := mul_le_mul_of_nonneg_right h2 (show (0:ℝ) ≤ r by positivity)
  have h4 : 0 ≤ 128/κ := by positivity
  have h5 : (forkQ κ r:ℝ) ≤ D*(r+1) := by nlinarith
  exact_mod_cast h5

end TypedTriangle.CorePaid
