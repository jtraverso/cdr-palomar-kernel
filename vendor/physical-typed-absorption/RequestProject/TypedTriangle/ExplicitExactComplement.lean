module
public import RequestProject.TypedTriangle.ExplicitBankCore
public import RequestProject.TypedTriangle.ExplicitSparseEdgePayment
public import RequestProject.TypedTriangle.G4SampledReferenceComplement
set_option maxHeartbeats 4000000 -- build option (original: -DmaxHeartbeats=1600000; raised)
set_option maxRecDepth 16384 -- build option (original: -DmaxRecDepth=8192; raised)
@[expose] public section

open Finset Classical
noncomputable section
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false

namespace TypedTriangle.Vortex.Explicit
open BasalIncidence

def complementBudget (C α : ℝ) (h : ℕ) : ℝ :=
  min (ProtectedNibble.Explicit.deletedSeedBudget C α h)
    (min (ExplicitPaid.geometryBudget α h) (ExplicitPaid.latticeBudget α h))

def complementOrder (C α : ℝ) (h : ℕ) : ℕ :=
  max (RawReference.Explicit.seedOrder C)
    (max (ExplicitPaid.geometryOrder α h) (ExplicitPaid.latticeOrder α))

theorem complementBudget_pos {C α : ℝ} (h : ℕ) (hC : 1 ≤ C) (hα : 0 < α) :
    0 < complementBudget C α h :=
  lt_min (ProtectedNibble.Explicit.deletedSeedBudget_pos h hC hα)
    (lt_min (ExplicitPaid.geometryBudget_pos h hα) (ExplicitPaid.latticeBudget_pos h hα))

/-- The same complementary host has exact H1, its own physical lattice, and
the paid geometry; every numerical window is specified before the host. -/
theorem exact_basal_full_complement_explicit {I : Type} (F : Set (Multiset I))
    (C α : ℝ) (h : ℕ) (hC : 1 ≤ C) (hα : 0 < α) (hh : 6 ≤ h)
    {V : Type} [Fintype V] (H : Host V I) (φ : Finset V → ℝ)
    (D : Finset (Finset V)) (d : ℕ)
    (hn : complementOrder C α h ≤ Fintype.card V)
    (hSeed : IsDiffuseSeed H F C φ) (hPhys : IsPhysical H F (edges H))
    (h3 : CommonNbrCond H F α) (h4 : HingeCond H F α h)
    (hD : IsDecomposition H F (cover D) D)
    (hDeg : ∀ v, SparseEdge.degIn (cover D) v ≤ d)
    (hSmall : (d : ℝ) ≤ complementBudget C α h * Fintype.card V) :
    ∃ ψ : Finset V → ℝ,
      IsDiffuseSeed (subHost H (edges H \ cover D)) F (2*C) ψ ∧
      IsPhysical (subHost H (edges H \ cover D)) F
        (edges (subHost H (edges H \ cover D))) ∧
      CommonNbrCond (subHost H (edges H \ cover D)) F (α/2) ∧
      HingeCond (subHost H (edges H \ cover D)) F
        (S07V49.hingeConstB α 1 h) (2*h-3) := by
  have hnS : RawReference.Explicit.seedOrder C ≤ Fintype.card V :=
    (le_max_left _ _).trans hn
  have hnG : ExplicitPaid.geometryOrder α h ≤ Fintype.card V :=
    (le_max_left _ _).trans ((le_max_right _ _).trans hn)
  have hnL : ExplicitPaid.latticeOrder α ≤ Fintype.card V :=
    (le_max_right _ _).trans ((le_max_right _ _).trans hn)
  have hN : (0 : ℝ) ≤ Fintype.card V := Nat.cast_nonneg _
  have hdS : (d : ℝ) ≤ ProtectedNibble.Explicit.deletedSeedBudget C α h *
      Fintype.card V :=
    hSmall.trans (mul_le_mul_of_nonneg_right (min_le_left _ _) hN)
  have hdG : (d : ℝ) ≤ ExplicitPaid.geometryBudget α h * Fintype.card V :=
    hSmall.trans (mul_le_mul_of_nonneg_right
      ((min_le_right _ _).trans (min_le_left _ _)) hN)
  have hdL : (d : ℝ) ≤ ExplicitPaid.latticeBudget α h * Fintype.card V :=
    hSmall.trans (mul_le_mul_of_nonneg_right
      ((min_le_right _ _).trans (min_le_right _ _)) hN)
  have hDE : cover D ⊆ edges H := CorePaid.basal_subset_edges ⟨D,hD⟩
  obtain ⟨ψ,hψ,_⟩ := ProtectedNibble.Explicit.seed_persistence_exact_explicit
    (F:=F) hC hα h H φ (cover D) D d hnS hSeed h4 hDE hD hDeg hdS
  have hLdeg : ∀ v, (((cover D).filter (fun e => v ∈ e)).card : ℝ) ≤
      ExplicitPaid.latticeBudget α h * Fintype.card V := by
    intro v
    exact (by exact_mod_cast hDeg v :
      (((cover D).filter (fun e => v ∈ e)).card : ℝ) ≤ d).trans hdL
  have hAmbient := isPhysical_sdiff hPhys (isPhysical_of_isDecomposition hD) hDE
  have hZero : ∀ e ∈ cover D, SparseEdge.ind (edges H \ cover D) e = 0 := by
    intro e he
    simp [SparseEdge.ind,he]
  have hEntry := (ExplicitPaid.sparse_edge_deletion_host_explicit α h hα V I H F
    hnL h3 h4 (cover D) hLdeg (SparseEdge.ind (edges H \ cover D))).mpr
      ⟨hAmbient,hZero⟩
  have hPhysical : IsPhysical (subHost H (edges H \ cover D)) F
      (edges (subHost H (edges H \ cover D))) := by
    change SparseEdge.ind (edges (subHost H (edges H \ cover D))) ∈ _
    rw [Residual.edges_subHost_eq sdiff_subset]
    exact hEntry
  obtain ⟨h3',h4'⟩ := ExplicitPaid.geometry_after_edge_payment_explicit α h hα hh
    H F (cover D) d hnG h3 h4 hDE hDeg hdG
  exact ⟨ψ,hψ,hPhysical,h3',h4'⟩

theorem exact_complement_after_sampled_reference_explicit {I : Type}
    (F : Set (Multiset I)) (C α : ℝ) (h : ℕ)
    (hC : 1 ≤ C) (hα : 0 < α) (hh : 6 ≤ h)
    {V : Type} [Fintype V] (H : Host V I) (φ : Finset V → ℝ)
    (W : Finset V) (U : Finset (Sym2 V))
    (E₀ : Finset (Sym2 {x // x ∈ W})) (dU : ℕ)
    (hn : complementOrder C α h ≤ Fintype.card V)
    (hSeed : IsDiffuseSeed H F C φ) (hPhys : IsPhysical H F (edges H))
    (h3 : CommonNbrCond H F α) (h4 : HingeCond H F α h)
    (hBasal : Basal H F (U ∪ SampledResource.lift W E₀))
    (hE : E₀ ⊆ edges
      (⟨H.G.comap Subtype.val,H.lab ∘ Subtype.val⟩ : Host {x // x ∈ W} I))
    (hU : ∀ v, SparseEdge.degIn U v ≤ dU)
    (hSmall : ((dU+W.card:ℕ):ℝ) ≤ complementBudget C α h * Fintype.card V) :
    let B := U ∪ SampledResource.lift W E₀
    ∃ ψ : Finset V → ℝ,
      IsDiffuseSeed (subHost H (edges H \ B)) F (2*C) ψ ∧
      IsPhysical (subHost H (edges H \ B)) F (edges (subHost H (edges H \ B))) ∧
      CommonNbrCond (subHost H (edges H \ B)) F (α/2) ∧
      HingeCond (subHost H (edges H \ B)) F
        (S07V49.hingeConstB α 1 h) (2*h-3) := by
  obtain ⟨DB,hDB⟩ := hBasal
  have hCover : cover DB = U ∪ SampledResource.lift W E₀ := hDB.2.2
  have hDegree : ∀ v, SparseEdge.degIn (cover DB) v ≤ dU+W.card := by
    intro v
    rw [hCover]
    exact SampledResource.full_reserved_degree_le H W U E₀ dU hU hE v
  have hDec : IsDecomposition H F (cover DB) DB := by
    simpa only [hCover] using hDB
  have hResult := exact_basal_full_complement_explicit F C α h hC hα hh
    H φ DB (dU+W.card) hn hSeed hPhys h3 h4 hDec hDegree hSmall
  simpa only [hCover] using hResult

end TypedTriangle.Vortex.Explicit

#print axioms TypedTriangle.Vortex.Explicit.exact_basal_full_complement_explicit
#print axioms TypedTriangle.Vortex.Explicit.exact_complement_after_sampled_reference_explicit
