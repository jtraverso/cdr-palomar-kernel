module
public import RequestProject.TypedTriangle.ExplicitMonitorPayment
public import RequestProject.S07V46.FullMonitor
public import RequestProject.S07V47.Uniform
set_option maxHeartbeats 4000000 -- build option (original: -DmaxHeartbeats=1600000; raised)
set_option maxRecDepth 16384 -- build option (original: -DmaxRecDepth=8192; raised)
@[expose] public section
open Finset Classical Submodule
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace S07V34.Explicit

theorem monitorMagnitude_pos (d R : ℕ) : 0 < monitorMagnitude d R :=
  lt_of_lt_of_le (by decide : 0 < (1 : ℕ)) (le_max_left _ _)

theorem monitorDimension_pos (d R : ℕ) : 0 < monitorDimension d R := by
  unfold monitorDimension
  positivity

theorem paymentCost_pos (d R : ℕ) : 0 < paymentCost d R :=
  lt_of_lt_of_le (TypedTriangle.GroupingExplicit.kernelBound_pos _ _) (Nat.le_add_right _ _)

#print axioms paymentCost_pos
end S07V34.Explicit
namespace S07V46.Explicit
open TypedTriangle.SparseEdge TypedTriangle.ComponentRows TypedTriangle.Composition
open TypedTriangle.Dispersal S07V42 S07V34 S07V32 S07V44

theorem uniform_monitors_with_full_explicit (d c E R : ℕ) :
    let A := S07V34.Explicit.paymentCost d (monR R E)
    let M := S07V34.Explicit.monitorMagnitude d (monR R E)
    let K := S07V34.Explicit.monitorDimension d (monR R E)
    ∀ {V : Type u} [Fintype V] {I : Type v} {H : SimpleGraph V} {lab : V → I}
      {F : Set (Multiset I)} {W : Finset V} (C0 : CoreCompression H lab F W d c E),
      (∀ Z : Finset V, CatalogGen C0 R Z → Nonempty (PhysicalMonitors C0 R Z A M K)) ∧
      Nonempty (FullMonitor C0 R A M K) := by
  dsimp only
  have h := S07V34.Explicit.uniform_monitor_payment_kmax_explicit d (monR R E)
  intro V _ I H lab F W C0
  have hS : C0.S ⊆ box d (monR R E) := fun s hs => mem_box.2 fun i =>
    (C0.S_bound s hs i).trans (by exact_mod_cast E_le_monR R E)
  refine ⟨fun Z hgen => ?_, ?_⟩
  · have hD : Dset C0 R Z ⊆ box d (monR R E) :=
      (Dset_subset_box C0 R Z).trans (box_mono (R_le_monR R E))
    obtain ⟨psi, hker, hM, hpay⟩ := h C0.S (Dset C0 R Z) hS hD
    exact ⟨PhysicalMonitors.mk' C0 R Z hgen psi hker hM hpay⟩
  · obtain ⟨psi, hker, hM, hpay⟩ := h C0.S ∅ hS (empty_subset _)
    exact ⟨⟨psi, hker, hM, physMon_payment_zero C0 (R_le_monR R E) psi hpay⟩⟩

#print axioms uniform_monitors_with_full_explicit
end S07V46.Explicit
namespace S07V47.Explicit
open TypedTriangle.SparseEdge TypedTriangle.ComponentRows TypedTriangle.Composition
open TypedTriangle.Dispersal S07V42 S07V34 S07V32 S07V44 S07V43 S07V40 S07V46

theorem shape_allocation_constants_explicit (d c E R L : ℕ) :
    let A := S07V34.Explicit.paymentCost d (monR R E)
    let M := S07V34.Explicit.monitorMagnitude d (monR R E)
    let K := S07V34.Explicit.monitorDimension d (monR R E)
    let P := 2 * gammaL A M L
    ∀ {V : Type u} [Fintype V] {I : Type v} {H : SimpleGraph V} {lab : V → I}
      {F : Set (Multiset I)} {W : Finset V} (C0 : CoreCompression H lab F W d c E),
    ∃ (Mon : ∀ Z : Finset V, CatalogGen C0 R Z → PhysicalMonitors C0 R Z A M K)
      (Fm : FullMonitor C0 R A M K),
    ∀ (S : MacroSetting V (ClassQ H lab F W × ℤ) (Cat d R)), ChildShape C0 R S → S.P = P →
    ∀ N : ℕ, MacroBank S L N → (∀ j ≤ L, CatalogGen C0 R (Zstrat S N j)) →
    ∀ {eta gamma tau : ℝ} (n : ℕ), 0 < gamma → 0 ≤ eta → gamma * n ≤ S.q →
      eta * ((2 * S.E * S.Bstar : ℕ) : ℝ) / gamma ≤ 1 →
    ∀ x : MCore H lab F W, clsQ H lab F W (x : Sym2 V → ℤ) ∈ KZ H lab F W ∅ →
      (∀ ℓ ≤ L, (ℓ < L ∨ S.K (Zr S N) = ⊥) →
        ∀ hg : CatalogGen C0 R (Zstrat S N (ℓ + 1)),
        (l1 (physMon C0 (Dset C0 R (Zstrat S N (ℓ + 1))) (Mon _ hg).psi x) : ℝ) ≤
          eta * n * (Zstrat S N (ℓ + 1)).card) →
      (S.K (Zr S N) ≠ ⊥ → (l1 (physMon C0 ∅ Fm.psi x) : ℝ) ≤ tau * n ^ 2) →
      (S.K (Zr S N) ≠ ⊥ → 1 + tau * n ^ 2 ≤ 2 * N) →
      ∃ J ≤ L, ShapeOutcome C0 R S N J x ∧ (S.K (Zr S N) ≠ ⊥ → J = L) ∧
        (S.K (Zr S N) = ⊥ → J + 1 = numStrata S N ∨ (numStrata S N = 0 ∧ J = 0)) := by
  dsimp only
  let A := S07V34.Explicit.paymentCost d (monR R E)
  let M := S07V34.Explicit.monitorMagnitude d (monR R E)
  let K := S07V34.Explicit.monitorDimension d (monR R E)

  intro V _ I H lab F W C0
  obtain ⟨Mon⟩ : Nonempty (∀ Z : Finset V, CatalogGen C0 R Z → PhysicalMonitors C0 R Z A M K) :=
    ⟨fun Z h => Classical.choice ((S07V46.Explicit.uniform_monitors_with_full_explicit d c E R C0).1 Z h)⟩
  obtain ⟨Fm⟩ := (S07V46.Explicit.uniform_monitors_with_full_explicit d c E R C0).2
  refine ⟨Mon, Fm, ?_⟩
  intro S hS hPS N hM hgen eta gamma tau n hγ hη hqn hθ x hx hloc hfull hN
  exact shape_allocation_dichotomy hS hM Mon Fm hgen n hγ hη hqn hθ (le_of_eq hPS.symm) x hx hloc
    hfull hN

theorem protSetting_allocation_constants_explicit (d c E R L : ℕ) :
    let A := S07V34.Explicit.paymentCost d (monR R E)
    let M := S07V34.Explicit.monitorMagnitude d (monR R E)
    let K := S07V34.Explicit.monitorDimension d (monR R E)
    let P := 2 * gammaL A M L
    ∀ {V : Type u} [Fintype V] {I : Type v} {H : SimpleGraph V} {lab : V → I}
      {F : Set (Multiset I)} {W : Finset V} (C0 : CoreCompression H lab F W d c E),
    ∃ (Mon : ∀ Z : Finset V, CatalogGen C0 R Z → PhysicalMonitors C0 R Z A M K)
      (Fm : FullMonitor C0 R A M K),
    ∀ (q Ecell zmax : ℕ) (F0 : Finset (Sym2 V)) (N : ℕ),
    MacroBank (protSetting C0 R P q Ecell zmax F0) L N →
    (∀ j ≤ L, CatalogGen C0 R (Zstrat (protSetting C0 R P q Ecell zmax F0) N j)) →
    ∀ {eta gamma tau : ℝ} (n : ℕ), 0 < gamma → 0 ≤ eta → gamma * n ≤ q →
      eta * ((2 * Ecell * (childSetting C0 R P q Ecell zmax).Bstar : ℕ) : ℝ) / gamma ≤ 1 →
    ∀ x : MCore H lab F W, clsQ H lab F W (x : Sym2 V → ℤ) ∈ KZ H lab F W ∅ →
      (∀ ℓ ≤ L, (ℓ < L ∨ (protSetting C0 R P q Ecell zmax F0).K
          (Zr (protSetting C0 R P q Ecell zmax F0) N) = ⊥) →
        ∀ hg : CatalogGen C0 R (Zstrat (protSetting C0 R P q Ecell zmax F0) N (ℓ + 1)),
        (l1 (physMon C0 (Dset C0 R (Zstrat (protSetting C0 R P q Ecell zmax F0) N (ℓ + 1)))
          (Mon _ hg).psi x) : ℝ) ≤
          eta * n * (Zstrat (protSetting C0 R P q Ecell zmax F0) N (ℓ + 1)).card) →
      ((protSetting C0 R P q Ecell zmax F0).K (Zr (protSetting C0 R P q Ecell zmax F0) N) ≠ ⊥ →
        (l1 (physMon C0 ∅ Fm.psi x) : ℝ) ≤ tau * n ^ 2) →
      ((protSetting C0 R P q Ecell zmax F0).K (Zr (protSetting C0 R P q Ecell zmax F0) N) ≠ ⊥ →
        1 + tau * n ^ 2 ≤ 2 * N) →
      ∃ J ≤ L, ProtOutcome C0 R P q Ecell zmax F0 N J x ∧
        ((protSetting C0 R P q Ecell zmax F0).K (Zr (protSetting C0 R P q Ecell zmax F0) N) ≠ ⊥ →
          J = L) ∧
        ((protSetting C0 R P q Ecell zmax F0).K (Zr (protSetting C0 R P q Ecell zmax F0) N) = ⊥ →
          J + 1 = numStrata (protSetting C0 R P q Ecell zmax F0) N ∨
            (numStrata (protSetting C0 R P q Ecell zmax F0) N = 0 ∧ J = 0)) := by
  dsimp only
  let A := S07V34.Explicit.paymentCost d (monR R E)
  let M := S07V34.Explicit.monitorMagnitude d (monR R E)
  let K := S07V34.Explicit.monitorDimension d (monR R E)
  let P := 2 * gammaL A M L
  intro V _ I H lab F W C0
  obtain ⟨Mon, Fm, h⟩ := shape_allocation_constants_explicit d c E R L C0
  refine ⟨Mon, Fm, ?_⟩
  intro q Ecell zmax F0 N hM hgen eta gamma tau n hγ hη hqn hθ x hx hloc hfull hN
  obtain ⟨J, hJ, ⟨z, hs, hz⟩, h1, h2⟩ := h (protSetting C0 R P q Ecell zmax F0)
    (protSetting_shape C0 R P q Ecell zmax F0) rfl N hM hgen n hγ hη hqn hθ x hx hloc hfull hN
  exact ⟨J, hJ, ⟨z, hs, hz, prot_avoids (fun X hX => ((protSetting_basal C0 R P q Ecell zmax F0 X).1 hX).2) hz⟩, h1, h2⟩

#print axioms shape_allocation_constants_explicit
#print axioms protSetting_allocation_constants_explicit
end S07V47.Explicit
