/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module
public import RequestProject.S07V47.Branches
set_option maxHeartbeats 4000000 -- build option (original: -DmaxHeartbeats=1600000; raised)
set_option maxRecDepth 16384 -- build option (original: -DmaxRecDepth=8192; raised)
@[expose] public section

/-!
# V47 §5 — constants fixed BEFORE the host, for the protected bank with early stopping

`shape_allocation_constants d c E R L` : `A, M, K` (V34/V44 monitors on the bounded presentation
`box d (monR R E)`) and `P = 2 · gammaL A M L` are fixed from `(d, c, E, R, L)` only.  Then, for
every host and core compression, ONE family of localized monitors and ONE full monitor are fixed,
and for EVERY setting of child shape with `P` colours (in particular every protected setting),
every bank and every charge, the dichotomy of §4 holds.  The hypotheses on the charge are
* the localized bounds `η n |Zstrat (ℓ+1)|` (for `ℓ < L`, and at the final stratum set in the
  early-stop case), and
* the full bound `τ n²` and `1 + τ n² ≤ 2N` ONLY when the final subgroup is nonzero.

No host-dependent constant appears, and no H1–H4 hypothesis is used or strengthened here.

`protSetting_allocation_constants` specializes this to `protSetting C0 R P q Ecell zmax F0` and adds
the avoidance of `F0` (`prot_avoids`).  For the protected bank the chain bound is
`L = card (Cat d R)` (`protSetting_chainBound`, the V43 bound verbatim).
-/

open Finset Classical Submodule

noncomputable section

namespace S07V47

open TypedTriangle.SparseEdge TypedTriangle.ComponentRows TypedTriangle.Composition
open TypedTriangle.Dispersal S07V42 S07V34 S07V32 S07V44 S07V43 S07V40 S07V46

universe u v

/-- **constants before the host; dichotomy for every child-shaped (protected) bank** -/
theorem shape_allocation_constants (d c E R L : ℕ) :
    ∃ A M K P : ℕ, P = 2 * gammaL A M L ∧
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
  obtain ⟨A, M, K, hU⟩ := uniform_monitors_with_full.{u, v} d c E R
  refine ⟨A, M, K, 2 * gammaL A M L, rfl, ?_⟩
  intro V _ I H lab F W C0
  obtain ⟨Mon⟩ : Nonempty (∀ Z : Finset V, CatalogGen C0 R Z → PhysicalMonitors C0 R Z A M K) :=
    ⟨fun Z h => Classical.choice ((hU C0).1 Z h)⟩
  obtain ⟨Fm⟩ := (hU C0).2
  refine ⟨Mon, Fm, ?_⟩
  intro S hS hPS N hM hgen eta gamma tau n hγ hη hqn hθ x hx hloc hfull hN
  exact shape_allocation_dichotomy hS hM Mon Fm hgen n hγ hη hqn hθ (le_of_eq hPS.symm) x hx hloc
    hfull hN

/-- the outcome in the protected bank: the V46/V47 outcome plus avoidance of `F0` -/
def ProtOutcome {V I : Type*} [Fintype V] {H : SimpleGraph V} {lab : V → I}
    {F : Set (Multiset I)} {W : Finset V} {d c E : ℕ} (C0 : CoreCompression H lab F W d c E)
    (R P q Ecell zmax : ℕ) (F0 : Finset (Sym2 V)) (N J : ℕ) (x : MCore H lab F W) : Prop :=
  ∃ (z : ℕ → Fin P → Cat d R → ℤ)
    (hs : ∀ i, (stratBank (protSetting C0 R P q Ecell zmax F0) N i).Supplies (z i)),
    ShapeProps C0 R (protSetting C0 R P q Ecell zmax F0) N J x z hs ∧
    Disjoint ((range (J + 1)).biUnion fun i =>
      (stratBank (protSetting C0 R P q Ecell zmax F0) N i).total) F0 ∧
    Disjoint ((range (J + 1)).biUnion fun i => Bank.payload (hs i)) F0 ∧
    Disjoint ((range (J + 1)).biUnion fun i => Bank.cover (hs i)) F0

/-- **the protected bank: constants before the host, early-stop dichotomy, avoidance of `F0`** -/
theorem protSetting_allocation_constants (d c E R L : ℕ) :
    ∃ A M K P : ℕ, P = 2 * gammaL A M L ∧
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
  obtain ⟨A, M, K, P, hP, hU⟩ := shape_allocation_constants.{u, v} d c E R L
  refine ⟨A, M, K, P, hP, ?_⟩
  intro V _ I H lab F W C0
  obtain ⟨Mon, Fm, h⟩ := hU C0
  refine ⟨Mon, Fm, ?_⟩
  intro q Ecell zmax F0 N hM hgen eta gamma tau n hγ hη hqn hθ x hx hloc hfull hN
  obtain ⟨J, hJ, ⟨z, hs, hz⟩, h1, h2⟩ := h (protSetting C0 R P q Ecell zmax F0)
    (protSetting_shape C0 R P q Ecell zmax F0) rfl N hM hgen n hγ hη hqn hθ x hx hloc hfull hN
  exact ⟨J, hJ, ⟨z, hs, hz, prot_avoids (fun X hX => ((protSetting_basal C0 R P q Ecell zmax F0 X).1 hX).2) hz⟩, h1, h2⟩

end S07V47
