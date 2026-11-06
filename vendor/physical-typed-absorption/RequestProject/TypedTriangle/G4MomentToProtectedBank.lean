/-
Copyright (c) 2026 Juan Pablo Traverso Gianini.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module
public import RequestProject.TypedTriangle.G4ActualBankActivation
public import RequestProject.TypedTriangle.FullPhysicalMonitorWeights
public import RequestProject.TypedTriangle.G4UniformMonitorCap
set_option maxHeartbeats 4000000 -- build option (original: -DmaxHeartbeats=1600000; raised)
set_option maxRecDepth 16384 -- build option (original: -DmaxRecDepth=8192; raised)
@[expose] public section

/-! Converts moments of the actual positive residual into the integer
physical-monitor bounds required by the protected bank. The weights must be
obtained from the native localization theorem on the actual strata. -/

open Finset Classical
noncomputable section

namespace TypedTriangle.CatalogNative

open S07V40 S07V42 S07V43 S07V44 S07V46 S07V47
open TypedTriangle.LocalizedCover

variable {V I : Type*} [Fintype V] {H : SimpleGraph V} {lab : V → I}
  {F : Set (Multiset I)} {W : Finset V} {d c E : ℕ}

theorem activate_actual_bank_of_physical_moments
    (C0 : CoreCompression H lab F W d c E) (Rc : ℕ)
    (A M K P q Ecell zmax N L : ℕ)
    (Mon : ∀ Z : Finset V, CatalogGen C0 Rc Z → PhysicalMonitors C0 Rc Z A M K)
    (Fm : FullMonitor C0 Rc A M K)
    (hP : P = 2 * gammaL A M L)
    (F0 Y : Finset (Sym2 V))
    (hBank : MacroBank (protSetting C0 Rc P q Ecell zmax F0) L N)
    (hgen : ∀ j, CatalogGen C0 Rc
      (Zstrat (protSetting C0 Rc P q Ecell zmax F0) N j))
    {eta gamma : ℝ} (n : ℕ)
    (hgamma : 0 < gamma) (heta : 0 ≤ eta) (hqn : gamma * n ≤ q)
    (hcapacity : eta *
      ((2 * Ecell * (childSetting C0 Rc P q Ecell zmax).Bstar : ℕ) : ℝ) / gamma ≤ 1)
    (x : MCore H lab F W) (hxY : (x : Sym2 V → ℤ) = ind Y)
    (hx : clsQ H lab F W (x : Sym2 V → ℤ) ∈ KZ H lab F W ∅)
    (loc : ℕ → Fin K → Sym2 V → ℝ) (full : Fin K → Sym2 V → ℝ)
    (hLocRep : ∀ ℓ (hg : CatalogGen C0 Rc
      (Zstrat (protSetting C0 Rc P q Ecell zmax F0) N (ℓ + 1))) j,
      ∑ e, loc ℓ j e * ((x.1 e : ℤ) : ℝ) =
        physMonReal C0
          (Dset C0 Rc (Zstrat (protSetting C0 Rc P q Ecell zmax F0) N (ℓ + 1)))
          (Mon _ hg).psi j x)
    (hFullRep : ∀ j, ∑ e, full j e * ((x.1 e : ℤ) : ℝ) =
      physMonReal C0 ∅ Fm.psi j x)
    (B : ℝ) (hKB : (K : ℝ) * B ≤ eta)
    (hLocMom : ∀ ℓ ≤ L, ∀ j,
      |edgeSum (loc ℓ j) Y| ≤ B * n *
        (Zstrat (protSetting C0 Rc P q Ecell zmax F0) N (ℓ + 1)).card)
    (hFullMom : ∀ j, |edgeSum (full j) Y| ≤ B * n ^ 2)
    (hN : (protSetting C0 Rc P q Ecell zmax F0).K
      (Zr (protSetting C0 Rc P q Ecell zmax F0) N) ≠ ⊥ →
      1 + eta * n ^ 2 ≤ 2 * N) :
    ∃ J ≤ L, ProtOutcome C0 Rc P q Ecell zmax F0 N J x ∧
      ((protSetting C0 Rc P q Ecell zmax F0).K
        (Zr (protSetting C0 Rc P q Ecell zmax F0) N) ≠ ⊥ → J = L) ∧
      ((protSetting C0 Rc P q Ecell zmax F0).K
        (Zr (protSetting C0 Rc P q Ecell zmax F0) N) = ⊥ →
        J + 1 = numStrata (protSetting C0 Rc P q Ecell zmax F0) N ∨
          (numStrata (protSetting C0 Rc P q Ecell zmax F0) N = 0 ∧ J = 0)) := by
  have hloc : ∀ ℓ ≤ L,
      (ℓ < L ∨ (protSetting C0 Rc P q Ecell zmax F0).K
        (Zr (protSetting C0 Rc P q Ecell zmax F0) N) = ⊥) →
      ∀ hg : CatalogGen C0 Rc
        (Zstrat (protSetting C0 Rc P q Ecell zmax F0) N (ℓ + 1)),
      (S07V32.l1 (physMon C0
        (Dset C0 Rc (Zstrat (protSetting C0 Rc P q Ecell zmax F0) N (ℓ + 1)))
        (Mon _ hg).psi x) : ℝ) ≤
          eta * n * (Zstrat (protSetting C0 Rc P q Ecell zmax F0) N (ℓ + 1)).card := by
    intro ℓ hℓ _ hg
    have hh := physical_monitor_norm_of_edge_moments (Mon _ hg) x Y hxY
      (loc ℓ) (hLocRep ℓ hg) (B * n *
        (Zstrat (protSetting C0 Rc P q Ecell zmax F0) N (ℓ + 1)).card)
      (hLocMom ℓ hℓ)
    have hfactor : (0 : ℝ) ≤ n *
        (Zstrat (protSetting C0 Rc P q Ecell zmax F0) N (ℓ + 1)).card := by
      positivity
    have hscaled := mul_le_mul_of_nonneg_right hKB hfactor
    have hscaled' : (K : ℝ) * (B * n *
        (Zstrat (protSetting C0 Rc P q Ecell zmax F0) N (ℓ + 1)).card) ≤
        eta * (n * (Zstrat (protSetting C0 Rc P q Ecell zmax F0) N (ℓ + 1)).card) := by
      convert hscaled using 1 <;> ring
    convert hh.trans hscaled' using 1 <;> ring
  have hfull : (protSetting C0 Rc P q Ecell zmax F0).K
      (Zr (protSetting C0 Rc P q Ecell zmax F0) N) ≠ ⊥ →
      (S07V32.l1 (physMon C0 ∅ Fm.psi x) : ℝ) ≤ eta * n ^ 2 := by
    intro _
    have hh := full_monitor_norm_of_edge_moments C0 Fm x Y hxY full
      hFullRep (B * n ^ 2) hFullMom
    have hfactor : (0 : ℝ) ≤ (n : ℝ) ^ 2 := by positivity
    have hscaled := mul_le_mul_of_nonneg_right hKB hfactor
    have hscaled' : (K : ℝ) * (B * n ^ 2) ≤ eta * n ^ 2 := by
      convert hscaled using 1 <;> ring
    exact hh.trans hscaled'
  exact activate_actual_protected_bank C0 Rc A M K P q Ecell zmax N L Mon Fm
    hP F0 hBank hgen n hgamma heta hqn hcapacity x hx hloc hfull hN

end TypedTriangle.CatalogNative

#print axioms TypedTriangle.CatalogNative.activate_actual_bank_of_physical_moments
