/-
Copyright (c) 2026 Juan Pablo Traverso Gianini.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module
public import RequestProject.TypedTriangle.G34NativePackingOneLayer
public import RequestProject.S07V47.Uniform
set_option maxHeartbeats 4000000 -- build option (original: -DmaxHeartbeats=1600000; raised)
set_option maxRecDepth 16384 -- build option (original: -DmaxRecDepth=8192; raised)
@[expose] public section

/-! Activate the protected bank with the monitors fixed on its actual core.
The local and full moment bounds remain explicit obligations of the caller. -/

open Finset Classical
noncomputable section

namespace TypedTriangle.CatalogNative

open S07V40 S07V42 S07V43 S07V44 S07V46 S07V47

variable {V I : Type*} [Fintype V] {H : SimpleGraph V} {lab : V → I}
  {F : Set (Multiset I)} {W : Finset V} {d c E : ℕ}

theorem activate_actual_protected_bank
    (C0 : CoreCompression H lab F W d c E) (Rc : ℕ)
    (A M K P q Ecell zmax N L : ℕ)
    (Mon : ∀ Z : Finset V, CatalogGen C0 Rc Z → PhysicalMonitors C0 Rc Z A M K)
    (Fm : FullMonitor C0 Rc A M K)
    (hP : P = 2 * gammaL A M L)
    (F0 : Finset (Sym2 V))
    (hBank : MacroBank (protSetting C0 Rc P q Ecell zmax F0) L N)
    (hgen : ∀ j, CatalogGen C0 Rc
      (Zstrat (protSetting C0 Rc P q Ecell zmax F0) N j))
    {eta gamma tau : ℝ} (n : ℕ)
    (hgamma : 0 < gamma) (heta : 0 ≤ eta) (hqn : gamma * n ≤ q)
    (hcapacity : eta *
      ((2 * Ecell * (childSetting C0 Rc P q Ecell zmax).Bstar : ℕ) : ℝ) / gamma ≤ 1)
    (x : MCore H lab F W)
    (hx : clsQ H lab F W (x : Sym2 V → ℤ) ∈ KZ H lab F W ∅)
    (hloc : ∀ ℓ ≤ L,
      (ℓ < L ∨ (protSetting C0 Rc P q Ecell zmax F0).K
        (Zr (protSetting C0 Rc P q Ecell zmax F0) N) = ⊥) →
      ∀ hg : CatalogGen C0 Rc
        (Zstrat (protSetting C0 Rc P q Ecell zmax F0) N (ℓ + 1)),
      (S07V32.l1 (physMon C0
        (Dset C0 Rc (Zstrat (protSetting C0 Rc P q Ecell zmax F0) N (ℓ + 1)))
        (Mon _ hg).psi x) : ℝ) ≤
          eta * n * (Zstrat (protSetting C0 Rc P q Ecell zmax F0) N (ℓ + 1)).card)
    (hfull : (protSetting C0 Rc P q Ecell zmax F0).K
      (Zr (protSetting C0 Rc P q Ecell zmax F0) N) ≠ ⊥ →
      (S07V32.l1 (physMon C0 ∅ Fm.psi x) : ℝ) ≤ tau * n ^ 2)
    (hN : (protSetting C0 Rc P q Ecell zmax F0).K
      (Zr (protSetting C0 Rc P q Ecell zmax F0) N) ≠ ⊥ →
      1 + tau * n ^ 2 ≤ 2 * N) :
    ∃ J ≤ L, ProtOutcome C0 Rc P q Ecell zmax F0 N J x ∧
      ((protSetting C0 Rc P q Ecell zmax F0).K
        (Zr (protSetting C0 Rc P q Ecell zmax F0) N) ≠ ⊥ → J = L) ∧
      ((protSetting C0 Rc P q Ecell zmax F0).K
        (Zr (protSetting C0 Rc P q Ecell zmax F0) N) = ⊥ →
        J + 1 = numStrata (protSetting C0 Rc P q Ecell zmax F0) N ∨
          (numStrata (protSetting C0 Rc P q Ecell zmax F0) N = 0 ∧ J = 0)) := by
  obtain ⟨J, hJ, ⟨coeff, hsup, hshape⟩, hfinish, hearly⟩ :=
    shape_allocation_dichotomy
      (protSetting_shape C0 Rc P q Ecell zmax F0) hBank Mon Fm
      (fun j _ => hgen j) n hgamma heta hqn hcapacity
      (le_of_eq hP.symm) x hx hloc hfull hN
  exact ⟨J, hJ,
    ⟨coeff, hsup, hshape,
      prot_avoids
        (fun X hX => ((protSetting_basal C0 Rc P q Ecell zmax F0 X).1 hX).2)
        hshape⟩,
    hfinish, hearly⟩

end TypedTriangle.CatalogNative

#print axioms TypedTriangle.CatalogNative.activate_actual_protected_bank
