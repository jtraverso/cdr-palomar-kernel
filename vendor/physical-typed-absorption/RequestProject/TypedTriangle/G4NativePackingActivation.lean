/-
Copyright (c) 2026 Juan Pablo Traverso Gianini.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module
public import RequestProject.TypedTriangle.G4MomentToProtectedBank
public import RequestProject.TypedTriangle.G4ActualMomentCap
set_option maxHeartbeats 4000000 -- build option (original: -DmaxHeartbeats=1600000; raised)
set_option maxRecDepth 16384 -- build option (original: -DmaxRecDepth=8192; raised)
@[expose] public section

/-! Convert the moments of one actual positive packing residue into the
physical-monitor capacity of the bank built for that same residue. -/

open Finset Classical
noncomputable section
set_option maxHeartbeats 1600000

namespace TypedTriangle.CatalogNative

open S07V40 S07V42 S07V43 S07V44 S07V46 S07V47
open TypedTriangle.LocalizedCover

variable {V I : Type*} [Fintype V] {H : SimpleGraph V} {lab : V → I}
  {F : Set (Multiset I)} {W : Finset V} {d c E : ℕ}

theorem activate_bank_from_native_packing_moments
    (C0 : CoreCompression H lab F W d c E) (Rc : ℕ)
    (A M K P q Ecell zmax N L : ℕ)
    (Mon : ∀ Z : Finset V, CatalogGen C0 Rc Z →
      PhysicalMonitors C0 Rc Z A M K)
    (Fm : FullMonitor C0 Rc A M K)
    (hP : P = 2 * gammaL A M L)
    (F0 Y : Finset (Sym2 V))
    (hBank : MacroBank (protSetting C0 Rc P q Ecell zmax F0) L N)
    (hgen : ∀ j, CatalogGen C0 Rc
      (Zstrat (protSetting C0 Rc P q Ecell zmax F0) N j))
    (n : ℕ) (Λ η γ ηPack τ ρ τSel load : ℝ)
    (hΛ : 0 ≤ Λ) (hη : 0 ≤ η) (hγ : 0 < γ)
    (hqn : γ * n ≤ q)
    (hcapacity : η *
      ((2 * Ecell * (childSetting C0 Rc P q Ecell zmax).Bstar : ℕ) : ℝ) / γ ≤ 1)
    (hload : load ≤ ηPack * n)
    (hKB : (K : ℝ) *
      (τ + (3 * Λ / 2) * (ηPack + 2 * ρ + 2 * τSel)) ≤ η)
    (x : MCore H lab F W) (hxY : (x : Sym2 V → ℤ) = ind Y)
    (hx : clsQ H lab F W (x : Sym2 V → ℤ) ∈ KZ H lab F W ∅)
    (loc : ℕ → Fin K → Sym2 V → ℝ)
    (full : Fin K → Sym2 V → ℝ)
    (hLocRep : ∀ ℓ (hg : CatalogGen C0 Rc
      (Zstrat (protSetting C0 Rc P q Ecell zmax F0) N (ℓ + 1))) j,
      ∑ e, loc ℓ j e * ((x.1 e : ℤ) : ℝ) =
        physMonReal C0
          (Dset C0 Rc (Zstrat
            (protSetting C0 Rc P q Ecell zmax F0) N (ℓ + 1)))
          (Mon _ hg).psi j x)
    (hFullRep : ∀ j, ∑ e, full j e * ((x.1 e : ℤ) : ℝ) =
      physMonReal C0 ∅ Fm.psi j x)
    (hLocMom : ∀ ℓ ≤ L, ∀ j,
      |edgeSum (loc ℓ j) Y| ≤
        τ * n * (Zstrat
          (protSetting C0 Rc P q Ecell zmax F0) N (ℓ + 1)).card +
        (3 * Λ * (Zstrat
          (protSetting C0 Rc P q Ecell zmax F0) N (ℓ + 1)).card) *
          (load + ρ * n + 2 * (τSel * n) + ρ * n) / 2)
    (hFullMom : ∀ j, |edgeSum (full j) Y| ≤
      τ * (n : ℝ) ^ 2 + (3 * Λ * n) *
        (load + ρ * n + 2 * (τSel * n) + ρ * n) / 2)
    (hN : (protSetting C0 Rc P q Ecell zmax F0).K
      (Zr (protSetting C0 Rc P q Ecell zmax F0) N) ≠ ⊥ →
      1 + η * n ^ 2 ≤ 2 * N) :
    ∃ J ≤ L, ProtOutcome C0 Rc P q Ecell zmax F0 N J x ∧
      ((protSetting C0 Rc P q Ecell zmax F0).K
        (Zr (protSetting C0 Rc P q Ecell zmax F0) N) ≠ ⊥ → J = L) ∧
      ((protSetting C0 Rc P q Ecell zmax F0).K
        (Zr (protSetting C0 Rc P q Ecell zmax F0) N) = ⊥ →
        J + 1 = numStrata (protSetting C0 Rc P q Ecell zmax F0) N ∨
          (numStrata (protSetting C0 Rc P q Ecell zmax F0) N = 0 ∧ J = 0)) := by
  let B := τ + (3 * Λ / 2) * (ηPack + 2 * ρ + 2 * τSel)
  have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg _
  have hloc : ∀ ℓ ≤ L, ∀ j,
      |edgeSum (loc ℓ j) Y| ≤ B * n *
        (Zstrat (protSetting C0 Rc P q Ecell zmax F0) N (ℓ + 1)).card := by
    intro ℓ hℓ j
    exact (hLocMom ℓ hℓ j).trans
      (TypedTriangle.StockEntry.actual_moment_factor_bound Λ n
        (Zstrat (protSetting C0 Rc P q Ecell zmax F0) N (ℓ + 1)).card
        τ ηPack ρ τSel load hΛ (by positivity) hload)
  have hfull : ∀ j, |edgeSum (full j) Y| ≤ B * n ^ 2 := by
    intro j
    have hh := TypedTriangle.StockEntry.actual_moment_factor_bound Λ n n
      τ ηPack ρ τSel load hΛ hn hload
    have hh' : τ * (n : ℝ) ^ 2 + (3 * Λ * n) *
        (load + ρ * n + 2 * (τSel * n) + ρ * n) / 2 ≤ B * n ^ 2 := by
      convert hh using 1 <;> ring
    have hbound := (hFullMom j).trans hh'
    exact hbound
  exact activate_actual_bank_of_physical_moments C0 Rc A M K P q Ecell zmax N L
    Mon Fm hP F0 Y hBank hgen (eta := η) (gamma := γ) n hγ hη hqn hcapacity x hxY hx
    loc full hLocRep hFullRep B hKB hloc hfull hN

end TypedTriangle.CatalogNative

#print axioms TypedTriangle.CatalogNative.activate_bank_from_native_packing_moments
