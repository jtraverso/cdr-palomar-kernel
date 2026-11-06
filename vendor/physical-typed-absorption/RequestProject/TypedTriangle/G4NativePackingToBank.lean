/-
Copyright (c) 2026 Juan Pablo Traverso Gianini.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module
public import RequestProject.TypedTriangle.G4FiniteMonitorTests
public import RequestProject.TypedTriangle.G4NativePackingActivation
set_option maxHeartbeats 4000000 -- build option (original: -DmaxHeartbeats=1600000; raised)
set_option maxRecDepth 16384 -- build option (original: -DmaxRecDepth=8192; raised)
@[expose] public section

/-! Feed every coordinate of the actual bank into one monitored packing call,
then activate that same bank on the packing's physical positive residue. -/

open Finset Classical
noncomputable section
set_option maxHeartbeats 1600000

namespace TypedTriangle.CatalogNative

open S07V40 S07V42 S07V43 S07V44 S07V46 S07V47
open TypedTriangle.LocalizedCover

variable {V I : Type} [Fintype V] {H : SimpleGraph V} {lab : V → I}
  {F : Set (Multiset I)} {W : Finset V} {d c E : ℕ}

theorem activate_bank_after_one_monitored_packing
    (C0 : CoreCompression H lab F W d c E) (Rc : ℕ)
    (A M K P q Ecell zmax N L : ℕ)
    (Mon : ∀ Z : Finset V, CatalogGen C0 Rc Z →
      PhysicalMonitors C0 Rc Z A M K)
    (Fm : FullMonitor C0 Rc A M K)
    (hP : P = 2 * gammaL A M L)
    (F0 : Finset (Sym2 V))
    (hBank : MacroBank (protSetting C0 Rc P q Ecell zmax F0) L N)
    (hgen : ∀ j, CatalogGen C0 Rc
      (Zstrat (protSetting C0 Rc P q Ecell zmax F0) N j))
    (n : ℕ) (Λ η γ ηPack τ ρ τSel : ℝ)
    (hΛ : 0 ≤ Λ) (hη : 0 ≤ η) (hγ : 0 < γ)
    (hsize : (L+2)*K ≤ n)
    (hqn : γ * n ≤ q)
    (hcapacity : η *
      ((2 * Ecell * (childSetting C0 Rc P q Ecell zmax).Bstar : ℕ) : ℝ) / γ ≤ 1)
    (hKB : (K : ℝ) *
      (τ + (3 * Λ / 2) * (ηPack + 2 * ρ + 2 * τSel)) ≤ η)
    (loc : ℕ → Fin K → Sym2 V → ℝ)
    (full : Fin K → Sym2 V → ℝ)
    (hLocRep : ∀ ℓ (hg : CatalogGen C0 Rc
      (Zstrat (protSetting C0 Rc P q Ecell zmax F0) N (ℓ + 1))) j
        (x : MCore H lab F W),
      ∑ e, loc ℓ j e * ((x.1 e : ℤ) : ℝ) =
        physMonReal C0
          (Dset C0 Rc (Zstrat
            (protSetting C0 Rc P q Ecell zmax F0) N (ℓ + 1)))
          (Mon _ hg).psi j x)
    (hFullRep : ∀ j (x : MCore H lab F W),
      ∑ e, full j e * ((x.1 e : ℤ) : ℝ) =
        physMonReal C0 ∅ Fm.psi j x)
    (hLocTri : ∀ ℓ j T, IsAllowed (⟨H,lab⟩ : Host V I) F T →
      |triSum (loc ℓ j) T| ≤
        3 * Λ * (T ∩ Zstrat
          (protSetting C0 Rc P q Ecell zmax F0) N (ℓ+1)).card)
    (hFullTri : ∀ j T, IsAllowed (⟨H,lab⟩ : Host V I) F T →
      |triSum (full j) T| ≤ 3 * Λ * T.card)
    (hPack : ∀ (badF : Fin (L+1) × Fin K → Finset V)
        (locF : Fin (L+1) × Fin K → Sym2 V → ℝ)
        (fullF : Fin K → Sym2 V → ℝ),
      ((Fintype.card (Fin (L+1) × Fin K) + Fintype.card (Fin K) : ℕ) : ℝ) ≤ n →
      (∀ k T, IsAllowed (⟨H,lab⟩ : Host V I) F T →
        |triSum (locF k) T| ≤ 3 * Λ * (T ∩ badF k).card) →
      (∀ j T, IsAllowed (⟨H,lab⟩ : Host V I) F T →
        |triSum (fullF j) T| ≤ 3 * Λ * T.card) →
      ∃ (Y : Finset (Sym2 V)) (x : MCore H lab F W) (load : ℝ),
        Y ⊆ F0 ∧
        Y ⊆ edges (⟨H,lab⟩ : Host V I) ∧
        (x : Sym2 V → ℤ) = ind Y ∧
        clsQ H lab F W (x : Sym2 V → ℤ) ∈ KZ H lab F W ∅ ∧
        load ≤ ηPack * n ∧
        (∀ k, |edgeSum (locF k) Y| ≤
          τ * n * (badF k).card + (3 * Λ * (badF k).card) *
            (load + ρ*n + 2*(τSel*n) + ρ*n) / 2) ∧
        ∀ j, |edgeSum (fullF j) Y| ≤
          τ * (n : ℝ)^2 + (3 * Λ * n) *
            (load + ρ*n + 2*(τSel*n) + ρ*n) / 2)
    (hN : (protSetting C0 Rc P q Ecell zmax F0).K
      (Zr (protSetting C0 Rc P q Ecell zmax F0) N) ≠ ⊥ →
      1 + η * n ^ 2 ≤ 2 * N) :
    ∃ (Y : Finset (Sym2 V)) (x : MCore H lab F W) (J : ℕ),
      Y ⊆ F0 ∧ Y ⊆ edges (⟨H,lab⟩ : Host V I) ∧
      J ≤ L ∧ (x : Sym2 V → ℤ) = ind Y ∧
      ProtOutcome C0 Rc P q Ecell zmax F0 N J x ∧
      ((protSetting C0 Rc P q Ecell zmax F0).K
        (Zr (protSetting C0 Rc P q Ecell zmax F0) N) ≠ ⊥ → J = L) := by
  let S := protSetting C0 Rc P q Ecell zmax F0
  let badF : Fin (L+1) × Fin K → Finset V :=
    fun k => Zstrat S N (k.1.val+1)
  let locF : Fin (L+1) × Fin K → Sym2 V → ℝ :=
    fun k => loc k.1.val k.2
  have hCount :
      ((Fintype.card (Fin (L+1) × Fin K) + Fintype.card (Fin K) : ℕ) : ℝ) ≤ n := by
    simp only [Fintype.card_prod, Fintype.card_fin]
    exact_mod_cast (show (L+1)*K+K ≤ n from by nlinarith only [hsize])
  have hTri : ∀ k T, IsAllowed (⟨H,lab⟩ : Host V I) F T →
      |triSum (locF k) T| ≤ 3 * Λ * (T ∩ badF k).card := by
    intro k T hT
    exact hLocTri k.1.val k.2 T hT
  obtain ⟨Y,x,load,hYF,hYE,hxY,hx,hload,hLocMom,hFullMom⟩ :=
    hPack badF locF full hCount hTri hFullTri
  have hLoc : ∀ ℓ ≤ L, ∀ j,
      |edgeSum (loc ℓ j) Y| ≤
        τ * n * (Zstrat S N (ℓ+1)).card +
        (3 * Λ * (Zstrat S N (ℓ+1)).card) *
          (load + ρ*n + 2*(τSel*n) + ρ*n) / 2 := by
    intro ℓ hℓ j
    exact hLocMom ⟨⟨ℓ, Nat.lt_succ_iff.mpr hℓ⟩, j⟩
  obtain ⟨J,hJ,hOutcome,hFinish,_⟩ :=
    activate_bank_from_native_packing_moments C0 Rc A M K P q Ecell zmax N L
      Mon Fm hP F0 Y hBank hgen n Λ η γ ηPack τ ρ τSel load
      hΛ hη hγ hqn hcapacity hload hKB x hxY hx loc full
      (fun ℓ hg j => hLocRep ℓ hg j x)
      (fun j => hFullRep j x) hLoc hFullMom hN
  exact ⟨Y,x,J,hYF,hYE,hJ,hxY,hOutcome,hFinish⟩

end TypedTriangle.CatalogNative

#print axioms TypedTriangle.CatalogNative.activate_bank_after_one_monitored_packing
