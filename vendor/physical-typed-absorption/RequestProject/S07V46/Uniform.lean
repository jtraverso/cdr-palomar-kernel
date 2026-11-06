/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module
public import RequestProject.S07V46.Global
set_option maxHeartbeats 4000000 -- build option (original: -DmaxHeartbeats=1600000; raised)
set_option maxRecDepth 16384 -- build option (original: -DmaxRecDepth=8192; raised)
@[expose] public section

/-!
# V46 §8 — constants fixed BEFORE the host

`global_allocation_constants d c E R L` : the constants `A, M, K` (V34/V44 monitors on the fixed
bounded presentation `box d (max 1 (max R E))`) and the number of colours
`P = 2 · gammaL A M L = 2 A (L+1) (1+AM)^L` are fixed from `(d, c, E, R, L)` ONLY.  Then, for
every host and core compression `C0`, ONE family of stratum monitors (one for every `Z` with
`CatalogGen`) and ONE full monitor are fixed before any bank or charge, and for every actual child
bank (with `L` strata bound), every `J ≤ L`, and every charge `x ∈ K_∅` satisfying the localized
and full monitor bounds and the numeric criterion, the allocation outcome (`AllocOutcome`, the
conclusion of `global_capacitated_allocation`) holds.

The smallness `η (2 Ecell B*) / γ ≤ 1` is a condition on `η` relative to constants (`Ecell`,
`|Cat|`, `P` are fixed before the host); `q ≥ γ n` and `1 + τ n² ≤ ∑_{i ≤ J} m_i` are conditions
on the bank.  For the child bank of V43 the chain bound is `L = card (Cat d R)`.
-/

open Finset Classical Submodule

noncomputable section

namespace S07V46

open TypedTriangle.SparseEdge TypedTriangle.ComponentRows TypedTriangle.Composition
open TypedTriangle.Dispersal S07V42 S07V34 S07V32 S07V44 S07V43 S07V40

variable {V I : Type*} [Fintype V] {H : SimpleGraph V} {lab : V → I} {F : Set (Multiset I)}
  {W : Finset V} {d c E : ℕ}

/-- **the allocation outcome** (exactly the conclusion of `global_capacitated_allocation`) -/
def AllocOutcome (C0 : CoreCompression H lab F W d c E) (R P q Ecell zmax N J : ℕ)
    (x : MCore H lab F W) : Prop :=
  ∃ (z : ℕ → Fin P → Cat d R → ℤ) (hs : ∀ i, (stratBank (childSetting C0 R P q Ecell zmax) N i).Supplies (z i)),
    (∀ i p v, z i p v ≠ 0 → i ≤ J ∧ gCat C0 R v ∈ KZ H lab F W (Zstrat (childSetting C0 R P q Ecell zmax) N i)) ∧
    (∀ i p v, (z i p v).natAbs ≤ mStrat (childSetting C0 R P q Ecell zmax) N i) ∧
    (∀ i, PhysicalActivation H lab F W (stratBank (childSetting C0 R P q Ecell zmax) N i) (gCat C0 R) (z i) (hs i) Ecell) ∧
    (∀ i, Avoids (Zstrat (childSetting C0 R P q Ecell zmax) N i) (Bank.payload (hs i))) ∧
    (∀ i j, i ≠ j → Disjoint (stratBank (childSetting C0 R P q Ecell zmax) N i).total (stratBank (childSetting C0 R P q Ecell zmax) N j).total) ∧
    clsQ H lab F W (x : Sym2 V → ℤ) +
      chargeQ H lab F W ((range (J + 1)).biUnion fun i => Bank.payload (hs i)) = 0 ∧
    (x : Sym2 V → ℤ) + ind ((range (J + 1)).biUnion fun i => Bank.payload (hs i)) ∈
      LamCore H lab F W ∧
    ((range (J + 1)).biUnion fun i => (stratBank (childSetting C0 R P q Ecell zmax) N i).total) =
      ((range (J + 1)).biUnion fun i => Bank.cover (hs i)) ∪
        ((range (J + 1)).biUnion fun i => Bank.payload (hs i)) ∧
    Disjoint ((range (J + 1)).biUnion fun i => Bank.cover (hs i))
      ((range (J + 1)).biUnion fun i => Bank.payload (hs i)) ∧
    physBasal H lab F ((range (J + 1)).biUnion fun i => Bank.cover (hs i)) ∧
    ((range (J + 1)).biUnion fun i => Bank.payload (hs i)).card ≤
      Ecell * ∑ i ∈ range (J + 1), ∑ p, ∑ v, (z i p v).natAbs

universe u v

/-- **Global capacitated allocation with all constants fixed before the host.** -/
theorem global_allocation_constants (d c E R L : ℕ) :
    ∃ A M K P : ℕ, P = 2 * gammaL A M L ∧
    ∀ {V : Type u} [Fintype V] {I : Type v} {H : SimpleGraph V} {lab : V → I}
      {F : Set (Multiset I)} {W : Finset V} (C0 : CoreCompression H lab F W d c E),
    ∃ (Mon : ∀ Z : Finset V, CatalogGen C0 R Z → PhysicalMonitors C0 R Z A M K)
      (Fm : FullMonitor C0 R A M K),
    ∀ (q Ecell zmax N J : ℕ), MacroBank (childSetting C0 R P q Ecell zmax) L N → J ≤ L →
    ∀ hgen : (∀ j ≤ J, CatalogGen C0 R (Zstrat (childSetting C0 R P q Ecell zmax) N j)),
    ∀ {eta gamma tau : ℝ} (n : ℕ), 0 < gamma → 0 ≤ eta → 0 ≤ tau → gamma * n ≤ q →
      eta * ((2 * Ecell * (childSetting C0 R P q Ecell zmax).Bstar : ℕ) : ℝ) / gamma ≤ 1 →
      1 + tau * n ^ 2 ≤ ∑ i ∈ range (J + 1), (mStrat (childSetting C0 R P q Ecell zmax) N i : ℝ) →
      ∀ x : MCore H lab F W, clsQ H lab F W (x : Sym2 V → ℤ) ∈ KZ H lab F W ∅ →
      (∀ ℓ (h : ℓ < J), (l1 (physMon C0 (Dset C0 R (Zstrat (childSetting C0 R P q Ecell zmax) N (ℓ + 1)))
          (Mon _ (hgen (ℓ + 1) h)).psi x) : ℝ) ≤ eta * n * (Zstrat (childSetting C0 R P q Ecell zmax) N (ℓ + 1)).card) →
      (l1 (physMon C0 ∅ Fm.psi x) : ℝ) ≤ tau * n ^ 2 →
      AllocOutcome C0 R P q Ecell zmax N J x := by
  obtain ⟨A, M, K, hU⟩ := uniform_monitors_with_full.{u, v} d c E R
  refine ⟨A, M, K, 2 * gammaL A M L, rfl, ?_⟩
  intro V _ I H lab F W C0
  refine ⟨fun Z h => Classical.choice ((hU C0).1 Z h), Classical.choice (hU C0).2, ?_⟩
  intro q Ecell zmax N J hM hJL hgen eta gamma tau n hγ hη hτ hqn hθ hSJ x hx hloc hfull
  exact global_capacitated_allocation C0 hM hJL
    (fun ℓ h => Classical.choice ((hU C0).1 _ (hgen (ℓ + 1) h))) _ hgen n hγ hη hτ hqn hθ le_rfl
    hSJ x hx hloc hfull

end S07V46
