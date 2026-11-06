/-
Copyright (c) 2026 Juan Pablo Traverso Gianini.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module
public import RequestProject.S07V47.Uniform
public import RequestProject.TypedTriangle.NativeProtectedGeometricBank
set_option maxHeartbeats 4000000 -- build option (original: -DmaxHeartbeats=1600000; raised)
set_option maxRecDepth 16384 -- build option (original: -DmaxRecDepth=8192; raised)
@[expose] public section
open Finset Classical
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace TypedTriangle.CatalogNative
open S07V40 S07V42 S07V43 S07V44
variable {V I : Type*} [Fintype V] {H : SimpleGraph V} {lab : V → I}
  {F : Set (Multiset I)} {W : Finset V}

/-- The local constructor and V47 use exactly the same protected setting,
including the original host and its integer charge group. -/
theorem native_protect_eq_protSetting {d c E : ℕ}
    (C0 : CoreCompression H lab F W d c E) (R P q Ecell zmax : ℕ)
    (F0 : Finset (Sym2 V)) :
    ProtectedBank.protect (childSetting C0 R P q Ecell zmax) F0 =
      S07V47.protSetting C0 R P q Ecell zmax F0 := rfl

/-- Every ACTUAL protected-bank stratum has its catalog generation derived
from the native small-deletion compressions. Includes the last early-stop
set and empty strata. No CatalogGen provider is assumed. -/
theorem catalogGen_on_protected_strata {β : ℝ} {h : ℕ} (hβ : 0 < β)
    {d c E d' c' E' P q Ecell zmax L N : ℕ}
    (h3 : SparseEdge.CommonNbrCond (H.comap (Subtype.val : {x // x ∈ W} → V))
      (lab ∘ Subtype.val) F β)
    (h4 : SparseEdge.HingeCond (H.comap (Subtype.val : {x // x ∈ W} → V))
      (lab ∘ Subtype.val) F β h)
    (hW : coreN0 β h ≤ W.card) (C0 : CoreCompression H lab F W d c E)
    (hz : (zmax:ℝ) ≤ coreDelta β h*W.card)
    (CZ : ∀ Z : Finset V, Z.card ≤ zmax → Nonempty (DelCompression H lab F Z d' c' E'))
    (F0 : Finset (Sym2 V))
    (hM : MacroBank (ProtectedBank.protect
      (childSetting C0 (catR β d c E d' c' E') P q Ecell zmax) F0) L N) :
    ∀ j, CatalogGen C0 (catR β d c E d' c' E')
      (Zstrat (S07V47.protSetting C0 (catR β d c E d' c' E') P q Ecell zmax F0) N j) := by
  rw [native_protect_eq_protSetting] at hM
  intro j
  let S := S07V47.protSetting C0 (catR β d c E d' c' E') P q Ecell zmax F0
  have hs : (Zstrat S N j).card ≤ zmax :=
    hM.small _ ((preStrat_le N j).trans (numRounds_le N))
  obtain ⟨Cj⟩ := CZ (Zstrat S N j) hs
  exact catalogGen_of_H3H4 hβ h3 h4 hW C0
    ((show ((Zstrat S N j).card:ℝ) ≤ zmax by exact_mod_cast hs).trans hz) Cj

end TypedTriangle.CatalogNative
