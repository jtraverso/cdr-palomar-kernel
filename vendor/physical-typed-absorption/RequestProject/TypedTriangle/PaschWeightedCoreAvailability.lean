module
public import RequestProject.S07V27.CoreComponent
public import RequestProject.TypedTriangle.PaschSelectorUniverse
public import RequestProject.TypedTriangle.PaschEmbeddingIncidence
set_option maxHeartbeats 4000000 -- build option (original: -DmaxHeartbeats=1600000; raised)
set_option maxRecDepth 16384 -- build option (original: -DmaxRecDepth=8192; raised)
@[expose] public section
open Finset Classical SelSimul
noncomputable section
set_option autoImplicit false
namespace TypedTriangle.Pasch
variable {V I Ambient : Type*} [DecidableEq V] [DecidableEq Ambient]

/-- Literal ambient triangle universe of one local selector. Every later
mode is a subfamily of this fixed universe. -/
def weightedCoreUniverse (ι : V ↪ Ambient) (v : V) (σ : LocalSel V) :
    Finset (Finset Ambient) :=
  mapConfiguration ι (σ.P.image (selectorTriangle v))

/-- Internal construction contract for one root. The previous family is
arbitrary and its pair-codegree remains an explicit input. Geometric windows
are exactly the legacy windows; its support is never added to Z0. -/
def WeightedCoreAvail (G : SimpleGraph V) (lab : V → I) (F : Set (Multiset I))
    (v : V) (U : Finset V) (Adm : Finset V → Prop)
    (A ζw ρw : ℕ) (Wc : Finset V) (ι : V ↪ Ambient) (pay : ℕ → ℝ) : Prop :=
  ∀ (R0 : Finset (Finset Ambient)) (L0 : ℕ), PairCodegreeBound R0 L0 →
    ∀ (Z0 : Finset V) (Bf : Finset (Sym2 V)),
      Z0.card ≤ ζw → (∀ y, SelSimul.edeg Bf y ≤ ρw) →
      ∃ σ : LocalSel V,
        σ.Valid G lab F v U Adm Z0 Bf A ∧ σ.W ⊆ Wc ∧
          (count (R0 ∪ weightedCoreUniverse ι v σ) : ℝ) ≤
            (count R0 : ℝ) + (U.card : ℝ) * pay L0

/-- Components and root scheduling shift the concrete codegree argument;
this does not assert a uniform codegree across different vortex levels. -/
def weightedCorePayShift (pay : ℕ → ℝ) (k : ℕ) : ℕ → ℝ :=
  fun L => pay (L+k)

end TypedTriangle.Pasch
