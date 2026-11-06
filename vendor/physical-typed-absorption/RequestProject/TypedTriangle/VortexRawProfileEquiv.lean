/-
Copyright (c) 2026 Juan Pablo Traverso Gianini.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module
public import RequestProject.TypedTriangle.VortexGlobalRawProfileTransport
public import RequestProject.TypedTriangle.VortexDiffuseSeedEquiv
set_option maxHeartbeats 4000000 -- build option (original: -DmaxHeartbeats=1600000; raised)
set_option maxRecDepth 16384 -- build option (original: -DmaxRecDepth=8192; raised)
@[expose] public section
open Finset Classical
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1600000
namespace TypedTriangle.Vortex

/-- An approximate raw profile transports across the actual host
identification with its coefficient constant and error unchanged. -/
theorem raw_profile_pull_equiv {X Y I : Type} [Fintype X] [Fintype Y]
    (e : X ≃ Y) (H : Host X I) (J : Host Y I) (F : Set (Multiset I))
    (C ρ : ℝ) (μ : Finset Y → ℝ)
    (hAdj : ∀u v, H.G.Adj u v ↔ J.G.Adj (e u) (e v))
    (hLab : ∀u, H.lab u = J.lab (e u))
    (hRaw : RawProfileAt J F C ρ μ) : RawProfileAt H F C ρ (equivSeed e μ) := by
  have hCard : Fintype.card X = Fintype.card Y := Fintype.card_congr e
  constructor
  · intro Q hQ
    have hBound := hRaw.1 (Q.map e.toEmbedding) (isAllowed_map_equiv e H J F hAdj hLab Q hQ)
    simpa only [equivSeed,hCard] using hBound
  · intro f hf
    rw [bdry_equivSeed e H J F hAdj hLab]
    apply hRaw.2
    induction f using Sym2.ind with
    | _ u v =>
      have huv : H.G.Adj u v := by simpa [edges] using hf
      simpa [edges] using (hAdj u v).1 huv

#print axioms raw_profile_pull_equiv
end TypedTriangle.Vortex
