/-
Copyright (c) 2026 Juan Pablo Traverso Gianini.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module
public import RequestProject.TypedTriangle.VortexEmbeddedPaidAssembly
public import RequestProject.TypedTriangle.SampledForbiddenTransport
set_option maxHeartbeats 4000000 -- build option (original: -DmaxHeartbeats=1600000; raised)
set_option maxRecDepth 16384 -- build option (original: -DmaxRecDepth=8192; raised)
@[expose] public section
open Finset Classical
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1600000
namespace TypedTriangle.Vortex

/-- The actual image of a prepared child, with its original vertex map. -/
def embeddingWindow {X Y : Type} [Fintype X] (ι : X ↪ Y) : Finset Y :=
  univ.map ι

/-- No vertex is reselected when the child is expressed as a parent window. -/
def embeddingWindowEquiv {X Y : Type} [Fintype X] (ι : X ↪ Y) :
    X ≃ {y // y ∈ embeddingWindow ι} :=
  Equiv.ofBijective (fun x => ⟨ι x,mem_map.mpr ⟨x,mem_univ _,rfl⟩⟩) (by
    constructor
    · intro x y h
      exact ι.injective (congrArg Subtype.val h)
    · intro y
      obtain ⟨x,hx,hxy⟩ := mem_map.mp y.property
      exact ⟨x,Subtype.ext hxy⟩)

@[simp] theorem embeddingWindowEquiv_val {X Y : Type} [Fintype X]
    (ι : X ↪ Y) (x : X) : (embeddingWindowEquiv ι x).val = ι x := rfl

theorem card_embeddingWindow {X Y : Type} [Fintype X] (ι : X ↪ Y) :
    (embeddingWindow ι).card = Fintype.card X := by
  simp only [embeddingWindow,card_map,card_univ]

/-- The two carrier descriptions lift every edge to the identical parent edge. -/
theorem lift_embeddingWindow_image {X Y : Type} [Fintype X] [Fintype Y]
    (ι : X ↪ Y) (E : Finset (Sym2 X)) :
    SampledResource.lift (embeddingWindow ι)
      (E.image (Sym2.map (embeddingWindowEquiv ι))) = embeddedEdges ι E := by
  change (E.image _).image _ = E.image _
  rw [Finset.image_image]
  congr 1
  funext f
  induction f using Sym2.ind with
  | _ u v => rfl

/-- Preserving the full raw child forces its induced graph in the actual
parent to be exactly the raw child; the ambient parent may have paid holes. -/
theorem preserved_window_adj_iff {X Y I : Type} [Fintype X] [Fintype Y]
    (ι : X ↪ Y) (J : Host X I) (Hraw Hactual : Host Y I)
    (hRaw : ∀ u v, J.G.Adj u v ↔ Hraw.G.Adj (ι u) (ι v))
    (hActual : Hactual.G ≤ Hraw.G)
    (hPreserved : embeddedEdges ι (edges J) ⊆ edges Hactual) :
    ∀ u v, J.G.Adj u v ↔ Hactual.G.Adj (ι u) (ι v) := by
  intro u v
  constructor
  · intro huv
    have he : s(u,v) ∈ edges J := by simpa [edges] using huv
    have heActual := hPreserved (mem_image.mpr ⟨s(u,v),he,rfl⟩)
    simpa [edges] using heActual
  · intro huv
    exact (hRaw u v).2 (hActual huv)

/-- The literal window host used by the paid bank frontend. -/
def embeddingWindowHost {X Y I : Type} [Fintype X]
    (ι : X ↪ Y) (H : Host Y I) : Host {y // y ∈ embeddingWindow ι} I :=
  ⟨H.G.comap Subtype.val,H.lab ∘ Subtype.val⟩

theorem preserved_window_host_equiv {X Y I : Type} [Fintype X] [Fintype Y]
    (ι : X ↪ Y) (J : Host X I) (Hraw Hactual : Host Y I)
    (hRaw : ∀ u v, J.G.Adj u v ↔ Hraw.G.Adj (ι u) (ι v))
    (hActual : Hactual.G ≤ Hraw.G)
    (hPreserved : embeddedEdges ι (edges J) ⊆ edges Hactual)
    (hLab : ∀ u, J.lab u = Hactual.lab (ι u)) :
    (∀ u v, J.G.Adj u v ↔
      (embeddingWindowHost ι Hactual).G.Adj (embeddingWindowEquiv ι u) (embeddingWindowEquiv ι v)) ∧
    (∀ u, J.lab u = (embeddingWindowHost ι Hactual).lab (embeddingWindowEquiv ι u)) := by
  exact ⟨preserved_window_adj_iff ι J Hraw Hactual hRaw hActual hPreserved,hLab⟩

#print axioms embeddingWindowEquiv
#print axioms lift_embeddingWindow_image
#print axioms preserved_window_host_equiv
end TypedTriangle.Vortex
