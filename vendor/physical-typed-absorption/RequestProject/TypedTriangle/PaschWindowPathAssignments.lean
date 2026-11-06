module
public import RequestProject.TypedTriangle.PaschDenseWindowRoutes
set_option maxHeartbeats 4000000 -- build option (original: -DmaxHeartbeats=1600000; raised)
set_option maxRecDepth 16384 -- build option (original: -DmaxRecDepth=8192; raised)
@[expose] public section
open Finset Classical S07V24
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace TypedTriangle.Pasch
variable {V : Type} [Fintype V] [DecidableEq V]

def windowPathAssignments (G : SimpleGraph V) [DecidableRel G.Adj]
    (m : ℕ) (x y : V) (W Z : Finset V) (B : SimpleGraph V) : Finset (Fin m → V) :=
  (validWindowPaths G m x y W Z B).image (intl m)

/-- The actual finite walk family has exactly as many internal assignments.
No spread condition or new probabilistic sample is used. -/
theorem windowPathAssignments_card (G : SimpleGraph V) [DecidableRel G.Adj]
    (m : ℕ) (x y : V) (W Z : Finset V) (B : SimpleGraph V) :
    (windowPathAssignments G m x y W Z B).card = (validWindowPaths G m x y W Z B).card := by
  apply card_image_of_injOn
  intro p hp p' hp' heq
  have hLength : p.length = m+1 := SimpleGraph.mem_finsetWalkLength_iff.mp
    (mem_filter.mp (mem_filter.mp (mem_filter.mp hp).1).1).1
  have hLength' : p'.length = m+1 := SimpleGraph.mem_finsetWalkLength_iff.mp
    (mem_filter.mp (mem_filter.mp (mem_filter.mp hp').1).1).1
  exact intl_injOn m x y hLength hLength' heq

/-- Reconstituting the endpoint coordinates of a retained assignment gives
the original walk at every position. -/
theorem walk_coordinates_from_internals {G : SimpleGraph V} {m : ℕ} {x y : V}
    (p : G.Walk x y) (hLength : p.length = m+1) :
    Fin.cons x (Fin.snoc (intl m p) y) = (fun i : Fin (m+2) => p.getVert i.val) := by
  funext i
  refine Fin.cases ?_ (fun j => ?_) i
  · simp
  · refine Fin.lastCases ?_ (fun k => ?_) j
    · simp only [Fin.cons_succ,Fin.snoc_last,Fin.val_succ,Fin.val_last]
      rw [← hLength]
      exact p.getVert_length.symm
    · simp [intl]

theorem windowPathAssignments_realize (G : SimpleGraph V) [DecidableRel G.Adj]
    (m : ℕ) (x y : V) (W Z : Finset V) (B : SimpleGraph V)
    {f : Fin m → V} (hf : f ∈ windowPathAssignments G m x y W Z B) :
    ∃ p ∈ validWindowPaths G m x y W Z B,
      Fin.cons x (Fin.snoc f y) = (fun i : Fin (m+2) => p.getVert i.val) := by
  obtain ⟨p,hp,rfl⟩ := mem_image.mp hf
  refine ⟨p,hp,walk_coordinates_from_internals p ?_⟩
  exact SimpleGraph.mem_finsetWalkLength_iff.mp
    (mem_filter.mp (mem_filter.mp (mem_filter.mp hp).1).1).1

end TypedTriangle.Pasch

#print axioms TypedTriangle.Pasch.windowPathAssignments_card
#print axioms TypedTriangle.Pasch.walk_coordinates_from_internals
#print axioms TypedTriangle.Pasch.windowPathAssignments_realize
