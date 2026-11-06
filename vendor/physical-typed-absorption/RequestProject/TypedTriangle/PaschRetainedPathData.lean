module
public import RequestProject.TypedTriangle.PaschDenseWindowRoutes
set_option maxHeartbeats 4000000 -- build option (original: -DmaxHeartbeats=1600000; raised)
set_option maxRecDepth 16384 -- build option (original: -DmaxRecDepth=8192; raised)
@[expose] public section
open Finset Classical S07V24
noncomputable section
set_option autoImplicit false
namespace TypedTriangle.Pasch
variable {V : Type} [Fintype V] [DecidableEq V]
/-- Read the retained-family certificate using the same canonical predicate
instance as its definition, including inside a context with decidable B. -/
theorem valid_window_path_data {G : SimpleGraph V} [DecidableRel G.Adj]
    {m : ℕ} {x y : V} {W Z : Finset V} {B : SimpleGraph V} {p : G.Walk x y}
    (hp : p ∈ validWindowPaths G m x y W Z B) :
    p ∈ pathsIn G m x y W ∧ (∀ i : Fin m, intl m p i ∉ Z) ∧
      ∀ k < m+1, ¬ B.Adj (p.getVert k) (p.getVert (k+1)) :=
  mem_filter.mp hp
end TypedTriangle.Pasch
#print axioms TypedTriangle.Pasch.valid_window_path_data
