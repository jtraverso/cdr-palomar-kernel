module
public import Mathlib
set_option maxHeartbeats 4000000 -- build option (original: -DmaxHeartbeats=1600000; raised)
set_option maxRecDepth 16384 -- build option (original: -DmaxRecDepth=8192; raised)
@[expose] public section
open Finset Classical
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace TypedTriangle.Pasch
variable {V : Type*} [Fintype V]

def sixTupleCollisions : Finset (Fin 6 → V) :=
  univ.filter (fun f => ¬ Function.Injective f)

private theorem fixed_collision_card_le (i j : Fin 6) (hij : i ≠ j) :
    (univ.filter (fun f : Fin 6 → V => f i = f j)).card ≤ (Fintype.card V)^5 := by
  let A : Finset (Fin 6) := univ.erase j
  let C := univ.filter (fun f : Fin 6 → V => f i = f j)
  let r : ↥C → (↥A → V) := fun f x => f.val x.val
  have hr : Function.Injective r := by
    intro f g h
    apply Subtype.ext
    funext x
    by_cases hx : x = j
    · subst x
      have hfi : f.val i = f.val j := (mem_filter.mp f.property).2
      have hgi : g.val i = g.val j := (mem_filter.mp g.property).2
      calc
        f.val j = f.val i := hfi.symm
        _ = g.val i := congrFun h ⟨i,by simp [A,hij]⟩
        _ = g.val j := hgi
    · exact congrFun h ⟨x,by simp [A,hx]⟩
  have hh := Fintype.card_le_of_injective r hr
  have hA : A.card = 5 := by simp [A]
  simpa only [Fintype.card_coe,Fintype.card_fun,hA] using hh

/-- Among all labelled six-tuples at most `15*n^5` identify two positions.
The fifteen unordered position pairs are counted in the kernel. -/
theorem sixTupleCollisions_card_le : (sixTupleCollisions (V := V)).card ≤
    15*(Fintype.card V)^5 := by
  let P : Finset (Fin 6 × Fin 6) := univ.filter (fun p => p.1 < p.2)
  let C : Fin 6 × Fin 6 → Finset (Fin 6 → V) :=
    fun p => univ.filter (fun f => f p.1 = f p.2)
  have hP : P.card = 15 := by decide
  have hSub : sixTupleCollisions (V := V) ⊆ P.biUnion C := by
    intro f hf
    have hNot := (mem_filter.mp hf).2
    have hExists : ∃ i j, f i = f j ∧ i ≠ j := by
      by_contra h
      apply hNot
      intro i j hEq
      by_contra hij
      exact h ⟨i,j,hEq,hij⟩
    obtain ⟨i,j,hEq,hij⟩ := hExists
    rcases lt_or_gt_of_ne hij with hlt | hgt
    · exact mem_biUnion.mpr ⟨(i,j),by simp [P,hlt],by simp [C,hEq]⟩
    · exact mem_biUnion.mpr ⟨(j,i),by simp [P,hgt],by simp [C,hEq.symm]⟩
  calc
    (sixTupleCollisions (V := V)).card ≤ (P.biUnion C).card := card_le_card hSub
    _ ≤ ∑ p ∈ P, (C p).card := card_biUnion_le
    _ ≤ ∑ _p ∈ P, (Fintype.card V)^5 := by
      apply sum_le_sum
      intro p hp
      have hlt := (mem_filter.mp hp).2
      exact fixed_collision_card_le p.1 p.2 (ne_of_lt hlt)
    _ = 15*(Fintype.card V)^5 := by simp only [sum_const_nat,hP]

end TypedTriangle.Pasch

#print axioms TypedTriangle.Pasch.sixTupleCollisions_card_le
