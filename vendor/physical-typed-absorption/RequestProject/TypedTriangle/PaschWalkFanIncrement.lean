module
public import RequestProject.TypedTriangle.PaschPotentialIncrement
public import RequestProject.TypedTriangle.PaschWeightedWindowPaths
set_option maxHeartbeats 4000000 -- build option (original: -DmaxHeartbeats=1600000; raised)
set_option maxRecDepth 16384 -- build option (original: -DmaxRecDepth=8192; raised)
@[expose] public section
open Finset Classical
noncomputable section
set_option autoImplicit false
namespace TypedTriangle.Pasch
variable {V : Type*} [DecidableEq V]

/-- Repeated blocks in a retained path do not impose a disjointness condition
against the fixed previous universe. -/
theorem count_union_le_rooted_increment {R : Finset (Finset V)} {L : ℕ}
    (hL : PairCodegreeBound R L) (N : Finset (Finset V)) :
    count (N∪R) ≤ count R + (∑ T ∈ N, rootedCount (insert T R) T) +
      9*L*(N.card.choose 2)+N.card.choose 3+N.card.choose 4 := by
  have hBase := count_union_le_potential_increment hL (N\R) sdiff_disjoint
  have hUnion : (N\R)∪R = N∪R := by
    ext T; simp only [mem_union,mem_sdiff]; tauto
  rw [hUnion] at hBase
  have hSum : (∑ T ∈ N\R, rootedCount (insert T R) T) ≤
      ∑ T ∈ N, rootedCount (insert T R) T := sum_le_sum_of_subset sdiff_subset
  have hk : (N\R).card ≤ N.card := card_le_card sdiff_subset
  have h2 := Nat.mul_le_mul_left (9*L) (Nat.choose_le_choose 2 hk)
  have h3 := Nat.choose_le_choose 3 hk
  have h4 := Nat.choose_le_choose 4 hk
  omega

def walkFanTriangles {G : SimpleGraph V} {x y : V} (v : V) (m : ℕ)
    (p : G.Walk x y) : Finset (Finset V) :=
  univ.image (fun k : Fin (m+1) => {v,p.getVert k.val,p.getVert (k.val+1)})

theorem walkFanTriangles_card {G : SimpleGraph V} {x y : V} (v : V) (m : ℕ)
    (p : G.Walk x y) : (walkFanTriangles v m p).card ≤ m+1 := by
  exact card_image_le.trans (by simp)

/-- The actual collection of fan triangles is paid by the sum already
controlled by the one-assignment averaging theorem. -/
theorem walkFanTriangles_count_increment {G : SimpleGraph V} {x y : V}
    (v : V) (m : ℕ) (p : G.Walk x y) (R : Finset (Finset V))
    (L : ℕ) (hL : PairCodegreeBound R L) :
    count (walkFanTriangles v m p∪R) ≤ count R +
      (∑ k : Fin (m+1), rootedCount
        (insert {v,p.getVert k.val,p.getVert (k.val+1)} R)
        {v,p.getVert k.val,p.getVert (k.val+1)}) +
      9*L*((m+1).choose 2)+(m+1).choose 3+(m+1).choose 4 := by
  have hBase := count_union_le_rooted_increment hL (walkFanTriangles v m p)
  have hSum : (∑ T ∈ walkFanTriangles v m p, rootedCount (insert T R) T) ≤
      ∑ k : Fin (m+1), rootedCount
        (insert {v,p.getVert k.val,p.getVert (k.val+1)} R)
        {v,p.getVert k.val,p.getVert (k.val+1)} := by
    exact sum_image_le_of_nonneg (fun _ _ => Nat.zero_le _)
  have hk := walkFanTriangles_card v m p
  have h2 := Nat.mul_le_mul_left (9*L) (Nat.choose_le_choose 2 hk)
  have h3 := Nat.choose_le_choose 3 hk
  have h4 := Nat.choose_le_choose 4 hk
  omega

end TypedTriangle.Pasch
#print axioms TypedTriangle.Pasch.count_union_le_rooted_increment
#print axioms TypedTriangle.Pasch.walkFanTriangles_card
#print axioms TypedTriangle.Pasch.walkFanTriangles_count_increment
