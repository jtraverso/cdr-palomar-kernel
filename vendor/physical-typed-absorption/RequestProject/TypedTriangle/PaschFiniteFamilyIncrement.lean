module
public import RequestProject.TypedTriangle.PaschWalkFanIncrement
set_option maxHeartbeats 4000000 -- build option (original: -DmaxHeartbeats=1600000; raised)
set_option maxRecDepth 16384 -- build option (original: -DmaxRecDepth=8192; raised)
@[expose] public section
open Finset Classical
noncomputable section
set_option autoImplicit false
namespace TypedTriangle.Pasch
variable {V K : Type*} [DecidableEq V] [Fintype K]

/-- A finite list of new blocks pays its own actual rooted costs and a
constant higher-order term. Duplicate images only decrease the bound. -/
theorem finite_family_count_increment (f : K→Finset V)
    (R : Finset (Finset V)) (L : ℕ) (hL : PairCodegreeBound R L) :
    count (univ.image f∪R)  ≤  count R+(∑k:K,rootedCount (insert (f k) R) (f k))+
      9*L*((Fintype.card K).choose 2)+(Fintype.card K).choose 3+(Fintype.card K).choose 4 := by
  have hBase := count_union_le_rooted_increment hL (univ.image f)
  have hSum : (∑T∈univ.image f,rootedCount (insert T R) T)  ≤ 
      ∑k:K,rootedCount (insert (f k) R) (f k) :=
    sum_image_le_of_nonneg (fun _ _ => Nat.zero_le _)
  have hk : (univ.image f).card ≤ Fintype.card K := card_image_le.trans (by simp)
  have h2 := Nat.mul_le_mul_left (9*L) (Nat.choose_le_choose 2 hk)
  have h3 := Nat.choose_le_choose 3 hk
  have h4 := Nat.choose_le_choose 4 hk
  omega

end TypedTriangle.Pasch
#print axioms TypedTriangle.Pasch.finite_family_count_increment
