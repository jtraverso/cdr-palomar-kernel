module
public import RequestProject.TypedTriangle.PaschSupportPotential
set_option maxHeartbeats 4000000 -- build option (original: -DmaxHeartbeats=1600000; raised)
set_option maxRecDepth 16384 -- build option (original: -DmaxRecDepth=8192; raised)
@[expose] public section
open Finset Classical
noncomputable section
set_option autoImplicit false
namespace TypedTriangle.Pasch
variable {A J V : Type*} [DecidableEq A] [DecidableEq J] [DecidableEq V]

/-- Evaluate a support position other than the distinguished free coordinate. -/
def supportEvalAway (base : A → V) (i : J) (p : A ⊕ J) (hp : p ≠ Sum.inr i)
    (r : {j : J // j ≠ i} → V) : V :=
  match p, hp with
  | Sum.inl u, _ => base u
  | Sum.inr j, hj => r ⟨j,fun h => hj (congrArg Sum.inr h)⟩

theorem supportEvalAway_eq (base : A → V) (i : J) (p : A ⊕ J)
    (hp : p ≠ Sum.inr i) (f : J → V) :
    supportEvalAway base i p hp (fun j => f j.val) = Sum.elim base f p := by
  cases p <;> rfl

/-- Every support triple containing a free position has the coordinate
form required by the proved simultaneous support-potential bound. -/
theorem support_triple_has_free_form (base : A → V) (T : Finset (A ⊕ J))
    (hT : T.card = 3) (hFree : ∃ i : J, Sum.inr i ∈ T) :
    ∃ i : J, ∃ a b : ({j : J // j ≠ i} → V) → V,
      ∀ f : J → V, T.image (Sum.elim base f) =
        {a (fun j => f j.val),b (fun j => f j.val),f i} := by
  obtain ⟨i,hi⟩ := hFree
  have he : (T.erase (Sum.inr i)).card = 2 := by rw [card_erase_of_mem hi,hT]
  obtain ⟨p,q,hpq,heq⟩ := card_eq_two.mp he
  have hp : p ∈ T.erase (Sum.inr i) := by rw [heq]; simp
  have hq : q ∈ T.erase (Sum.inr i) := by rw [heq]; simp
  have hpi : p ≠ Sum.inr i := (mem_erase.mp hp).1
  have hqi : q ≠ Sum.inr i := (mem_erase.mp hq).1
  let a := supportEvalAway base i p hpi
  let b := supportEvalAway base i q hqi
  refine ⟨i,a,b,?_⟩
  intro f
  have hRepr : T = insert (Sum.inr i) {p,q} := by
    rw [←heq,insert_erase hi]
  rw [hRepr,image_insert,image_insert,image_singleton]
  have ha : a (fun j => f j.val) = Sum.elim base f p := supportEvalAway_eq base i p hpi f
  have hb : b (fun j => f j.val) = Sum.elim base f q := supportEvalAway_eq base i q hqi f
  rw [ha,hb]
  ext v
  simp only [Sum.elim_inr,mem_insert,mem_singleton]
  tauto

/-- Construct the designated free coordinates from a family of actual
support triples; they are data, not an additional regularity assumption. -/
theorem indexed_support_free_forms {K : Type*} (base : A → V)
    (T : K → Finset (A ⊕ J)) (hT : ∀ k, (T k).card = 3)
    (hFree : ∀ k, ∃ i : J, Sum.inr i ∈ T k) :
    ∃ (i : K → J) (a b : ∀ k, ({j : J // j ≠ i k} → V) → V),
      ∀ k (f : J → V), (T k).image (Sum.elim base f) =
        {a k (fun j => f j.val),b k (fun j => f j.val),f (i k)} := by
  choose i a b h using fun k => support_triple_has_free_form base (T k) (hT k) (hFree k)
  exact ⟨i,a,b,h⟩

theorem exists_low_potential_for_support_triples {K : Type*}
    [Fintype V] [Fintype J] [Fintype K]
    (R : Finset (Finset V)) (L : ℕ) (hL : PairCodegreeBound R L)
    (base : A → V) (T : K → Finset (A ⊕ J)) (hT : ∀ k, (T k).card = 3)
    (hFree : ∀ k, ∃ i : J, Sum.inr i ∈ T k)
    (P : Finset (J → V)) (κ : ℝ) (hκ : 0 < κ)
    (hN : 0 < (Fintype.card (J → V):ℝ))
    (hP : κ*(Fintype.card (J → V):ℝ) ≤ P.card) :
    ∃ f ∈ P, ((∑ k : K, rootedCount
      (insert ((T k).image (Sum.elim base f)) R) ((T k).image (Sum.elim base f))):ℝ) ≤
        ((Fintype.card K:ℝ)*(L:ℝ)^3)/κ := by
  obtain ⟨i,a,b,hForm⟩ := indexed_support_free_forms base T hT hFree
  obtain ⟨f,hf,hCost⟩ := exists_low_support_potential R L hL i a b P κ hκ hN hP
  refine ⟨f,hf,?_⟩
  have he : (∑ k : K, rootedCount
      (insert ((T k).image (Sum.elim base f)) R) ((T k).image (Sum.elim base f))) =
        supportCompletionCost R i a b f := by
    unfold supportCompletionCost
    apply sum_congr rfl
    intro k _
    rw [hForm k f]
  rw [←Nat.cast_sum,he]
  exact hCost

#print axioms supportEvalAway_eq
#print axioms support_triple_has_free_form
#print axioms indexed_support_free_forms
#print axioms exists_low_potential_for_support_triples
end TypedTriangle.Pasch
