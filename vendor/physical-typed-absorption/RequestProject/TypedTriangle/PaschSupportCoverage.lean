module
public import RequestProject.TypedTriangle.PaschSupportForms
set_option maxHeartbeats 4000000 -- build option (original: -DmaxHeartbeats=1600000; raised)
set_option maxRecDepth 16384 -- build option (original: -DmaxRecDepth=8192; raised)
@[expose] public section
open Finset Classical
noncomputable section
set_option autoImplicit false
namespace TypedTriangle.Pasch
variable {A J V : Type*} [Fintype A] [Fintype J] [Fintype V]
  [DecidableEq A] [DecidableEq J] [DecidableEq V]

def freePositionTriples (A J : Type*) [Fintype A] [Fintype J]
    [DecidableEq A] [DecidableEq J] : Finset (Finset (A ⊕ J)) :=
  univ.powersetCard 3 |>.filter (fun T => ∃ j : J, Sum.inr j ∈ T)

def newSupportTriples (base : A → V) (f : J → V) : Finset (Finset V) :=
  (univ.image base ∪ univ.image f).powersetCard 3 |>.filter (fun Q => ¬ Q ⊆ univ.image base)

theorem freePositionTriples_card_le :
    (freePositionTriples A J).card ≤ Nat.choose (Fintype.card A+Fintype.card J) 3 := by
  calc (freePositionTriples A J).card ≤ ((univ : Finset (A ⊕ J)).powersetCard 3).card :=
      card_filter_le _ _
    _ = _ := by rw [card_powersetCard,card_univ,Fintype.card_sum]

/-- Lift a concrete new support triple to a triple of positions. No
injectivity of the assignment is needed: choose one preimage of each of its three vertices. -/
theorem support_triple_has_position_preimage (base : A → V) (f : J → V)
    (Q : Finset V) (hQ : Q.card = 3)
    (hSupp : Q ⊆ univ.image base ∪ univ.image f) (hNew : ¬ Q ⊆ univ.image base) :
    ∃ T ∈ freePositionTriples A J, T.image (Sum.elim base f) = Q := by
  have hpre (v : {v // v ∈ Q}) : ∃ p : A ⊕ J, Sum.elim base f p = v.val := by
    rcases mem_union.mp (hSupp v.property) with ha | hj
    · obtain ⟨a,_,hav⟩ := mem_image.mp ha
      exact ⟨Sum.inl a,hav⟩
    · obtain ⟨j,_,hjv⟩ := mem_image.mp hj
      exact ⟨Sum.inr j,hjv⟩
  choose p hp using hpre
  let T : Finset (A ⊕ J) := univ.image p
  have hinj : Function.Injective p := by
    intro x y hxy
    apply Subtype.ext
    exact (hp x).symm.trans ((congrArg (Sum.elim base f) hxy).trans (hp y))
  have hCard : T.card = 3 := by
    rw [card_image_of_injective _ hinj,card_univ,Fintype.card_coe,hQ]
  have hImage : T.image (Sum.elim base f) = Q := by
    ext v
    constructor
    · intro hv
      obtain ⟨r,hr,hrv⟩ := mem_image.mp hv
      obtain ⟨x,_,hxr⟩ := mem_image.mp hr
      have he : x.val = v := (hp x).symm.trans (by simpa only [hxr] using hrv)
      exact he ▸ x.property
    · intro hv
      let x : {v // v ∈ Q} := ⟨v,hv⟩
      exact mem_image.mpr ⟨p x,mem_image.mpr ⟨x,mem_univ _,rfl⟩,hp x⟩
  have hFree : ∃ j : J, Sum.inr j ∈ T := by
    obtain ⟨v,hv,hvNot⟩ := Finset.not_subset.mp hNew
    let x : {v // v ∈ Q} := ⟨v,hv⟩
    have hpx : p x ∈ T := mem_image.mpr ⟨x,mem_univ _,rfl⟩
    cases he : p x with
    | inl a =>
      have ha : base a = v := by simpa only [he,Sum.elim_inl] using hp x
      exact (hvNot (mem_image.mpr ⟨a,mem_univ _,ha⟩)).elim
    | inr j => exact ⟨j,by simpa only [he] using hpx⟩
  exact ⟨T,mem_filter.mpr ⟨mem_powersetCard.mpr ⟨subset_univ _,hCard⟩,hFree⟩,hImage⟩

/-- The simultaneous potential covers every possible new mode block, not
only a separately prescribed list of triangles. -/
theorem sum_mode_cost_le_support_potential (R N : Finset (Finset V))
    (base : A → V) (f : J → V) (hCard : ∀ Q ∈ N, Q.card = 3)
    (hSupp : ∀ Q ∈ N, Q ⊆ univ.image base ∪ univ.image f)
    (hNew : ∀ Q ∈ N, ¬ Q ⊆ univ.image base) :
    (∑ Q ∈ N, rootedCount (insert Q R) Q) ≤
      ∑ T ∈ freePositionTriples A J, rootedCount
        (insert (T.image (Sum.elim base f)) R) (T.image (Sum.elim base f)) := by
  have hSub : N ⊆ (freePositionTriples A J).image (fun T => T.image (Sum.elim base f)) := by
    intro Q hQ
    obtain ⟨T,hT,hImage⟩ := support_triple_has_position_preimage base f Q (hCard Q hQ) (hSupp Q hQ) (hNew Q hQ)
    exact mem_image.mpr ⟨T,hT,hImage⟩
  exact (sum_le_sum_of_subset hSub).trans (sum_image_le_of_nonneg (fun _ _ => Nat.zero_le _))

/-- The selected assignment bounds the actual increase of the support
potential over all new triples, with no list of mode blocks as input. -/
theorem exists_low_support_increment (R : Finset (Finset V)) (L : ℕ)
    (hL : PairCodegreeBound R L) (base : A → V) (P : Finset (J → V)) (κ : ℝ)
    (hκ : 0 < κ) (hN : 0 < (Fintype.card (J → V):ℝ))
    (hP : κ*(Fintype.card (J → V):ℝ) ≤ P.card) :
    ∃ f ∈ P, (∑ Q ∈ newSupportTriples base f, (rootedCount (insert Q R) Q:ℝ)) ≤
      ((Nat.choose (Fintype.card A+Fintype.card J) 3:ℝ)*(L:ℝ)^3)/κ := by
  let Kpos := freePositionTriples A J
  have hCard (k : {T // T ∈ Kpos}) : k.val.card = 3 :=
    (mem_powersetCard.mp (mem_filter.mp k.property).1).2
  have hFree (k : {T // T ∈ Kpos}) : ∃ j : J, Sum.inr j ∈ k.val :=
    (mem_filter.mp k.property).2
  obtain ⟨f,hf,hCost⟩ := exists_low_potential_for_support_triples R L hL base
    (fun k : {T // T ∈ Kpos} => k.val) hCard hFree P κ hκ hN hP
  refine ⟨f,hf,?_⟩
  have hCover := sum_mode_cost_le_support_potential R (newSupportTriples base f) base f
    (fun Q hQ => (mem_powersetCard.mp (mem_filter.mp hQ).1).2)
    (fun Q hQ => (mem_powersetCard.mp (mem_filter.mp hQ).1).1)
    (fun Q hQ => (mem_filter.mp hQ).2)
  have hCoverReal : (∑ Q ∈ newSupportTriples base f, (rootedCount (insert Q R) Q:ℝ)) ≤
      ∑ T ∈ Kpos, (rootedCount (insert (T.image (Sum.elim base f)) R)
        (T.image (Sum.elim base f)):ℝ) := by exact_mod_cast hCover
  have hCostReal : (∑ T ∈ Kpos, (rootedCount (insert (T.image (Sum.elim base f)) R)
        (T.image (Sum.elim base f)):ℝ)) ≤ ((Kpos.card:ℝ)*(L:ℝ)^3)/κ := by
    have hUniv : (univ : Finset {T // T ∈ Kpos}) = Kpos.attach := by ext k; simp
    change (∑ k ∈ (univ : Finset {T // T ∈ Kpos}),
      (rootedCount (insert (k.val.image (Sum.elim base f)) R)
        (k.val.image (Sum.elim base f)):ℝ)) ≤ _ at hCost
    rw [hUniv,sum_attach Kpos (fun T => (rootedCount
      (insert (T.image (Sum.elim base f)) R) (T.image (Sum.elim base f)):ℝ))] at hCost
    simpa only [Fintype.card_coe] using hCost
  have hK : (Kpos.card:ℝ) ≤ (Nat.choose (Fintype.card A+Fintype.card J) 3:ℝ) := by
    exact_mod_cast (freePositionTriples_card_le (A := A) (J := J))
  exact (hCoverReal.trans hCostReal).trans (div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_right hK (by positivity)) hκ.le)

#print axioms support_triple_has_position_preimage
#print axioms sum_mode_cost_le_support_potential
#print axioms freePositionTriples_card_le
#print axioms exists_low_support_increment
end TypedTriangle.Pasch
