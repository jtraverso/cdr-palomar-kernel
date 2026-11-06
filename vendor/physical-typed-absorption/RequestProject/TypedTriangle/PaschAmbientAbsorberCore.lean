module
public import RequestProject.TypedTriangle.PaschWeightedSlotAbsorber
public import RequestProject.TypedTriangle.PaschSeededPotential
public import RequestProject.TypedTriangle.PaschAmbientSupportPotential
public import RequestProject.TypedTriangle.PaschSupportCoverage
public import RequestProject.TypedTriangle.PaschHostDensity
public import RequestProject.TypedTriangle.PaschHingeAssignmentFamilies
public import RequestProject.TypedTriangle.PaschSurvivingCertificateLift
set_option maxHeartbeats 4000000 -- build option (original: -DmaxHeartbeats=1600000; raised)
set_option maxRecDepth 16384 -- build option (original: -DmaxRecDepth=8192; raised)
@[expose] public section
open Finset Classical
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000

namespace TypedTriangle.Pasch.Ambient
variable {V W : Type*} [Fintype V] [Fintype W]

def orderRatio (_ι : V ↪ W) : ℝ := (Fintype.card W:ℝ)/Fintype.card V

def supportIncrementCost (ι : V ↪ W) (R : Finset (Finset W)) (U Z : Finset V) : ℕ :=
  Pasch.supportIncrementCost R (U.map ι) (Z.map ι)

theorem supportIncrementCost_self (ι : V ↪ W) (R : Finset (Finset W)) (U : Finset V) :
    supportIncrementCost ι R U U=0 := Pasch.supportIncrementCost_self R (U.map ι)

theorem supportIncrementCost_union (ι : V ↪ W) (R : Finset (Finset W)) (U Z1 Z2 : Finset V) :
    supportIncrementCost ι R U (Z1∪Z2)=
      supportIncrementCost ι R U Z1+supportIncrementCost ι R (U∪Z1) Z2 := by
  simp only [supportIncrementCost,map_union]
  exact Pasch.supportIncrementCost_union R (U.map ι) (Z1.map ι) (Z2.map ι)

theorem supportIncrementCost_mono (ι : V ↪ W) (R : Finset (Finset W)) (U : Finset V)
    {Z Z' : Finset V} (hZ : Z ⊆ Z') :
    supportIncrementCost ι R U Z ≤ supportIncrementCost ι R U Z' :=
  Pasch.supportIncrementCost_mono R (U.map ι) (map_subset_map.mpr hZ)

theorem orderRatio_nonneg (ι : V ↪ W) : 0 ≤ orderRatio ι := by unfold orderRatio; positivity

theorem orderRatio_one_le (ι : V ↪ W) (hn : 0<(Fintype.card V:ℝ)) : 1 ≤ orderRatio ι := by
  apply (le_div_iff₀ hn).mpr
  have hh : Fintype.card V ≤ Fintype.card W := Fintype.card_le_of_injective ι ι.injective
  simpa only [one_mul] using (show (Fintype.card V:ℝ) ≤ Fintype.card W by exact_mod_cast hh)

def apexPotentialCost (ι : V ↪ W) (α : ℝ) (Ub L : ℕ) : ℝ :=
  orderRatio ι*((Ub:ℝ)^2*(L:ℝ)^3/(α/2))

def hingePotentialCost (ι : V ↪ W) (α : ℝ) (h Ub L : ℕ) : ℝ :=
  orderRatio ι*((Nat.choose (Ub+h) 3:ℝ)*(2*(2:ℝ)^Nat.choose h 2)*(L:ℝ)^3/α)

def compositePotentialCost (ι : V ↪ W) (α : ℝ) (h Ub L : ℕ) : ℝ :=
  apexPotentialCost ι α Ub L+hingePotentialCost ι α h (Ub+1) L+
    hingePotentialCost ι α h (Ub+1+h) L

def gadgetPotentialCost (ι : V ↪ W) (α : ℝ) (h Ub L : ℕ) : ℝ :=
  apexPotentialCost ι α Ub L+compositePotentialCost ι α h (Ub+1) L

def absorptionPotentialCost (ι : V ↪ W) (α : ℝ) (h Ub L : ℕ) : ℝ :=
  gadgetPotentialCost ι α h Ub L+3*compositePotentialCost ι α h Ub L

theorem compositePotentialCost_factor (ι : V ↪ W) (α : ℝ) (h Ub L : ℕ) :
    compositePotentialCost ι α h Ub L=orderRatio ι*Pasch.compositePotentialCost α h Ub L := by
  unfold compositePotentialCost apexPotentialCost hingePotentialCost Pasch.compositePotentialCost Pasch.hingePotentialCost
  ring

theorem gadgetPotentialCost_factor (ι : V ↪ W) (α : ℝ) (h Ub L : ℕ) :
    gadgetPotentialCost ι α h Ub L=orderRatio ι*Pasch.gadgetPotentialCost α h Ub L := by
  unfold gadgetPotentialCost apexPotentialCost
  rw [compositePotentialCost_factor]
  unfold Pasch.gadgetPotentialCost
  ring

theorem absorptionPotentialCost_factor (ι : V ↪ W) (α : ℝ) (h Ub L : ℕ) :
    absorptionPotentialCost ι α h Ub L=orderRatio ι*Pasch.absorptionPotentialCost α h Ub L := by
  unfold absorptionPotentialCost Pasch.absorptionPotentialCost
  rw [gadgetPotentialCost_factor,compositePotentialCost_factor]
  ring

theorem supportIncrementCost_apex_le_pair_sum (ι : V ↪ W) (R : Finset (Finset W))
    (S : Finset V) (t : V) : supportIncrementCost ι R S {t} ≤
      ∑ p : S×S, rootedCount (insert {ι p.1.val,ι p.2.val,ι t} R) {ι p.1.val,ι p.2.val,ι t} := by
  let f : S → S.map ι := fun x => ⟨ι x.val,mem_map.mpr ⟨x.val,x.property,rfl⟩⟩
  have hf : Function.Bijective f := by
    constructor
    · intro x y hxy
      exact Subtype.ext (ι.injective (congrArg Subtype.val hxy))
    · intro y
      obtain ⟨x,hx,hxy⟩ := mem_map.mp y.property
      exact ⟨⟨x,hx⟩,Subtype.ext hxy⟩
  let eqv := Equiv.ofBijective f hf
  let pairEqv := Equiv.prodCongr eqv eqv
  have hSum : (∑ p : S×S, rootedCount
      (insert {ι p.1.val,ι p.2.val,ι t} R) {ι p.1.val,ι p.2.val,ι t}) =
      ∑ p : (S.map ι)×(S.map ι), rootedCount
        (insert {p.1.val,p.2.val,ι t} R) {p.1.val,p.2.val,ι t} :=
    Equiv.sum_comp pairEqv (fun p : (S.map ι)×(S.map ι) =>
      rootedCount (insert {p.1.val,p.2.val,ι t} R) {p.1.val,p.2.val,ι t})
  have hh := Pasch.supportIncrementCost_apex_le_pair_sum R (S.map ι) (ι t)
  change Pasch.supportIncrementCost R (S.map ι) (({t}:Finset V).map ι) ≤ _
  rw [map_singleton]
  exact hh.trans_eq hSum.symm

end TypedTriangle.Pasch.Ambient
#print axioms TypedTriangle.Pasch.Ambient.supportIncrementCost_union
#print axioms TypedTriangle.Pasch.Ambient.absorptionPotentialCost_factor
#print axioms TypedTriangle.Pasch.Ambient.supportIncrementCost_apex_le_pair_sum


namespace TypedTriangle.Pasch
variable {A J K X V : Type*} [DecidableEq A] [DecidableEq J] [DecidableEq X] [DecidableEq V]
  [Fintype J] [Fintype X] [Fintype V] [Fintype K]

/-- Free positions are sampled in X; every completion is still counted in
the full ambient family R. No part of R is pulled back to X. -/
theorem exists_low_embedded_potential_for_support_triples
    (ι : X ↪ V) (R : Finset (Finset V)) (L : ℕ) (hL : PairCodegreeBound R L)
    (base : A → X) (T : K → Finset (A⊕J)) (hT : ∀ k, (T k).card=3)
    (hFree : ∀ k, ∃ i : J, Sum.inr i ∈ T k)
    (P : Finset (J → X)) (κ : ℝ) (hκ : 0<κ) (hnX : 0<(Fintype.card X:ℝ))
    (hP : κ*(Fintype.card (J → X):ℝ) ≤ P.card) :
    ∃ f ∈ P, ((∑ k : K, rootedCount
      (insert ((T k).image (fun p => ι (Sum.elim base f p))) R)
      ((T k).image (fun p => ι (Sum.elim base f p)))):ℝ) ≤
        ((Fintype.card V:ℝ)/Fintype.card X)*((Fintype.card K:ℝ)*(L:ℝ)^3)/κ := by
  obtain ⟨i,a,b,hForm⟩ := indexed_support_free_forms base T hT hFree
  let av := fun k r => ι (a k r)
  let bv := fun k r => ι (b k r)
  obtain ⟨f,hf,hCost⟩ := exists_low_embedded_support_potential ι R L hL i av bv P κ hκ hnX hP
  have hFormV (k : K) : (T k).image (fun p => ι (Sum.elim base f p)) =
      {ι (a k (fun j => f j.val)),ι (b k (fun j => f j.val)),ι (f (i k))} := by
    have hh := congrArg (fun S : Finset X => S.image ι) (hForm k f)
    simpa only [image_image,Function.comp_def,image_insert,image_singleton] using hh
  have hEq : (∑ k : K, rootedCount
      (insert ((T k).image (fun p => ι (Sum.elim base f p))) R)
      ((T k).image (fun p => ι (Sum.elim base f p)))) =
      embeddedSupportCompletionCost ι R i av bv f := by
    unfold embeddedSupportCompletionCost
    apply sum_congr rfl
    intro k _
    rw [hFormV k]
  refine ⟨f,hf,?_⟩
  rw [←Nat.cast_sum,hEq]
  exact hCost

/-- The selected assignment pays every ambient triple newly supported by the
cell, using the same actual candidate family P from the local host. -/
theorem exists_low_embedded_support_increment [Fintype A]
    (ι : X ↪ V) (R : Finset (Finset V)) (L : ℕ) (hL : PairCodegreeBound R L)
    (base : A → X) (P : Finset (J → X)) (κ : ℝ) (hκ : 0<κ)
    (hnX : 0<(Fintype.card X:ℝ)) (hP : κ*(Fintype.card (J → X):ℝ) ≤ P.card) :
    ∃ f ∈ P, (∑ Q ∈ newSupportTriples (ι ∘ base) (ι ∘ f), (rootedCount (insert Q R) Q:ℝ)) ≤
      ((Fintype.card V:ℝ)/Fintype.card X)*
        ((Nat.choose (Fintype.card A+Fintype.card J) 3:ℝ)*(L:ℝ)^3)/κ := by
  let Kpos := freePositionTriples A J
  have hCard (k : {T // T∈Kpos}) : k.val.card=3 :=
    (mem_powersetCard.mp (mem_filter.mp k.property).1).2
  have hFree (k : {T // T∈Kpos}) : ∃ j : J, Sum.inr j∈k.val :=
    (mem_filter.mp k.property).2
  obtain ⟨f,hf,hCost⟩ := exists_low_embedded_potential_for_support_triples ι R L hL base
    (fun k : {T // T∈Kpos} => k.val) hCard hFree P κ hκ hnX hP
  have hEval : Sum.elim (ι ∘ base) (ι ∘ f) = fun p => ι (Sum.elim base f p) := by
    funext p
    cases p <;> rfl
  have hCover := sum_mode_cost_le_support_potential R
    (newSupportTriples (ι ∘ base) (ι ∘ f)) (ι ∘ base) (ι ∘ f)
    (fun Q hQ => (mem_powersetCard.mp (mem_filter.mp hQ).1).2)
    (fun Q hQ => (mem_powersetCard.mp (mem_filter.mp hQ).1).1)
    (fun Q hQ => (mem_filter.mp hQ).2)
  have hCoverR : (∑ Q ∈ newSupportTriples (ι ∘ base) (ι ∘ f), (rootedCount (insert Q R) Q:ℝ)) ≤
      ∑ T ∈ Kpos, (rootedCount (insert (T.image (Sum.elim (ι ∘ base) (ι ∘ f))) R)
        (T.image (Sum.elim (ι ∘ base) (ι ∘ f))):ℝ) := by exact_mod_cast hCover
  have hCostR : (∑ T ∈ Kpos, (rootedCount (insert (T.image (Sum.elim (ι ∘ base) (ι ∘ f))) R)
      (T.image (Sum.elim (ι ∘ base) (ι ∘ f))):ℝ)) ≤
      ((Fintype.card V:ℝ)/Fintype.card X)*((Kpos.card:ℝ)*(L:ℝ)^3)/κ := by
    have hUniv : (univ : Finset {T // T∈Kpos})=Kpos.attach := by ext k; simp
    change (∑ k ∈ (univ : Finset {T // T∈Kpos}),
      (rootedCount (insert (k.val.image (fun p => ι (Sum.elim base f p))) R)
        (k.val.image (fun p => ι (Sum.elim base f p))):ℝ)) ≤ _ at hCost
    rw [hUniv,sum_attach Kpos (fun T => (rootedCount
      (insert (T.image (fun p => ι (Sum.elim base f p))) R)
      (T.image (fun p => ι (Sum.elim base f p))):ℝ))] at hCost
    simpa only [hEval,Fintype.card_coe] using hCost
  have hK : (Kpos.card:ℝ) ≤ (Nat.choose (Fintype.card A+Fintype.card J) 3:ℝ) := by
    exact_mod_cast (freePositionTriples_card_le (A:=A) (J:=J))
  have hRatio : 0 ≤ (Fintype.card V:ℝ)/Fintype.card X := by positivity
  refine ⟨f,hf,(hCoverR.trans hCostR).trans ?_⟩
  exact div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hK (by positivity)) hRatio) hκ.le

#print axioms exists_low_embedded_potential_for_support_triples
#print axioms exists_low_embedded_support_increment
end TypedTriangle.Pasch


namespace TypedTriangle.Pasch.Ambient
variable {V Ω K : Type*} [Fintype V] [Fintype Ω] [Fintype K]

theorem exists_apex_total_cost_in_pool (ι : V ↪ Ω) [DecidableEq V] (R : Finset (Finset Ω)) (L : ℕ)
    (hL : PairCodegreeBound R L) (p q : K → V) (W : Finset V) (κ : ℝ)
    (hκ : 0 < κ) (hn : 0 < (Fintype.card V:ℝ)) (hW : κ*(Fintype.card V:ℝ) ≤ W.card) :
    ∃ x ∈ W, ((∑ k : K, rootedCount (insert {ι (p k),ι (q k),ι x} R) {ι (p k),ι (q k),ι x}):ℝ) ≤
      orderRatio ι*((Fintype.card K:ℝ)*(L:ℝ)^3)/κ := by
  let P : Finset (Unit → V) := W.image (fun x _ => x)
  let i : K → Unit := fun _ => ()
  let a : ∀ k, ({j : Unit // j ≠ i k} → V) → Ω := fun k _ => ι (p k)
  let b : ∀ k, ({j : Unit // j ≠ i k} → V) → Ω := fun k _ => ι (q k)
  have hCard : P.card = W.card := by
    apply card_image_of_injective
    intro x y h
    exact congrFun h ()
  have hN : 0 < (Fintype.card (Unit → V):ℝ) := by simpa using hn
  have hP : κ*(Fintype.card (Unit → V):ℝ) ≤ P.card := by
    rw [hCard]
    simpa using hW
  obtain ⟨f,hf,hCost⟩ := exists_low_embedded_support_potential ι R L hL i a b P κ hκ hn hP
  obtain ⟨x,hx,hxf⟩ := mem_image.mp hf
  have hfx : f () = x := (congrFun hxf ()).symm
  refine ⟨x,hx,?_⟩
  simpa only [embeddedSupportCompletionCost,i,a,b,hfx,Nat.cast_sum,orderRatio] using hCost

/-- H3 chooses one actual fresh apex paying the sum of all indicated
support-pair costs. The old family R is fixed before the apex is chosen. -/
theorem exists_low_total_cost_fresh_apex (ι : V ↪ Ω) {I : Type*} {H : Host V I}
    {F : Set (Multiset I)} {α : ℝ} (hα : 0 < α) (hH3 : CommonNbrCond H F α)
    {a b c : V} (hT : IsAllowed H F {a,b,c}) (R : Finset (Finset Ω)) (L : ℕ)
    (hL : PairCodegreeBound R L) (p q : K → V) (B : Finset (Sym2 V)) (d : ℕ)
    (hdeg : ∀ v, degIn B v ≤ d) (Z : Finset V)
    (hwin : (Z.card:ℝ)+2*d ≤ α/2*Fintype.card V) :
    ∃ x : V, x ∉ Z ∧ IsAllowed H F {a,b,x} ∧ s(a,x) ∉ B ∧ s(b,x) ∉ B ∧
      ((∑ k : K, rootedCount (insert {ι (p k),ι (q k),ι x} R) {ι (p k),ι (q k),ι x}):ℝ) ≤
        orderRatio ι*((Fintype.card K:ℝ)*(L:ℝ)^3)/(α/2) := by
  let bad := (Z ∪ nbrIn B a) ∪ nbrIn B b
  let W := commonNbrs H (H.lab c) a b \ bad
  have hbadNat : bad.card ≤ Z.card+2*d := by
    have ha := (card_nbrIn_le B a).trans (hdeg a)
    have hb := (card_nbrIn_le B b).trans (hdeg b)
    exact ((card_union_le _ _).trans (Nat.add_le_add_right (card_union_le _ _) _)).trans (by omega)
  have hbad : (bad.card:ℝ) ≤ (Z.card:ℝ)+2*d := by exact_mod_cast hbadNat
  have hcover : commonNbrs H (H.lab c) a b ⊆ W ∪ bad := by
    intro x hx
    by_cases hxb : x ∈ bad
    · exact mem_union_right _ hxb
    · exact mem_union_left _ (mem_sdiff.mpr ⟨hx,hxb⟩)
  have hcountNat : (commonNbrs H (H.lab c) a b).card ≤ W.card+bad.card :=
    (card_le_card hcover).trans (card_union_le _ _)
  have hcount : ((commonNbrs H (H.lab c) a b).card:ℝ) ≤ W.card+bad.card := by
    exact_mod_cast hcountNat
  have hH3count := commonNbr_card_lower hH3 hT
  have hW : α/2*(Fintype.card V:ℝ) ≤ W.card := by
    linarith only [hcount,hH3count,hbad,hwin]
  have hnNat : 0 < Fintype.card V := by
    have hCard : 3 ≤ Fintype.card V := hT.1 ▸ card_le_univ ({a,b,c}:Finset V)
    omega
  have hn : (0:ℝ) < Fintype.card V := by exact_mod_cast hnNat
  obtain ⟨x,hx,hCost⟩ := exists_apex_total_cost_in_pool ι R L hL p q W (α/2) (by positivity) hn hW
  obtain ⟨hxCommon,hxBad⟩ := mem_sdiff.mp hx
  have hxZ : x ∉ Z := fun h => hxBad (mem_union_left _ (mem_union_left _ h))
  have hxA : s(a,x) ∉ B := by
    intro h
    exact hxBad (mem_union_left _ (mem_union_right _ (mem_filter.mpr ⟨mem_univ _,h⟩)))
  have hxB : s(b,x) ∉ B := by
    intro h
    exact hxBad (mem_union_right _ (mem_filter.mpr ⟨mem_univ _,h⟩))
  exact ⟨x,hxZ,allowed_of_commonNbr hT hxCommon,hxA,hxB,hCost⟩

#print axioms exists_apex_total_cost_in_pool
#print axioms exists_low_total_cost_fresh_apex
end TypedTriangle.Pasch.Ambient


namespace TypedTriangle.Pasch.Ambient
variable {V Ω I : Type*} [Fintype V] [Fintype Ω]

/-- The actual robust H4 family supplies a low-potential hinge. R is the
fixed previous mode universe; all triples newly added to the old support are paid together. -/
theorem exists_low_cost_robust_hinge (ι : V ↪ Ω) {H : Host V I} {F : Set (Multiset I)}
    {α : ℝ} {h : ℕ} (hα : 0 < α) (hH4 : HingeCond H F α h)
    {u v a b : V} (hab : a ≠ b)
    (hTa : IsAllowed H F {u,v,a}) (hTb : IsAllowed H F {u,v,b})
    (R : Finset (Finset Ω)) (L : ℕ) (hL : PairCodegreeBound R L)
    (U : Finset V) (Ub : ℕ) (hU : U.card ≤ Ub) (hRoots : ({u,v,a,b}:Finset V) ⊆ U)
    (Z : Finset V) (B : Finset (Sym2 V)) (d : ℕ) (hdeg : ∀ x, degIn B x ≤ d)
    (hB : s(a,b) ∉ B) (hWin : ((Z.card:ℝ)+5*d)*2^Nat.choose h 2 ≤ α/2*Fintype.card V) :
    ∃ i : ℕ, 6 ≤ i ∧ i ≤ h ∧ ∃ J ∈ hinges H F u v a b i,
      (∀ z ∈ Z, z ∈ support J → z ∈ ({u,v,a,b}:Finset V)) ∧ Disjoint J B ∧
      (supportIncrementCost ι R U (support J):ℝ) ≤ hingePotentialCost ι α h Ub L := by
  obtain ⟨i,hi6,hih,P,hMass,hWitness⟩ := exists_robust_hinge_assignment_family
    hα hH4 hab hTa hTb Z B d hdeg hB hWin
  let A := {v // v ∈ U}
  let base : A → V := Subtype.val
  have hBase : univ.image base = U := by
    ext x
    constructor
    · intro hx
      obtain ⟨y,_,rfl⟩ := mem_image.mp hx
      exact y.property
    · intro hx
      exact mem_image.mpr ⟨⟨x,hx⟩,mem_univ _,rfl⟩
  let κ : ℝ := α/(2*(2:ℝ)^Nat.choose i 2)
  have hκ : 0 < κ := by dsimp only [κ]; positivity
  have hnNat : 0 < Fintype.card V := Fintype.card_pos_iff.mpr ⟨u⟩
  have hn : (0:ℝ) < Fintype.card V := by exact_mod_cast hnNat
  have hN : (0:ℝ) < Fintype.card (Fin (i-4) → V) := by
    simpa only [Fintype.card_fun,Fintype.card_fin,Nat.cast_pow] using pow_pos hn (i-4)
  have hPool : κ*(Fintype.card (Fin (i-4) → V):ℝ) ≤ P.card := by
    simpa only [κ,Fintype.card_fun,Fintype.card_fin,Nat.cast_pow] using hMass
  obtain ⟨f,hf,hCost⟩ := exists_low_embedded_support_increment ι R L hL base P κ hκ hn hPool
  obtain ⟨_,_,J,hJ,hFresh,hJB,hFull⟩ := hWitness f hf
  have hUnion : U ∪ support J = U ∪ univ.image f := by
    rw [hFull,←union_assoc,union_eq_left.mpr hRoots]
  have hBaseAmbient : univ.image (ι ∘ base)=U.map ι := by
    calc univ.image (ι ∘ base) = (univ.image base).map ι := by
          rw [map_eq_image,image_image]
      _ = U.map ι := by rw [hBase]
  have hFreeAmbient : univ.image (ι ∘ f)=(univ.image f).map ι := by
    rw [map_eq_image,image_image]
  have hUnionAmbient : U.map ι∪(support J).map ι=U.map ι∪(univ.image f).map ι := by
    rw [←map_union, hUnion, map_union]
  have hNew : ((U.map ι∪(support J).map ι).powersetCard 3).filter (fun Q => ¬ Q ⊆ U.map ι) =
      newSupportTriples (ι ∘ base) (ι ∘ f) := by
    unfold newSupportTriples
    rw [hBaseAmbient,hFreeAmbient,hUnionAmbient]
  have hActual : (supportIncrementCost ι R U (support J):ℝ) =
      ∑ Q ∈ newSupportTriples (ι ∘ base) (ι ∘ f), (rootedCount (insert Q R) Q:ℝ) := by
    unfold supportIncrementCost Pasch.supportIncrementCost
    rw [hNew,Nat.cast_sum]
  have hCost' : (∑ Q ∈ newSupportTriples (ι ∘ base) (ι ∘ f), (rootedCount (insert Q R) Q:ℝ)) ≤
      orderRatio ι*((Nat.choose (U.card+(i-4)) 3:ℝ)*(L:ℝ)^3)/κ := by
    simpa only [A,Fintype.card_coe,Fintype.card_fin,orderRatio] using hCost
  have hChooseNat : Nat.choose (U.card+(i-4)) 3 ≤ Nat.choose (Ub+h) 3 :=
    Nat.choose_le_choose 3 (Nat.add_le_add hU ((Nat.sub_le i 4).trans hih))
  have hChoose : (Nat.choose (U.card+(i-4)) 3:ℝ) ≤ (Nat.choose (Ub+h) 3:ℝ) := by
    exact_mod_cast hChooseNat
  have hPow : (2:ℝ)^Nat.choose i 2 ≤ (2:ℝ)^Nat.choose h 2 :=
    pow_le_pow_right₀ (by norm_num) (Nat.choose_le_choose 2 hih)
  have hNumer : (Nat.choose (U.card+(i-4)) 3:ℝ)*(2*(2:ℝ)^Nat.choose i 2)*(L:ℝ)^3 ≤
      (Nat.choose (Ub+h) 3:ℝ)*(2*(2:ℝ)^Nat.choose h 2)*(L:ℝ)^3 := by
    apply mul_le_mul_of_nonneg_right _ (by positivity)
    exact mul_le_mul hChoose (mul_le_mul_of_nonneg_left hPow (by norm_num))
      (by positivity) (by positivity)
  have hUniform : ((Nat.choose (U.card+(i-4)) 3:ℝ)*(L:ℝ)^3)/κ ≤ Pasch.hingePotentialCost α h Ub L := by
    calc ((Nat.choose (U.card+(i-4)) 3:ℝ)*(L:ℝ)^3)/κ
        = ((Nat.choose (U.card+(i-4)) 3:ℝ)*(2*(2:ℝ)^Nat.choose i 2)*(L:ℝ)^3)/α := by
          dsimp only [κ]
          field_simp [ne_of_gt hα,ne_of_gt (pow_pos (by norm_num : (0:ℝ)<2) (Nat.choose i 2))] <;> ring
      _ ≤ Pasch.hingePotentialCost α h Ub L := div_le_div_of_nonneg_right hNumer hα.le
  have hScaled : orderRatio ι*(((Nat.choose (U.card+(i-4)) 3:ℝ)*(L:ℝ)^3)/κ) ≤
      hingePotentialCost ι α h Ub L :=
    mul_le_mul_of_nonneg_left hUniform (orderRatio_nonneg ι)
  have hCostRatio : (∑ Q ∈ newSupportTriples (ι ∘ base) (ι ∘ f), (rootedCount (insert Q R) Q:ℝ)) ≤
      orderRatio ι*(((Nat.choose (U.card+(i-4)) 3:ℝ)*(L:ℝ)^3)/κ) := by
    convert hCost' using 1 <;> ring
  exact ⟨i,hi6,hih,J,hJ,hFresh,hJB,hActual.trans_le (hCostRatio.trans hScaled)⟩

#print axioms exists_low_cost_robust_hinge
end TypedTriangle.Pasch.Ambient


namespace TypedTriangle.Pasch.Ambient
variable {V Ω I : Type*} [Fintype V] [Fintype Ω]

/-- A robust composite hinge, selected with the concrete support potential.
The local bounded support S is separate from the global forbidden history U. -/
theorem exists_low_cost_robust_composite_hinge (ι : V ↪ Ω) {H : Host V I} {F : Set (Multiset I)}
    {α : ℝ} {h : ℕ} (hα : 0 < α) (hH3 : CommonNbrCond H F α) (hH4 : HingeCond H F α h)
    {u v a b : V} (hab : a ≠ b) (hTa : IsAllowed H F {u,v,a}) (hTb : IsAllowed H F {u,v,b})
    (R : Finset (Finset Ω)) (L : ℕ) (hL : PairCodegreeBound R L)
    (S : Finset V) (Ub : ℕ) (hS : S.card ≤ Ub) (hRoots : ({u,v,a,b}:Finset V) ⊆ S)
    (U : Finset V) (B : Finset (Sym2 V)) (d : ℕ) (hdeg : ∀ x, degIn B x ≤ d)
    (hwin1 : (U.card:ℝ)+2+4*d ≤ α/2*Fintype.card V)
    (hwin2 : ((U.card:ℝ)+h+5*d)*2^Nat.choose h 2 ≤ α/2*Fintype.card V) :
    ∃ J, IsHinge H F u v a b J ∧ Disjoint J B ∧ s(a,b) ∉ J ∧
      (∀ z ∈ U, z ∈ support J → z ∈ ({u,v,a,b}:Finset V)) ∧
      (support J).card ≤ 2*h-3 ∧
      (supportIncrementCost ι R S (support J):ℝ) ≤ compositePotentialCost ι α h Ub L := by
  obtain ⟨huv,hua,hva⟩ := distinct_of_card_three hTa.1
  obtain ⟨_,hub,hvb⟩ := distinct_of_card_three hTb.1
  let X := (U ∪ {a,b}) ∪ (nbrIn B a ∪ nbrIn B b)
  have hXNat : X.card ≤ U.card+2+2*d := by
    have ha := (card_nbrIn_le B a).trans (hdeg a)
    have hb := (card_nbrIn_le B b).trans (hdeg b)
    have h1 : (U ∪ {a,b}).card ≤ U.card+2 :=
      (card_union_le _ _).trans (Nat.add_le_add_left card_le_two _)
    have h2 : (nbrIn B a ∪ nbrIn B b).card ≤ 2*d := (card_union_le _ _).trans (by omega)
    exact (card_union_le _ _).trans (by omega)
  have hXReal : (X.card:ℝ) ≤ (U.card:ℝ)+2+2*d := by exact_mod_cast hXNat
  have hMargin : (X.card:ℝ)+2*d ≤ α/2*Fintype.card V := by linarith only [hXReal,hwin1]
  let p : S × S → V := fun x => x.1.val
  let q : S × S → V := fun x => x.2.val
  obtain ⟨t,htX,hTt,htBu,htBv,hPair⟩ := exists_low_total_cost_fresh_apex ι
    hα hH3 hTa R L hL p q B d hdeg X hMargin
  have hApex0 : (supportIncrementCost ι R S {t}:ℝ) ≤
      orderRatio ι*((S.card:ℝ)^2*(L:ℝ)^3/(α/2)) := by
    have hNatural := supportIncrementCost_apex_le_pair_sum ι R S t
    have hReal : (supportIncrementCost ι R S {t}:ℝ) ≤
        ∑ p : S×S, (rootedCount (insert {ι p.1.val,ι p.2.val,ι t} R)
          {ι p.1.val,ι p.2.val,ι t}:ℝ) := by exact_mod_cast hNatural
    have hPairNorm : (∑ p : S×S, (rootedCount
        (insert {ι p.1.val,ι p.2.val,ι t} R) {ι p.1.val,ι p.2.val,ι t}:ℝ)) ≤
        orderRatio ι*((S.card:ℝ)^2*(L:ℝ)^3/(α/2)) := by
      convert hPair using 1 <;>
        simp only [p,q,Fintype.card_prod,Fintype.card_coe,Nat.cast_mul,Nat.cast_sum,pow_two] <;> ring
    exact hReal.trans hPairNorm
  have hApex : (supportIncrementCost ι R S {t}:ℝ) ≤ apexPotentialCost ι α Ub L := by
    have hsPow : (S.card:ℝ)^2 ≤ (Ub:ℝ)^2 := by exact_mod_cast Nat.pow_le_pow_left hS 2
    exact hApex0.trans (mul_le_mul_of_nonneg_left
      (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hsPow (by positivity)) (by positivity))
      (orderRatio_nonneg ι))
  obtain ⟨_,hut,hvt⟩ := distinct_of_card_three hTt.1
  simp only [X,mem_union,mem_insert,mem_singleton,not_or,nbrIn,mem_filter,mem_univ,true_and] at htX
  obtain ⟨⟨htU,hta,htb⟩,htBa,htBb⟩ := htX
  have hat : a ≠ t := Ne.symm hta
  have hbt : b ≠ t := Ne.symm htb
  have hnB : ∀ x, s(x,t) ∉ B → s(t,x) ∉ B := fun x hx => by rwa [Sym2.eq_swap]
  let S1 := insert t S
  have hS1 : S1.card ≤ Ub+1 := (card_insert_le t S).trans (Nat.add_le_add_right hS 1)
  have hRoots1 : ({u,v,a,t}:Finset V) ⊆ S1 := by
    intro x hx
    simp only [mem_insert,mem_singleton] at hx
    rcases hx with rfl | rfl | rfl | rfl
    · exact mem_insert_of_mem (hRoots (by simp))
    · exact mem_insert_of_mem (hRoots (by simp))
    · exact mem_insert_of_mem (hRoots (by simp))
    · exact mem_insert_self _ _
  -- 2. primera bisagra `H₁ : uva → uvt`
  have hwinZ1 : (((insert b U).card : ℝ) + 5 * d) * 2 ^ Nat.choose h 2 ≤
      α / 2 * Fintype.card V := by
    have : ((insert b U).card : ℝ) ≤ U.card + h := by
      have := Finset.card_insert_le b U
      have h6 : (1 : ℝ) ≤ h := by
        obtain ⟨i, hi6, hih, -⟩ := hH4 u v a b hab hTa hTb
        exact_mod_cast (show 1 ≤ h by omega)
      have : ((insert b U).card : ℝ) ≤ U.card + 1 := by exact_mod_cast this
      linarith
    refine le_trans ?_ hwin2
    exact mul_le_mul_of_nonneg_right (by linarith) (by positivity)
  obtain ⟨i₁, _, hi₁h, H₁, hH₁, hH₁Z, hH₁B, hPay₁⟩ :=
    exists_low_cost_robust_hinge ι hα hH4 hat hTa hTt R L hL S1 (Ub+1) hS1 hRoots1
      (insert b U) B d hdeg htBa hwinZ1
  simp only [hinges, Finset.mem_filter, Finset.mem_univ, true_and] at hH₁
  have hb1 : b ∉ support H₁ := by
    intro hb
    have := hH₁Z b (Finset.mem_insert_self _ _) hb
    simp only [Finset.mem_insert, Finset.mem_singleton] at this
    rcases this with h' | h' | h' | h'
    exacts [hub h'.symm, hvb h'.symm, hab h'.symm, hbt h']
  -- 3. segunda bisagra `H₂ : uvt → uvb`
  set Z₂ := U ∪ (support H₁).filter (fun x => x ∉ ({u, v, t} : Finset V)) with hZ₂
  have hR1 := (hinge_order_ge_six hat hTa hTt hH₁.1).1
  have hZ₂c : (Z₂.card : ℝ) ≤ U.card + h := by
    have h3 : ({u, v, t} : Finset V).card = 3 := hTt.1
    have hfilt : ((support H₁).filter (fun x => x ∉ ({u, v, t} : Finset V))).card + 3 ≤
        (support H₁).card := by
      have hsplit := Finset.card_filter_add_card_filter_not (s := support H₁)
        (fun x => x ∉ ({u, v, t} : Finset V))
      have hsub : ({u, v, t} : Finset V) ⊆ (support H₁).filter
          (fun x => ¬ x ∉ ({u, v, t} : Finset V)) := by
        intro x hx
        refine Finset.mem_filter.2 ⟨hR1 ?_, fun h' => h' hx⟩
        simp only [Finset.mem_insert, Finset.mem_singleton] at hx ⊢; tauto
      have := Finset.card_le_card hsub
      omega
    have : Z₂.card ≤ U.card + h := by
      refine (Finset.card_union_le _ _).trans ?_
      omega
    exact_mod_cast this
  have hwinZ2 : ((Z₂.card : ℝ) + 5 * d) * 2 ^ Nat.choose h 2 ≤ α / 2 * Fintype.card V :=
    le_trans (mul_le_mul_of_nonneg_right (by linarith) (by positivity)) hwin2
  let S2 := S1 ∪ support H₁
  have hS2 : S2.card ≤ Ub+1+h := (card_union_le _ _).trans
    (Nat.add_le_add hS1 (hH₁.2.le.trans hi₁h))
  have hRoots2 : ({u,v,t,b}:Finset V) ⊆ S2 := by
    intro x hx
    apply mem_union_left
    simp only [mem_insert,mem_singleton] at hx
    rcases hx with rfl | rfl | rfl | rfl
    · exact mem_insert_of_mem (hRoots (by simp))
    · exact mem_insert_of_mem (hRoots (by simp))
    · exact mem_insert_self _ _
    · exact mem_insert_of_mem (hRoots (by simp))
  obtain ⟨i₂, _, hi₂h, H₂, hH₂, hH₂Z, hH₂B, hPay₂⟩ :=
    exists_low_cost_robust_hinge ι hα hH4 hbt.symm hTt hTb R L hL S2 (Ub+1+h) hS2 hRoots2
      Z₂ B d hdeg (hnB b htBb) hwinZ2
  simp only [hinges, Finset.mem_filter, Finset.mem_univ, true_and] at hH₂
  have ha2 : a ∉ support H₂ := by
    intro ha
    have haZ : a ∈ Z₂ := Finset.mem_union_right _ (Finset.mem_filter.2 ⟨hR1 (by simp), by
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or]; exact ⟨hua.symm, hva.symm, hat⟩⟩)
    have := hH₂Z a haZ ha
    simp only [Finset.mem_insert, Finset.mem_singleton] at this
    rcases this with h' | h' | h' | h'
    exacts [hua h'.symm, hva h'.symm, hat h', hab h']
  have h₁₂ : ∀ x ∈ support H₁, x ∈ support H₂ → x ∈ ({u, v, t} : Finset V) := by
    intro x hx1 hx2
    by_contra hxn
    have := hH₂Z x (Finset.mem_union_right _ (Finset.mem_filter.2 ⟨hx1, hxn⟩)) hx2
    simp only [Finset.mem_insert, Finset.mem_singleton] at this hxn
    rcases this with h' | h' | h' | h'
    · exact hxn (Or.inl h')
    · exact hxn (Or.inr (Or.inl h'))
    · exact hxn (Or.inr (Or.inr h'))
    · exact hb1 (h' ▸ hx1)
  -- 4. composición
  obtain ⟨hJ, habJ, hsupp⟩ := composite_hinge_of hTa hTb hTt hat hbt hH₁.1 hb1 hH₂.1 ha2 h₁₂
  refine ⟨_, hJ, ?_, habJ, ?_, ?_, ?_⟩
  · refine Finset.disjoint_union_left.2 ⟨Finset.disjoint_union_left.2 ⟨hH₁B, ?_⟩, hH₂B⟩
    simp only [wedge, Finset.disjoint_insert_left, Finset.disjoint_singleton_left]
    exact ⟨htBu, htBv⟩
  · intro z hzU hz
    rw [hsupp, Finset.mem_union] at hz
    have hzt : z ≠ t := fun h' => htU (h' ▸ hzU)
    rcases hz with hz | hz
    · have := hH₁Z z (Finset.mem_insert_of_mem hzU) hz
      simp only [Finset.mem_insert, Finset.mem_singleton] at this ⊢
      rcases this with h' | h' | h' | h'
      exacts [Or.inl h', Or.inr (Or.inl h'), Or.inr (Or.inr (Or.inl h')), absurd h' hzt]
    · have := hH₂Z z (Finset.mem_union_left _ hzU) hz
      simp only [Finset.mem_insert, Finset.mem_singleton] at this ⊢
      rcases this with h' | h' | h' | h'
      exacts [Or.inl h', Or.inr (Or.inl h'), absurd h' hzt, Or.inr (Or.inr (Or.inr h'))]
  · rw [hsupp]
    have hsub : ({u, v, t} : Finset V) ⊆ support H₁ ∩ support H₂ := by
      have hR2 := (hinge_order_ge_six hbt.symm hTt hTb hH₂.1).1
      intro x hx
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      refine Finset.mem_inter.2 ⟨hR1 ?_, hR2 ?_⟩ <;>
        simp only [Finset.mem_insert, Finset.mem_singleton] <;> tauto
    have h3 : ({u, v, t} : Finset V).card = 3 := hTt.1
    have := Finset.card_union_add_card_inter (support H₁) (support H₂)
    have := Finset.card_le_card hsub
    omega

  · rw [hsupp]
    have hMono : supportIncrementCost ι R S (support H₁ ∪ support H₂) ≤
        supportIncrementCost ι R S ({t} ∪ (support H₁ ∪ support H₂)) :=
      supportIncrementCost_mono ι R S subset_union_right
    have hBase : S ∪ {t} = S1 := by ext x; simp [S1,or_comm]
    have hLedger : supportIncrementCost ι R S ({t} ∪ (support H₁ ∪ support H₂)) =
        supportIncrementCost ι R S {t}+supportIncrementCost ι R S1 (support H₁)+
          supportIncrementCost ι R S2 (support H₂) := by
      rw [supportIncrementCost_union,supportIncrementCost_union,hBase]
      simp only [S2,Nat.add_assoc]
    have hReal : (supportIncrementCost ι R S (support H₁ ∪ support H₂):ℝ) ≤
        (supportIncrementCost ι R S {t}:ℝ)+(supportIncrementCost ι R S1 (support H₁):ℝ)+
          (supportIncrementCost ι R S2 (support H₂):ℝ) := by
      exact_mod_cast hMono.trans_eq hLedger
    exact hReal.trans (add_le_add (add_le_add hApex hPay₁) hPay₂)

#print axioms exists_low_cost_robust_composite_hinge
end TypedTriangle.Pasch.Ambient


namespace TypedTriangle.Pasch.Ambient
variable {V Ω I : Type*} [Fintype V] [Fintype Ω]

theorem exists_low_cost_gadget_core_fresh_support (ι : V ↪ Ω) {H : Host V I} {F : Set (Multiset I)} {α : ℝ} {h : ℕ}
    (hα : 0 < α) (hH3 : CommonNbrCond H F α) (hH4 : HingeCond H F α h) {a b c : V}
    (hT : IsAllowed H F {a,b,c}) (R : Finset (Finset Ω)) (L : ℕ) (hL : PairCodegreeBound R L)
    (S : Finset V) (Ub : ℕ) (hS : S.card ≤ Ub) (hRoots : ({a,b,c}:Finset V) ⊆ S)
    (U : Finset V) (haU : a ∈ U) (hbU : b ∈ U) (hcU : c ∈ U)
    (B : Finset (Sym2 V)) (d : ℕ) (hdeg : ∀ x, degIn B x ≤ d)
    (hwin1 : (U.card:ℝ)+3+4*d ≤ α/2*Fintype.card V)
    (hwin2 : ((U.card:ℝ)+1+h+5*d)*2^Nat.choose h 2 ≤ α/2*Fintype.card V) :
    ∃ (Y : Finset (Sym2 V)) (x y z : V),
      IsAllowed H F {a,b,x} ∧ IsAllowed H F {a,c,y} ∧ IsAllowed H F {b,c,z} ∧
      x ∉ U ∧ y ∉ U ∧ z ∉ U ∧ x ≠ y ∧ x ≠ z ∧ y ≠ z ∧
      Basal H F Y ∧ Basal H F (Y ∪ (wedge a b x ∪ wedge a c y ∪ wedge b c z)) ∧
      Disjoint Y (wedge a b x ∪ wedge a c y ∪ wedge b c z) ∧
      Disjoint (Y ∪ (wedge a b x ∪ wedge a c y ∪ wedge b c z)) B ∧ Fresh U Y ∧
      (U ∪ support (Y ∪ (wedge a b x ∪ wedge a c y ∪ wedge b c z))).card ≤ U.card+(2*h-2) ∧
      Y.card ≤ (2*h-2).choose 2 ∧
      (supportIncrementCost ι R S (support (Y ∪ (wedge a b x ∪ wedge a c y ∪ wedge b c z))):ℝ) ≤
        gadgetPotentialCost ι α h Ub L ∧
      (∀ w ∈ U, w ∈ support (Y ∪ (wedge a b x ∪ wedge a c y ∪ wedge b c z)) → w ∈ ({a,b,c}:Finset V)) ∧
      (support (Y ∪ (wedge a b x ∪ wedge a c y ∪ wedge b c z))).card ≤ 2*h-2 := by
  obtain ⟨hab,hac,hbc⟩ := distinct_of_card_three hT.1
  let p : S × S → V := fun x => x.1.val
  let q : S × S → V := fun x => x.2.val
  have hMargin : (U.card:ℝ)+2*d ≤ α/2*Fintype.card V := by
    linarith only [hwin1,show (0:ℝ) ≤ d by positivity]
  obtain ⟨x,hxU,hTx,hxBa,hxBb,hPair⟩ := exists_low_total_cost_fresh_apex ι
    hα hH3 hT R L hL p q B d hdeg U hMargin
  have hApex0 : (supportIncrementCost ι R S {x}:ℝ) ≤
      orderRatio ι*((S.card:ℝ)^2*(L:ℝ)^3/(α/2)) := by
    have hNatural := supportIncrementCost_apex_le_pair_sum ι R S x
    have hReal : (supportIncrementCost ι R S {x}:ℝ) ≤
        ∑ k : S×S, (rootedCount (insert {ι k.1.val,ι k.2.val,ι x} R)
          {ι k.1.val,ι k.2.val,ι x}:ℝ) := by exact_mod_cast hNatural
    have hPairNorm : (∑ k : S×S, (rootedCount
        (insert {ι k.1.val,ι k.2.val,ι x} R) {ι k.1.val,ι k.2.val,ι x}:ℝ)) ≤
        orderRatio ι*((S.card:ℝ)^2*(L:ℝ)^3/(α/2)) := by
      convert hPair using 1 <;>
        simp only [p,q,Fintype.card_prod,Fintype.card_coe,Nat.cast_mul,Nat.cast_sum,pow_two] <;> ring
    exact hReal.trans hPairNorm
  have hApex : (supportIncrementCost ι R S {x}:ℝ) ≤ apexPotentialCost ι α Ub L := by
    have hsPow : (S.card:ℝ)^2 ≤ (Ub:ℝ)^2 := by exact_mod_cast Nat.pow_le_pow_left hS 2
    exact hApex0.trans (mul_le_mul_of_nonneg_left
      (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hsPow (by positivity)) (by positivity))
      (orderRatio_nonneg ι))
  have hcx : c ≠ x := fun he => hxU (he ▸ hcU)
  have hax : a ≠ x := fun he => hxU (he ▸ haU)
  have hbx : b ≠ x := fun he => hxU (he ▸ hbU)
  let S1 := insert x S
  have hS1 : S1.card ≤ Ub+1 := (card_insert_le x S).trans (Nat.add_le_add_right hS 1)
  have hRoots1 : ({a,b,c,x}:Finset V) ⊆ S1 := by
    intro v hv
    simp only [mem_insert,mem_singleton] at hv
    rcases hv with rfl | rfl | rfl | rfl
    · exact mem_insert_of_mem (hRoots (by simp))
    · exact mem_insert_of_mem (hRoots (by simp))
    · exact mem_insert_of_mem (hRoots (by simp))
    · exact mem_insert_self _ _
  have hCardX : ((insert x U).card:ℝ) ≤ U.card+1 := by exact_mod_cast card_insert_le x U
  obtain ⟨J,hJ,hJB,hJcx,hJU,hJc,hCompPay⟩ := exists_low_cost_robust_composite_hinge ι
    hα hH3 hH4 hcx hT hTx R L hL S1 (Ub+1) hS1 hRoots1 (insert x U) B d hdeg
    (by linarith only [hCardX,hwin1])
    (le_trans (mul_le_mul_of_nonneg_right (by linarith only [hCardX]) (by positivity)) hwin2)
  obtain ⟨hJsub, hJdisj, ⟨Dc, hDc⟩, ⟨Dx, hDx⟩⟩ := hJ
  have notJ : ∀ f, f ∈ triEdges ({a, b, c} : Finset V) ∪ triEdges ({a, b, x} : Finset V) →
      f ∉ J := fun f hf hfJ => Finset.disjoint_left.1 hJdisj hfJ hf
  have habJ : s(a, b) ∉ J := notJ _ (Finset.mem_union_left _ (mem_triEdges.2 ⟨by simp, by simp, hab⟩))
  have hacJ : s(a, c) ∉ J := notJ _ (Finset.mem_union_left _ (mem_triEdges.2 ⟨by simp, by simp, hac⟩))
  have hbcJ : s(b, c) ∉ J := notJ _ (Finset.mem_union_left _ (mem_triEdges.2 ⟨by simp, by simp, hbc⟩))
  have haxJ : s(a, x) ∉ J := notJ _ (Finset.mem_union_right _ (mem_triEdges.2 ⟨by simp, by simp, hax⟩))
  have hbxJ : s(b, x) ∉ J := notJ _ (Finset.mem_union_right _ (mem_triEdges.2 ⟨by simp, by simp, hbx⟩))
  have hfreshJ : Fresh (insert x U) J := (show IsHinge H F a b c x J from
    ⟨hJsub, hJdisj, ⟨Dc, hDc⟩, ⟨Dx, hDx⟩⟩).fresh hJcx (insert x U) hJU
  have hsuppJ : ∀ w, w ∈ support J → w ∉ ({a, b, c, x} : Finset V) → w ∉ U := by
    intro w hw hwR hwU
    exact hwR (hJU w (Finset.mem_insert_of_mem hwU) hw)
  -- triángulo `acy` de `D^c`
  obtain ⟨T1, hT1, y, haT1, hcT1, hyT1, hya, hyc, hay, hcy⟩ :=
    hDc.third (p := a) (q := c) (by simp [wedge])
  obtain ⟨T2, hT2, z, hbT2, hcT2, hzT2, hzb, hzc, hbz, hcz⟩ :=
    hDc.third (p := b) (q := c) (by simp [wedge])
  have hayJ : s(a, y) ∈ J := by
    simp only [Finset.mem_union, wedge, Finset.mem_insert, Finset.mem_singleton,
      Sym2.eq_iff] at hay
    rcases hay with h' | (⟨-, h'⟩ | ⟨h', -⟩) | (⟨h', -⟩ | ⟨h', -⟩)
    · exact h'
    · exact absurd h' hyc
    · exact absurd h' hac
    · exact absurd h' hab
    · exact absurd h' hac
  have hyb : y ≠ b := fun h' => habJ (h' ▸ hayJ)
  have hcyJ : s(c, y) ∈ J := by
    simp only [Finset.mem_union, wedge, Finset.mem_insert, Finset.mem_singleton,
      Sym2.eq_iff] at hcy
    rcases hcy with h' | (⟨h', -⟩ | ⟨-, h'⟩) | (⟨h', -⟩ | ⟨-, h'⟩)
    · exact h'
    · exact absurd h'.symm hac
    · exact absurd h' hya
    · exact absurd h'.symm hbc
    · exact absurd h' hyb
  have hyx : y ≠ x := fun h' => haxJ (h' ▸ hayJ)
  have hbzJ : s(b, z) ∈ J := by
    simp only [Finset.mem_union, wedge, Finset.mem_insert, Finset.mem_singleton,
      Sym2.eq_iff] at hbz
    rcases hbz with h' | (⟨h', -⟩ | ⟨h', -⟩) | (⟨-, h'⟩ | ⟨h', -⟩)
    · exact h'
    · exact absurd h'.symm hab
    · exact absurd h' hbc
    · exact absurd h' hzc
    · exact absurd h' hbc
  have hza : z ≠ a := fun h' => habJ (by rw [Sym2.eq_swap]; exact h' ▸ hbzJ)
  have hczJ : s(c, z) ∈ J := by
    simp only [Finset.mem_union, wedge, Finset.mem_insert, Finset.mem_singleton,
      Sym2.eq_iff] at hcz
    rcases hcz with h' | (⟨h', -⟩ | ⟨-, h'⟩) | (⟨h', -⟩ | ⟨-, h'⟩)
    · exact h'
    · exact absurd h'.symm hac
    · exact absurd h' hza
    · exact absurd h'.symm hbc
    · exact absurd h' hzb
  have hzx : z ≠ x := fun h' => hbxJ (h' ▸ hbzJ)
  have hyU : y ∉ U := hsuppJ y (mem_support_of_mem hayJ (by simp)) (by
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or]; exact ⟨hya, hyb, hyc, hyx⟩)
  have hzU : z ∉ U := hsuppJ z (mem_support_of_mem hbzJ (by simp)) (by
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or]; exact ⟨hza, hzb, hzc, hzx⟩)
  have hT1eq : T1 = {a, c, y} := eq_three_of_mem (hDc.1 T1 hT1).1 haT1 hcT1 hyT1 hac
    (Ne.symm hya) (Ne.symm hyc)
  have hT2eq : T2 = {b, c, z} := eq_three_of_mem (hDc.1 T2 hT2).1 hbT2 hcT2 hzT2 hbc
    (Ne.symm hzb) (Ne.symm hzc)
  have hyz : y ≠ z := by
    intro hyz
    have hne : T1 ≠ T2 := by
      intro h'
      rw [h', hT2eq] at haT1
      simp only [Finset.mem_insert, Finset.mem_singleton] at haT1
      rcases haT1 with h'' | h'' | h''
      exacts [hab h'', hac h'', hza h''.symm]
    exact hne (hDc.unique hT1 hT2 (by rw [hT1eq]; exact mem_triEdges.2 ⟨by simp, by simp, Ne.symm hyc⟩)
      (by rw [hT2eq, ← hyz]; exact mem_triEdges.2 ⟨by simp, by simp [hyz], Ne.symm hyc⟩))
  have hTacy : IsAllowed H F {a, c, y} := hT1eq ▸ hDc.1 T1 hT1
  have hTbcz : IsAllowed H F {b, c, z} := hT2eq ▸ hDc.1 T2 hT2
  -- el gadget
  set Wab := wedge a b x
  set Wac := wedge a c y
  set Wbc := wedge b c z
  have hWacJ : Wac ⊆ J := by
    intro f hf; simp only [Wac, wedge, Finset.mem_insert, Finset.mem_singleton] at hf
    rcases hf with rfl | rfl
    · exact hayJ
    · exact hcyJ
  have hWbcJ : Wbc ⊆ J := by
    intro f hf; simp only [Wbc, wedge, Finset.mem_insert, Finset.mem_singleton] at hf
    rcases hf with rfl | rfl
    · exact hbzJ
    · exact hczJ
  have hWabJ : Disjoint J Wab := by
    simp only [Wab, wedge, Finset.disjoint_insert_right, Finset.disjoint_singleton_right]
    exact ⟨haxJ, hbxJ⟩
  set Y := J \ (Wac ∪ Wbc) with hYdef
  have hYsub : Y ⊆ J := Finset.sdiff_subset
  have hall : Y ∪ (Wab ∪ Wac ∪ Wbc) = J ∪ Wab := by
    ext f; simp only [Y, Finset.mem_union, Finset.mem_sdiff]
    constructor
    · rintro (⟨hf, -⟩ | (hf | hf) | hf)
      · exact Or.inl hf
      · exact Or.inr hf
      · exact Or.inl (hWacJ hf)
      · exact Or.inl (hWbcJ hf)
    · rintro (hf | hf)
      · by_cases h1 : f ∈ Wac ∪ Wbc
        · rcases Finset.mem_union.1 h1 with h2 | h2
          · exact Or.inr (Or.inl (Or.inr h2))
          · exact Or.inr (Or.inr h2)
        · exact Or.inl ⟨hf, by simpa using h1⟩
      · exact Or.inr (Or.inl (Or.inl hf))
  have hYbasal : Basal H F Y := by
    have hsub : ({T1, T2} : Finset (Finset V)) ⊆ Dc := by
      intro T hT; simp only [Finset.mem_insert, Finset.mem_singleton] at hT
      rcases hT with rfl | rfl <;> assumption
    refine Basal.congr ⟨_, hDc.sdiff_sub hsub⟩ ?_
    rw [Finset.biUnion_insert, Finset.singleton_biUnion, hT1eq, hT2eq,
      triEdges_eq_insert_wedge hac (Ne.symm hya) (Ne.symm hyc),
      triEdges_eq_insert_wedge hbc (Ne.symm hzb) (Ne.symm hzc),
      show wedge a b c = {s(a, c), s(b, c)} from rfl,
      show wedge a c y = Wac from rfl, show wedge b c z = Wbc from rfl]
    ext f
    have h1 : f ∈ J → f ≠ s(a, c) := fun hf he => hacJ (he ▸ hf)
    have h2 : f ∈ J → f ≠ s(b, c) := fun hf he => hbcJ (he ▸ hf)
    simp only [Y, Finset.mem_sdiff, Finset.mem_union, Finset.mem_insert, Finset.mem_singleton]
    constructor
    · rintro ⟨hf | hf | hf, hn⟩
      · exact ⟨hf, fun h => hn (h.elim (fun h => Or.inl (Or.inr h)) (fun h => Or.inr (Or.inr h)))⟩
      · exact absurd (Or.inl (Or.inl hf)) hn
      · exact absurd (Or.inr (Or.inl hf)) hn
    · rintro ⟨hf, hn⟩
      refine ⟨Or.inl hf, ?_⟩
      rintro ((h | h) | h | h)
      · exact h1 hf h
      · exact hn (Or.inl h)
      · exact h2 hf h
      · exact hn (Or.inr h)
  have h6 : 6 ≤ h := by
    obtain ⟨i, hi6, hih, -⟩ := hH4 a b c x hcx hT hTx
    omega
  refine ⟨Y, x, y, z, hTx, hTacy, hTbcz, hxU, hyU, hzU, Ne.symm hyx, Ne.symm hzx, hyz, hYbasal,
    ?_, ?_, ?_, (hfreshJ.subset hYsub).anti (Finset.subset_insert x U), ?_, ?_, ?_, ?_, ?_⟩
  · rw [hall]; exact ⟨Dx, hDx⟩
  · refine Finset.disjoint_union_right.2 ⟨Finset.disjoint_union_right.2
      ⟨Disjoint.mono_left hYsub hWabJ, ?_⟩, ?_⟩
    · exact Disjoint.mono_right Finset.subset_union_left Finset.sdiff_disjoint
    · exact Disjoint.mono_right Finset.subset_union_right Finset.sdiff_disjoint
  · rw [hall]
    refine Finset.disjoint_union_left.2 ⟨hJB, ?_⟩
    simp only [Wab, wedge, Finset.disjoint_insert_left, Finset.disjoint_singleton_left]
    exact ⟨hxBa, hxBb⟩
  · rw [hall, support_union, show Wab = wedge a b x from rfl, support_wedge]
    have hsub : U ∪ (support J ∪ {a, b, x}) ⊆ insert x (U ∪ support J) := by
      intro w hw
      simp only [Finset.mem_union, Finset.mem_insert, Finset.mem_singleton] at hw ⊢
      rcases hw with hw | hw | hw | hw | hw
      · exact Or.inr (Or.inl hw)
      · exact Or.inr (Or.inr hw)
      · exact Or.inr (Or.inl (hw ▸ haU))
      · exact Or.inr (Or.inl (hw ▸ hbU))
      · exact Or.inl hw
    refine (Finset.card_le_card hsub).trans ((Finset.card_insert_le _ _).trans ?_)
    have := Finset.card_union_le U (support J)
    omega
  · have := card_le_choose_of_support_le hJc
    rw [show 2 * h - 3 + 1 = 2 * h - 2 by omega] at this
    exact (Finset.card_le_card hYsub).trans this

  · rw [hall,support_union,show Wab = wedge a b x from rfl,support_wedge]
    have haS : a ∈ S := hRoots (by simp)
    have hbS : b ∈ S := hRoots (by simp)
    have hSame : S ∪ (support J ∪ {a,b,x}) = S ∪ ({x} ∪ support J) := by
      ext v
      have ha : v = a → v ∈ S := by rintro rfl; exact haS
      have hb : v = b → v ∈ S := by rintro rfl; exact hbS
      simp only [mem_union,mem_insert,mem_singleton]
      tauto
    have hEqCost : supportIncrementCost ι R S (support J ∪ {a,b,x}) =
        supportIncrementCost ι R S ({x} ∪ support J) := by
      unfold supportIncrementCost Pasch.supportIncrementCost
      rw [←map_union,←map_union,hSame]
    have hBase : S ∪ {x} = S1 := by ext v; simp [S1]
    rw [hEqCost,supportIncrementCost_union,hBase,Nat.cast_add]
    exact add_le_add hApex hCompPay

  · intro w hwU hw
    rw [hall,support_union,show Wab = wedge a b x from rfl,support_wedge] at hw
    rcases mem_union.mp hw with hwJ | hwW
    · have hRoot := hJU w (mem_insert_of_mem hwU) hwJ
      simp only [mem_insert,mem_singleton] at hRoot ⊢
      rcases hRoot with ha | hb | hc | hx
      · exact Or.inl ha
      · exact Or.inr (Or.inl hb)
      · exact Or.inr (Or.inr hc)
      · exact (hxU (hx ▸ hwU)).elim
    · simp only [mem_insert,mem_singleton] at hwW ⊢
      rcases hwW with ha | hb | hx
      · exact Or.inl ha
      · exact Or.inr (Or.inl hb)
      · exact (hxU (hx ▸ hwU)).elim
  · rw [hall,support_union,show Wab = wedge a b x from rfl,support_wedge]
    have hRootsJ : ({a,b,c,x}:Finset V) ⊆ support J :=
      (hinge_order_ge_six hcx hT hTx (show IsHinge H F a b c x J from
        ⟨hJsub,hJdisj,⟨Dc,hDc⟩,⟨Dx,hDx⟩⟩)).1
    have hRoot3 : ({a,b,x}:Finset V) ⊆ support J := by
      intro w hw
      apply hRootsJ
      simp only [mem_insert,mem_singleton] at hw ⊢
      tauto
    rw [union_eq_left.mpr hRoot3]
    omega

theorem exists_low_cost_slot_gadget_fresh_support (ι : V ↪ Ω) {H : Host V I} {F : Set (Multiset I)} {α : ℝ} {h : ℕ}
    (hα : 0 < α) (hH3 : CommonNbrCond H F α) (hH4 : HingeCond H F α h) {T : Finset V}
    (hT : IsAllowed H F T) (R : Finset (Finset Ω)) (L : ℕ) (hL : PairCodegreeBound R L)
    (S : Finset V) (Ub : ℕ) (hS : S.card ≤ Ub) (hTS : T ⊆ S)
    (U : Finset V) (hTU : T ⊆ U)
    (B : Finset (Sym2 V)) (d : ℕ) (hdeg : ∀ x, degIn B x ≤ d)
    (hwin1 : (U.card : ℝ) + 3 + 4 * d ≤ α/2 * Fintype.card V)
    (hwin2 : ((U.card : ℝ) + 1 + h + 5 * d) * 2 ^ Nat.choose h 2 ≤ α / 2 * Fintype.card V) :
    ∃ (Y : Finset (Sym2 V)) (ap : Sym2 V → V),
      (∀ e ∈ triEdges T, ap e ∉ U ∧ ap e ∉ e ∧ IsAllowed H F (slotTri e (ap e))) ∧
      (∀ e ∈ triEdges T, ∀ e' ∈ triEdges T, ap e = ap e' → e = e') ∧
      Basal H F Y ∧ Basal H F (Y ∪ (triEdges T).biUnion (fun e => wedgeOf e (ap e))) ∧
      Disjoint Y ((triEdges T).biUnion (fun e => wedgeOf e (ap e))) ∧
      Disjoint (Y ∪ (triEdges T).biUnion (fun e => wedgeOf e (ap e))) B ∧ Fresh U Y ∧
      (U ∪ support (Y ∪ (triEdges T).biUnion (fun e => wedgeOf e (ap e)))).card ≤
        U.card + (2 * h - 2) ∧ Y.card ≤ (2 * h - 2).choose 2 ∧
      (supportIncrementCost ι R S (support (Y ∪ (triEdges T).biUnion (fun e => wedgeOf e (ap e)))):ℝ) ≤
        gadgetPotentialCost ι α h Ub L ∧
      (∀ w ∈ U, w ∈ support (Y ∪ (triEdges T).biUnion (fun e => wedgeOf e (ap e))) → w ∈ T) ∧
      (support (Y ∪ (triEdges T).biUnion (fun e => wedgeOf e (ap e)))).card ≤ 2*h-2 := by
  obtain ⟨a, b, c, hab, hac, hbc, rfl⟩ := Finset.card_eq_three.1 hT.1
  have haU : a ∈ U := hTU (by simp)
  have hbU : b ∈ U := hTU (by simp)
  have hcU : c ∈ U := hTU (by simp)
  obtain ⟨Y, x, y, z, hTx, hTy, hTz, hxU, hyU, hzU, hxy, hxz, hyz, hY, hYW, hYWd, hYB, hYU,
    hcard, hYe, hPay, hInter, hSupp⟩ := exists_low_cost_gadget_core_fresh_support ι hα hH3 hH4 hT R L hL S Ub hS hTS
      U haU hbU hcU B d hdeg hwin1 hwin2
  set ap : Sym2 V → V := fun e => if e = s(a, b) then x else if e = s(a, c) then y else z
  have h1 : s(a, c) ≠ s(a, b) := by
    intro h'; rw [Sym2.eq_iff] at h'; rcases h' with ⟨-, h'⟩ | ⟨h', -⟩
    exacts [hbc h'.symm, hab h']
  have h2 : s(b, c) ≠ s(a, b) := by
    intro h'; rw [Sym2.eq_iff] at h'; rcases h' with ⟨h', -⟩ | ⟨-, h'⟩
    exacts [hab h'.symm, hac h'.symm]
  have h3 : s(b, c) ≠ s(a, c) := by
    intro h'; rw [Sym2.eq_iff] at h'; rcases h' with ⟨h', -⟩ | ⟨h', -⟩
    exacts [hab h'.symm, hbc h']
  have hapab : ap s(a, b) = x := by simp [ap]
  have hapac : ap s(a, c) = y := by simp [ap, h1]
  have hapbc : ap s(b, c) = z := by simp [ap, h2, h3]
  have hE := triEdges_three hab hac hbc
  have hW : (triEdges ({a, b, c} : Finset V)).biUnion (fun e => wedgeOf e (ap e)) =
      wedge a b x ∪ wedge a c y ∪ wedge b c z := by
    rw [hE, Finset.biUnion_insert, Finset.biUnion_insert, Finset.singleton_biUnion, hapab, hapac,
      hapbc, wedgeOf_mk, wedgeOf_mk, wedgeOf_mk, Finset.union_assoc]
  refine ⟨Y, ap, ?_, ?_, hY, by rw [hW]; exact hYW, by rw [hW]; exact hYWd,
    by rw [hW]; exact hYB, hYU, by rw [hW]; exact hcard, hYe, by rw [hW]; exact hPay,
    by rw [hW]; exact hInter, by rw [hW]; exact hSupp⟩
  · intro e he
    rw [hE] at he
    simp only [Finset.mem_insert, Finset.mem_singleton] at he
    rcases he with rfl | rfl | rfl
    · rw [hapab, slotTri_mk]
      exact ⟨hxU, by simp only [Sym2.mem_iff, not_or]; exact ⟨fun h' => hxU (h' ▸ haU),
        fun h' => hxU (h' ▸ hbU)⟩, hTx⟩
    · rw [hapac, slotTri_mk]
      exact ⟨hyU, by simp only [Sym2.mem_iff, not_or]; exact ⟨fun h' => hyU (h' ▸ haU),
        fun h' => hyU (h' ▸ hcU)⟩, hTy⟩
    · rw [hapbc, slotTri_mk]
      exact ⟨hzU, by simp only [Sym2.mem_iff, not_or]; exact ⟨fun h' => hzU (h' ▸ hbU),
        fun h' => hzU (h' ▸ hcU)⟩, hTz⟩
  · intro e he e' he' hee
    rw [hE] at he he'
    simp only [Finset.mem_insert, Finset.mem_singleton] at he he'
    rcases he with rfl | rfl | rfl <;> rcases he' with rfl | rfl | rfl <;>
      simp only [hapab, hapac, hapbc] at hee <;> first | rfl | exact absurd hee ‹_› |
        exact absurd hee.symm ‹_›


#print axioms exists_low_cost_gadget_core_fresh_support
#print axioms exists_low_cost_slot_gadget_fresh_support
end TypedTriangle.Pasch.Ambient


namespace TypedTriangle.Pasch.Ambient
variable {V Ω I : Type*} [Fintype V] [Fintype Ω] {τ σ : Type*}

theorem exists_low_cost_slot_gadget_avoiding_vertices (ι : V ↪ Ω) {H : Host V I} {F : Set (Multiset I)}
    {α : ℝ} {h : ℕ} (hα : 0 < α) (hH3 : CommonNbrCond H F α) (hH4 : HingeCond H F α h)
    {T : Finset V} (hT : IsAllowed H F T) (R : Finset (Finset Ω)) (L : ℕ) (hL : PairCodegreeBound R L)
    (U : Finset V) (Ub : ℕ) (hUc : U.card ≤ Ub) (hTU : T ⊆ U)
    (Z : Finset V) (hUZ : Disjoint U Z) (B : Finset (Sym2 V)) (d : ℕ) (hdeg : ∀ x, degIn B x ≤ d)
    (hwin1 : (Ub:ℝ)+Z.card+3+4*d ≤ α/2*Fintype.card V)
    (hwin2 : ((Ub:ℝ)+Z.card+1+h+5*d)*2^Nat.choose h 2 ≤ α/2*Fintype.card V) :
    ∃ (Y : Finset (Sym2 V)) (ap : Sym2 V → V),
      (∀ e ∈ triEdges T, ap e ∉ U ∧ ap e ∉ e ∧ IsAllowed H F (slotTri e (ap e))) ∧
      (∀ e ∈ triEdges T, ∀ e' ∈ triEdges T, ap e = ap e' → e = e') ∧
      Basal H F Y ∧ Basal H F (Y ∪ (triEdges T).biUnion (fun e => wedgeOf e (ap e))) ∧
      Disjoint Y ((triEdges T).biUnion (fun e => wedgeOf e (ap e))) ∧
      Disjoint (Y ∪ (triEdges T).biUnion (fun e => wedgeOf e (ap e))) B ∧ Fresh U Y ∧
      (U ∪ support (Y ∪ (triEdges T).biUnion (fun e => wedgeOf e (ap e)))).card ≤ U.card+(2*h-2) ∧
      Y.card ≤ (2*h-2).choose 2 ∧
      (supportIncrementCost ι R U (support (Y ∪ (triEdges T).biUnion (fun e => wedgeOf e (ap e)))):ℝ) ≤
        gadgetPotentialCost ι α h Ub L ∧
      Disjoint (support (Y ∪ (triEdges T).biUnion (fun e => wedgeOf e (ap e)))) Z := by
  let Big := U ∪ Z
  have hBigNat : Big.card ≤ Ub+Z.card := (card_union_le _ _).trans (Nat.add_le_add_right hUc _)
  have hBig : (Big.card:ℝ) ≤ (Ub:ℝ)+Z.card := by exact_mod_cast hBigNat
  obtain ⟨Y,ap,hAp,hInj,hY,hYW,hDis,hB,hFresh,hCard,hYe,hPay,hInter,hSupport⟩ :=
    exists_low_cost_slot_gadget_fresh_support ι hα hH3 hH4 hT R L hL U Ub hUc hTU Big
      (hTU.trans subset_union_left) B d hdeg (by linarith only [hBig,hwin1])
      ((mul_le_mul_of_nonneg_right (by linarith only [hBig]) (by positivity)).trans hwin2)
  refine ⟨Y,ap,?_,hInj,hY,hYW,hDis,hB,hFresh.anti subset_union_left,
    (card_union_le _ _).trans (Nat.add_le_add_left hSupport _),hYe,hPay,?_⟩
  · intro e he
    obtain ⟨hNot,hEdge,hAllow⟩ := hAp e he
    exact ⟨fun hu => hNot (mem_union_left _ hu),hEdge,hAllow⟩
  · apply disjoint_left.mpr
    intro z hz hzZ
    exact disjoint_left.mp hUZ (hTU (hInter z (mem_union_right _ hzZ) hz)) hzZ

theorem exists_low_cost_composite_hinge_avoiding_vertices (ι : V ↪ Ω) {H : Host V I} {F : Set (Multiset I)}
    {α : ℝ} {h : ℕ} (hα : 0 < α) (hH3 : CommonNbrCond H F α) (hH4 : HingeCond H F α h)
    {u v a b : V} (hab : a ≠ b) (hTa : IsAllowed H F {u,v,a}) (hTb : IsAllowed H F {u,v,b})
    (R : Finset (Finset Ω)) (L : ℕ) (hL : PairCodegreeBound R L)
    (U : Finset V) (Ub : ℕ) (hUc : U.card ≤ Ub) (hRoots : ({u,v,a,b}:Finset V) ⊆ U)
    (Z : Finset V) (hUZ : Disjoint U Z) (B : Finset (Sym2 V)) (d : ℕ) (hdeg : ∀ x, degIn B x ≤ d)
    (hwin1 : (Ub:ℝ)+Z.card+2+4*d ≤ α/2*Fintype.card V)
    (hwin2 : ((Ub:ℝ)+Z.card+h+5*d)*2^Nat.choose h 2 ≤ α/2*Fintype.card V) :
    ∃ J, IsHinge H F u v a b J ∧ Disjoint J B ∧ s(a,b) ∉ J ∧
      (∀ z ∈ U, z ∈ support J → z ∈ ({u,v,a,b}:Finset V)) ∧
      (support J).card ≤ 2*h-3 ∧
      (supportIncrementCost ι R U (support J):ℝ) ≤ compositePotentialCost ι α h Ub L ∧
      Disjoint (support J) Z := by
  let Big := U ∪ Z
  have hBigNat : Big.card ≤ Ub+Z.card := (card_union_le _ _).trans (Nat.add_le_add_right hUc _)
  have hBig : (Big.card:ℝ) ≤ (Ub:ℝ)+Z.card := by exact_mod_cast hBigNat
  obtain ⟨J,hJ,hB,hNo,hFresh,hCard,hPay⟩ := exists_low_cost_robust_composite_hinge ι
    hα hH3 hH4 hab hTa hTb R L hL U Ub hUc hRoots Big B d hdeg
      (by linarith only [hBig,hwin1])
      ((mul_le_mul_of_nonneg_right (by linarith only [hBig]) (by positivity)).trans hwin2)
  refine ⟨J,hJ,hB,hNo,(fun z hz => hFresh z (mem_union_left _ hz)),hCard,hPay,?_⟩
  apply disjoint_left.mpr
  intro z hz hzZ
  exact disjoint_left.mp hUZ (hRoots (hFresh z (mem_union_right _ hzZ) hz)) hzZ


theorem gadget_phase_avoiding_vertices_with_support_budget (ι : V ↪ Ω) {H : Host V I} {F : Set (Multiset I)} {α : ℝ} {h : ℕ}
    (hα : 0 < α) (hH3 : CommonNbrCond H F α) (hH4 : HingeCond H F α h)
    (R : Finset (Finset Ω)) (L : ℕ) (hL : PairCodegreeBound R L) (Z : Finset V)
    (B : Finset (Sym2 V)) (d : ℕ) (hdeg : ∀ x, degIn B x ≤ d)
    (tri : τ → Finset V) (sgn : τ → Prop) (Ub : ℕ)
    (hwin1 : (Ub : ℝ) + Z.card + 3 + 4 * d ≤ α/2 * Fintype.card V)
    (hwin2 : ((Ub : ℝ) + Z.card + 1 + h + 5 * d) * 2 ^ Nat.choose h 2 ≤ α / 2 * Fintype.card V) :
    ∀ (O : Finset τ) (U : Finset V), Disjoint U Z → (∀ o ∈ O, IsAllowed H F (tri o) ∧ tri o ⊆ U) →
      U.card + O.card * (2 * h - 2) ≤ Ub →
      ∃ (Y : Finset (Sym2 V)) (ap : τ × Sym2 V → V) (U' : Finset V),
        U ⊆ U' ∧ U'.card ≤ U.card + O.card * (2 * h - 2) ∧
        (∀ s ∈ occSlots O tri, ap s ∉ U ∧ ap s ∈ U' ∧ ap s ∉ s.2 ∧
          IsAllowed H F (slotTri s.2 (ap s))) ∧
        (∀ s ∈ occSlots O tri, ∀ s' ∈ occSlots O tri, ap s = ap s' → s = s') ∧
        Basal H F (Y ∪ ((occSlots O tri).filter (fun s => sgn s.1)).biUnion
          (fun s => wedgeOf s.2 (ap s))) ∧
        Basal H F (Y ∪ ((occSlots O tri).filter (fun s => ¬ sgn s.1)).biUnion
          (fun s => wedgeOf s.2 (ap s))) ∧
        Disjoint Y ((occSlots O tri).biUnion (fun s => wedgeOf s.2 (ap s))) ∧
        Disjoint (Y ∪ (occSlots O tri).biUnion (fun s => wedgeOf s.2 (ap s))) B ∧
        Fresh U Y ∧ Inside U' Y ∧ Y.card ≤ O.card * (2 * h - 2).choose 2 ∧
        (supportIncrementCost ι R U U':ℝ) ≤ (O.card:ℝ)*gadgetPotentialCost ι α h Ub L ∧ Disjoint U' Z := by
  intro O
  induction O using Finset.induction_on with
  | empty =>
    intro U hUZ _ _
    refine ⟨∅, fun s => (Quot.out s.2).1, U, subset_refl _, by simp, by simp [occSlots],
      by simp [occSlots], ?_, ?_, by simp, by simp [occSlots], fun e he => by simp at he,
      fun e he => by simp at he, by simp, ?_, hUZ⟩
    · simpa [occSlots] using Basal.empty H F
    · simpa [occSlots] using Basal.empty H F
    · rw [supportIncrementCost_self]
      simp
  | @insert o O ho ih =>
    intro U hUZ hOU hU
    have hoU := hOU o (Finset.mem_insert_self _ _)
    have hcardins : (insert o O).card = O.card + 1 := Finset.card_insert_of_notMem ho
    have hUb : (U.card : ℝ) ≤ Ub := by
      have : U.card ≤ Ub := by rw [hcardins] at hU; nlinarith
      exact_mod_cast this
    obtain ⟨Y₀, ap₀, hap₀, hinj₀, hY₀, hY₀W, hY₀Wd, hY₀B, hY₀U, hcard₀, hY₀e, hPay₀, hNoZ₀⟩ :=
      exists_low_cost_slot_gadget_avoiding_vertices ι hα hH3 hH4 hoU.1 R L hL U Ub
        (by exact_mod_cast hUb) hoU.2 Z hUZ B d hdeg hwin1 hwin2
    set W₀ := (triEdges (tri o)).biUnion (fun e => wedgeOf e (ap₀ e))
    set U₁ := U ∪ support (Y₀ ∪ W₀)
    have hUU₁ : U ⊆ U₁ := Finset.subset_union_left
    have hU₁Z : Disjoint U₁ Z := disjoint_union_left.mpr ⟨hUZ,hNoZ₀⟩
    have hin₁ : Inside U₁ (Y₀ ∪ W₀) := (inside_support _).mono Finset.subset_union_right
    obtain ⟨Y', ap', U', hU₁U', hU'c, hap', hinj', hY'pos, hY'neg, hY'Wd, hY'B, hY'U, hY'in,
      hY'e, hPay', hU'Z⟩ :=
      ih U₁ hU₁Z (fun o' ho' => ⟨(hOU o' (Finset.mem_insert_of_mem ho')).1,
        (hOU o' (Finset.mem_insert_of_mem ho')).2.trans hUU₁⟩) (by
          rw [hcardins] at hU
          have : (O.card + 1) * (2 * h - 2) = O.card * (2 * h - 2) + (2 * h - 2) := by ring
          have h0 : (U ∪ support (Y₀ ∪ W₀)).card ≤ U.card + (2 * h - 2) := hcard₀
          omega)
    set ap : τ × Sym2 V → V := fun s => if s.1 = o then ap₀ s.2 else ap' s
    have hap_o : ∀ e, ap (o, e) = ap₀ e := fun e => by simp [ap]
    have hap_O : ∀ s ∈ occSlots O tri, ap s = ap' s := fun s hs => by
      have : s.1 ≠ o := fun h' => ho (h' ▸ (mem_occSlots.1 hs).1)
      simp [ap, this]
    have hap₀U₁ : ∀ e ∈ triEdges (tri o), ap₀ e ∈ U₁ := fun e he =>
      Finset.mem_union_right _ (apex_mem_support (not_isDiag_of_mem_triEdges he)
        (fun f hf => Finset.mem_union_right _ (Finset.mem_biUnion.2 ⟨e, he, hf⟩)))
    have hW'eq : ∀ (q : τ × Sym2 V → Prop) [DecidablePred q],
        ((occSlots O tri).filter q).biUnion (fun s => wedgeOf s.2 (ap s)) =
        ((occSlots O tri).filter q).biUnion (fun s => wedgeOf s.2 (ap' s)) := fun q _ =>
      Finset.biUnion_congr rfl (fun s hs => by rw [hap_O s (Finset.mem_filter.1 hs).1])
    have hW₀eq : (triEdges (tri o)).biUnion (fun e => wedgeOf (o, e).2 (ap (o, e))) = W₀ :=
      Finset.biUnion_congr rfl (fun e _ => by rw [hap_o])
    have hfresh' : ∀ (q : τ × Sym2 V → Prop) [DecidablePred q],
        Fresh U₁ (((occSlots O tri).filter q).biUnion (fun s => wedgeOf s.2 (ap' s))) :=
      fun q _ => fresh_wedges (fun s hs => (hap' s (Finset.mem_filter.1 hs).1).1)
    have hsplit : ∀ (q : τ → Prop) [DecidablePred q],
        ((occSlots (insert o O) tri).filter (fun s => q s.1)).biUnion
          (fun s => wedgeOf s.2 (ap s)) = (if q o then W₀ else ∅) ∪
        ((occSlots O tri).filter (fun s => q s.1)).biUnion (fun s => wedgeOf s.2 (ap' s)) := by
      intro q _
      rw [biUnion_filter_insert, hW'eq (fun s => q s.1)]
      congr 1
      split_ifs
      · exact hW₀eq
      · rfl
    have hWall : (occSlots (insert o O) tri).biUnion (fun s => wedgeOf s.2 (ap s)) =
        W₀ ∪ (occSlots O tri).biUnion (fun s => wedgeOf s.2 (ap' s)) := by
      have := hsplit (fun _ => True)
      simp only [if_true, Finset.filter_true] at this
      exact this
    have hY'U₁ : Fresh U₁ Y' := hY'U
    have hfreshall : Fresh U₁ ((occSlots O tri).biUnion (fun s => wedgeOf s.2 (ap' s))) :=
      fresh_wedges (fun s hs => (hap' s hs).1)
    have hdisj₁ : ∀ X, Fresh U₁ X → Disjoint (Y₀ ∪ W₀) X := fun X hX => hin₁.disjoint_fresh hX
    have hmode : ∀ (q : τ → Prop) [DecidablePred q],
        Basal H F (Y' ∪ ((occSlots O tri).filter (fun s => q s.1)).biUnion
          (fun s => wedgeOf s.2 (ap' s))) →
        Basal H F ((Y₀ ∪ Y') ∪ ((occSlots (insert o O) tri).filter (fun s => q s.1)).biUnion
          (fun s => wedgeOf s.2 (ap s))) := by
      intro q _ hq
      rw [hsplit q]
      set X0 : Finset (Sym2 V) := if q o then W₀ else ∅ with hX0
      set R := ((occSlots O tri).filter (fun s => q s.1)).biUnion (fun s => wedgeOf s.2 (ap' s))
      have heq : Y₀ ∪ Y' ∪ (X0 ∪ R) = (Y₀ ∪ X0) ∪ (Y' ∪ R) := by
        ext; simp only [Finset.mem_union]; tauto
      have hX0sub : Y₀ ∪ X0 ⊆ Y₀ ∪ W₀ := by
        intro f hf
        rw [hX0] at hf
        split_ifs at hf
        · exact hf
        · exact Finset.mem_union_left _ (by simpa using hf)
      have hq0 : Basal H F (Y₀ ∪ X0) := by
        rw [hX0]; split_ifs
        · exact hY₀W
        · simpa using hY₀
      rw [heq]
      exact Basal.union hq0 hq (Disjoint.mono_left hX0sub (hdisj₁ _ (hY'U₁.union (hfresh' (fun s => q s.1)))))
    have hcardU₁ : U₁.card ≤ U.card + (2 * h - 2) := hcard₀
    refine ⟨Y₀ ∪ Y', ap, U', hUU₁.trans hU₁U', ?_, ?_, ?_, hmode sgn hY'pos, hmode (fun o => ¬ sgn o) hY'neg, ?_, ?_,
      hY₀U.union (hY'U.anti hUU₁),
      ((hin₁.subset Finset.subset_union_left).mono hU₁U').union hY'in, ?_, ?_, hU'Z⟩
    · rw [hcardins]
      have : U.card + (O.card + 1) * (2 * h - 2) = U.card + (2 * h - 2) + O.card * (2 * h - 2) :=
        by ring
      omega
    · intro s hs
      rw [mem_occSlots, Finset.mem_insert] at hs
      obtain ⟨hs1 | hs1, hs2⟩ := hs
      · obtain ⟨o', e⟩ := s
        simp only at hs1 hs2; subst hs1
        rw [hap_o]
        obtain ⟨h1, h2, h3⟩ := hap₀ e hs2
        exact ⟨h1, hU₁U' (hap₀U₁ e hs2), h2, h3⟩
      · have hs' : s ∈ occSlots O tri := mem_occSlots.2 ⟨hs1, hs2⟩
        rw [hap_O s hs']
        obtain ⟨h1, h2, h3, h4⟩ := hap' s hs'
        exact ⟨fun h' => h1 (hUU₁ h'), h2, h3, h4⟩
    · intro s hs s' hs' hss'
      rw [mem_occSlots, Finset.mem_insert] at hs hs'
      obtain ⟨hs1 | hs1, hs2⟩ := hs <;> obtain ⟨hs1' | hs1', hs2'⟩ := hs'
      · obtain ⟨o₁, e₁⟩ := s; obtain ⟨o₂, e₂⟩ := s'
        simp only at hs1 hs2 hs1' hs2' hss'; subst hs1; subst hs1'
        rw [hap_o, hap_o] at hss'
        rw [hinj₀ e₁ hs2 e₂ hs2' hss']
      · exfalso
        obtain ⟨o₁, e₁⟩ := s
        simp only at hs1 hs2 hss'; subst hs1
        have hs'' : s' ∈ occSlots O tri := mem_occSlots.2 ⟨hs1', hs2'⟩
        rw [hap_o, hap_O s' hs''] at hss'
        exact (hap' s' hs'').1 (hss' ▸ hap₀U₁ e₁ hs2)
      · exfalso
        obtain ⟨o₂, e₂⟩ := s'
        simp only at hs1' hs2' hss'; subst hs1'
        have hs'' : s ∈ occSlots O tri := mem_occSlots.2 ⟨hs1, hs2⟩
        rw [hap_o, hap_O s hs''] at hss'
        exact (hap' s hs'').1 (hss' ▸ hap₀U₁ e₂ hs2')
      · have h1 : s ∈ occSlots O tri := mem_occSlots.2 ⟨hs1, hs2⟩
        have h2 : s' ∈ occSlots O tri := mem_occSlots.2 ⟨hs1', hs2'⟩
        rw [hap_O s h1, hap_O s' h2] at hss'
        exact hinj' s h1 s' h2 hss'
    · rw [hWall]
      refine Finset.disjoint_union_left.2 ⟨Finset.disjoint_union_right.2 ⟨hY₀Wd, ?_⟩,
        Finset.disjoint_union_right.2 ⟨?_, hY'Wd⟩⟩
      · exact Disjoint.mono_left Finset.subset_union_left (hdisj₁ _ hfreshall)
      · exact (Disjoint.mono_left Finset.subset_union_right (hdisj₁ _ hY'U₁)).symm
    · rw [hWall]
      have h1 := Finset.disjoint_union_left.1 hY₀B
      have h2 := Finset.disjoint_union_left.1 hY'B
      have heq : Y₀ ∪ Y' ∪ (W₀ ∪ (occSlots O tri).biUnion (fun s => wedgeOf s.2 (ap' s))) =
          (Y₀ ∪ W₀) ∪ (Y' ∪ (occSlots O tri).biUnion (fun s => wedgeOf s.2 (ap' s))) := by
        ext; simp only [Finset.mem_union]; tauto
      rw [heq]
      exact Finset.disjoint_union_left.2 ⟨hY₀B, hY'B⟩
    · rw [hcardins, Nat.succ_mul]
      exact (Finset.card_union_le _ _).trans (by omega)

    · have hLocal : supportIncrementCost ι R U U₁ =
          supportIncrementCost ι R U (support (Y₀ ∪ W₀)) := by
        unfold supportIncrementCost Pasch.supportIncrementCost
        dsimp only [U₁]
        rw [map_union,←union_assoc,union_self]
      have hPay0 : (supportIncrementCost ι R U U₁:ℝ) ≤ gadgetPotentialCost ι α h Ub L := by
        simpa only [hLocal] using hPay₀
      have hSplit : supportIncrementCost ι R U U' =
          supportIncrementCost ι R U U₁+supportIncrementCost ι R U₁ U' := by
        simpa only [union_eq_right.mpr hU₁U',union_eq_right.mpr hUU₁] using
          supportIncrementCost_union ι R U U₁ U'
      have hSplitReal : (supportIncrementCost ι R U U':ℝ) =
          (supportIncrementCost ι R U U₁:ℝ)+(supportIncrementCost ι R U₁ U':ℝ) := by exact_mod_cast hSplit
      calc (supportIncrementCost ι R U U':ℝ) =
            (supportIncrementCost ι R U U₁:ℝ)+(supportIncrementCost ι R U₁ U':ℝ) := hSplitReal
        _ ≤ gadgetPotentialCost ι α h Ub L+(O.card:ℝ)*gadgetPotentialCost ι α h Ub L :=
          add_le_add hPay0 hPay'
        _ = ((insert o O).card:ℝ)*gadgetPotentialCost ι α h Ub L := by
          rw [hcardins,Nat.cast_add,Nat.cast_one]
          ring

theorem pairing_phase_avoiding_vertices_with_support_budget (ι : V ↪ Ω) {H : Host V I} {F : Set (Multiset I)} {α : ℝ} {h : ℕ}
    (hα : 0 < α) (hH3 : CommonNbrCond H F α) (hH4 : HingeCond H F α h)
    (R : Finset (Finset Ω)) (L : ℕ) (hL : PairCodegreeBound R L) (Z : Finset V)
    (B : Finset (Sym2 V)) (d : ℕ) (hdeg : ∀ x, degIn B x ≤ d) (P : Finset (Sym2 V))
    (base : σ → Sym2 V) (ap : σ → V) (pos : σ → Prop) (Ub : ℕ)
    (hwin1 : (Ub : ℝ) + Z.card + 2 + 4 * d ≤ α/2 * Fintype.card V)
    (hwin2 : ((Ub : ℝ) + Z.card + h + 5 * d) * 2 ^ Nat.choose h 2 ≤ α / 2 * Fintype.card V) :
    ∀ (N : ℕ) (Sl : Finset σ) (U : Finset V), Disjoint U Z →
      (Sl.filter (fun s => ¬ pos s)).card ≤ N → U.card + N * (2 * h - 3) ≤ Ub →
      SlotFamily H F base ap Sl U P → SlotCount base pos Sl P →
      ∃ J, Basal H F (J ∪ (Sl.filter (fun s => ¬ pos s)).biUnion
          (fun s => wedgeOf (base s) (ap s))) ∧
        Basal H F (J ∪ (Sl.filter pos).biUnion (fun s => wedgeOf (base s) (ap s)) ∪ P) ∧
        Disjoint J B ∧ Fresh U J ∧ (U ∪ support J).card ≤ U.card + N * (2 * h - 3) ∧
        J.card ≤ N * (2 * h - 2).choose 2 ∧
        (supportIncrementCost ι R U (support J):ℝ) ≤ (N:ℝ)*compositePotentialCost ι α h Ub L ∧ Disjoint (support J) Z := by
  have hCostNonneg : 0 ≤ compositePotentialCost ι α h Ub L := by
    unfold compositePotentialCost hingePotentialCost apexPotentialCost orderRatio
    positivity
  intro N
  induction N with
  | zero =>
    intro Sl U hUZ hN _ hS hC
    have hneg : Sl.filter (fun s => ¬ pos s) = ∅ := Finset.card_eq_zero.1 (by omega)
    refine ⟨∅, ?_, ?_, by simp, fun e he => by simp at he, by simp [support], by simp, ?_, by simp [support]⟩
    · rw [hneg]; simpa using Basal.empty H F
    · simpa using basal_pos_slots hS hC hneg
    · have hz : supportIncrementCost ι R U ∅ ≤ 0 := by
        simpa only [supportIncrementCost_self] using supportIncrementCost_mono ι R U (empty_subset U)
      have hzR : (supportIncrementCost ι R U ∅:ℝ) ≤ 0 := by exact_mod_cast hz
      simpa [support] using hzR
  | succ N ih =>
    intro Sl U hUZ hN hU hS hC
    by_cases hneg : Sl.filter (fun s => ¬ pos s) = ∅
    · refine ⟨∅, ?_, ?_, by simp, fun e he => by simp at he, by simp [support], by simp, ?_, by simp [support]⟩
      · rw [hneg]; simpa using Basal.empty H F
      · simpa using basal_pos_slots hS hC hneg
      · have hz : supportIncrementCost ι R U ∅ ≤ 0 := by
          simpa only [supportIncrementCost_self] using supportIncrementCost_mono ι R U (empty_subset U)
        have hzR : (supportIncrementCost ι R U ∅:ℝ) ≤ 0 := by exact_mod_cast hz
        simpa [support] using hzR.trans (mul_nonneg (Nat.cast_nonneg (N+1)) hCostNonneg)
    obtain ⟨sn, hsn⟩ := Finset.nonempty_iff_ne_empty.2 hneg
    rw [Finset.mem_filter] at hsn
    -- un slot positivo con la misma base
    obtain ⟨sp, hsp⟩ : (Sl.filter (fun s => pos s ∧ base s = base sn)).Nonempty := by
      rw [← Finset.card_pos]
      have h1 := hC (base sn)
      have h2 : 0 < (Sl.filter (fun s => ¬ pos s ∧ base s = base sn)).card :=
        Finset.card_pos.2 ⟨sn, Finset.mem_filter.2 ⟨hsn.1, hsn.2, rfl⟩⟩
      split_ifs at h1 <;> omega
    rw [Finset.mem_filter] at hsp
    obtain ⟨hspS, hspp, hspb⟩ := hsp
    have hne : sn ≠ sp := fun h' => hsn.2 (h' ▸ hspp)
    obtain ⟨u, v, he⟩ := Sym2.exists_mk_eq (base sn)
    have hTn := (hS.tri sn hsn.1).2.2
    have hTp := (hS.tri sp hspS).2.2
    rw [he, slotTri_mk] at hTn
    rw [hspb, he, slotTri_mk] at hTp
    have hab : ap sn ≠ ap sp := fun h' => hne (hS.inj sn hsn.1 sp hspS h')
    have hUb : (U.card : ℝ) ≤ Ub := by
      have : U.card ≤ Ub := by nlinarith
      exact_mod_cast this
    have hRoots : ({u,v,ap sn,ap sp}:Finset V) ⊆ U := by
      intro x hx
      simp only [mem_insert,mem_singleton] at hx
      rcases hx with rfl | rfl | rfl | rfl
      · exact (hS.inside sn hsn.1).1 _ (by rw [he]; simp)
      · exact (hS.inside sn hsn.1).1 _ (by rw [he]; simp)
      · exact (hS.inside sn hsn.1).2
      · exact (hS.inside sp hspS).2
    obtain ⟨J₀, hJ₀, hJ₀B, hJ₀ab, hJ₀U, hJ₀c, hPay₀, hNoZ₀⟩ :=
      exists_low_cost_composite_hinge_avoiding_vertices ι hα hH3 hH4 hab hTn hTp R L hL
        U Ub (by exact_mod_cast hUb) hRoots Z hUZ B d hdeg hwin1 hwin2
    set Sl' := (Sl.erase sn).erase sp
    set U' := U ∪ support J₀
    have hU'Z : Disjoint U' Z := disjoint_union_left.mpr ⟨hUZ,hNoZ₀⟩
    have hSl'sub : Sl' ⊆ Sl := (Finset.erase_subset _ _).trans (Finset.erase_subset _ _)
    have hsnSl' : sn ∉ Sl' := fun h' => by
      simp [Sl'] at h'
    have hspSl' : sp ∉ Sl' := fun h' => by simp [Sl'] at h'
    have hU'c : U'.card ≤ U.card + (2 * h - 3) :=
      (Finset.card_union_le _ _).trans (Nat.add_le_add_left hJ₀c _)
    have hS' : SlotFamily H F base ap Sl' U' P := hS.mono hSl'sub Finset.subset_union_left
    have hC' : SlotCount base pos Sl' P := by
      intro e
      have h1 := filter_erase_erase_card (Sl := Sl) (p := fun s => pos s ∧ base s = e) hne
      have h2 := filter_erase_erase_card (Sl := Sl) (p := fun s => ¬ pos s ∧ base s = e) hne
      have h3 := hC e
      by_cases hb : base sn = e
      · rw [if_neg (fun h' => hsn.2 h'.2.1), if_pos ⟨hspS, hspp, hspb.trans hb⟩] at h1
        rw [if_pos ⟨hsn.1, hsn.2, hb⟩, if_neg (fun h' => h'.2.1 hspp)] at h2
        simp only [Sl']
        split_ifs at h3 ⊢ <;> omega
      · have hb' : base sp ≠ e := hspb ▸ hb
        rw [if_neg (fun h' => hb h'.2.2), if_neg (fun h' => hb' h'.2.2)] at h1
        rw [if_neg (fun h' => hb h'.2.2), if_neg (fun h' => hb' h'.2.2)] at h2
        simp only [Sl']
        split_ifs at h3 ⊢ <;> omega
    have hN' : (Sl'.filter (fun s => ¬ pos s)).card ≤ N := by
      have h1 := filter_erase_erase_card (Sl := Sl) (p := fun s => ¬ pos s) hne
      rw [if_pos ⟨hsn.1, hsn.2⟩, if_neg (fun h' => h'.2 hspp)] at h1
      simp only [Sl']; omega
    have hU' : U'.card + N * (2 * h - 3) ≤ Ub := by
      have : U.card + (N + 1) * (2 * h - 3) = U.card + (2 * h - 3) + N * (2 * h - 3) := by ring
      omega
    obtain ⟨J', hJ'neg, hJ'pos, hJ'B, hJ'U, hJ'c, hJ'e, hPay', hNoZ'⟩ := ih Sl' U' hU'Z hN' hU' hS' hC'
    have hJ₀e : J₀.card ≤ (2 * h - 2).choose 2 := by
      have h6 : 6 ≤ h := by
        obtain ⟨i, hi6, hih, -⟩ := hH4 u v (ap sn) (ap sp) hab hTn hTp
        omega
      have := card_le_choose_of_support_le hJ₀c
      rwa [show 2 * h - 3 + 1 = 2 * h - 2 by omega] at this
    -- piezas
    have hJ₀fresh : Fresh U J₀ := hJ₀.fresh hJ₀ab U hJ₀U
    have hJ₀in : Inside U' J₀ := (inside_support J₀).mono Finset.subset_union_right
    have hWn : wedgeOf (base sn) (ap sn) = wedge u v (ap sn) := by rw [he, wedgeOf_mk]
    have hWp : wedgeOf (base sp) (ap sp) = wedge u v (ap sp) := by rw [hspb, he, wedgeOf_mk]
    have hWnin : Inside U (wedgeOf (base sn) (ap sn)) :=
      inside_wedgeOf (hS.inside sn hsn.1).1 (hS.inside sn hsn.1).2
    have hWpin : Inside U (wedgeOf (base sp) (ap sp)) :=
      inside_wedgeOf (hS.inside sp hspS).1 (hS.inside sp hspS).2
    have hnegeq : Sl.filter (fun s => ¬ pos s) = insert sn (Sl'.filter (fun s => ¬ pos s)) := by
      ext s
      simp only [Finset.mem_filter, Finset.mem_insert, Sl', Finset.mem_erase]
      constructor
      · rintro ⟨hs, hps⟩
        by_cases h1 : s = sn
        · exact Or.inl h1
        · exact Or.inr ⟨⟨fun h2 => hps (h2 ▸ hspp), h1, hs⟩, hps⟩
      · rintro (rfl | ⟨⟨-, -, hs⟩, hps⟩)
        · exact ⟨hsn.1, hsn.2⟩
        · exact ⟨hs, hps⟩
    have hposeq : Sl.filter pos = insert sp (Sl'.filter pos) := by
      ext s
      simp only [Finset.mem_filter, Finset.mem_insert, Sl', Finset.mem_erase]
      constructor
      · rintro ⟨hs, hps⟩
        by_cases h1 : s = sp
        · exact Or.inl h1
        · exact Or.inr ⟨⟨h1, fun h2 => hsn.2 (h2 ▸ hps), hs⟩, hps⟩
      · rintro (rfl | ⟨⟨-, -, hs⟩, hps⟩)
        · exact ⟨hspS, hspp⟩
        · exact ⟨hs, hps⟩
    have hnegsub : Sl'.filter (fun s => ¬ pos s) ⊆ Sl := (Finset.filter_subset _ _).trans hSl'sub
    have hpossub : Sl'.filter pos ⊆ Sl := (Finset.filter_subset _ _).trans hSl'sub
    refine ⟨J₀ ∪ J', ?_, ?_, Finset.disjoint_union_left.2 ⟨hJ₀B, hJ'B⟩,
      hJ₀fresh.union (hJ'U.anti Finset.subset_union_left), ?_, ?_, ?_,
      by rw [support_union]; exact disjoint_union_left.mpr ⟨hNoZ₀,hNoZ'⟩⟩
    · rw [hnegeq, Finset.biUnion_insert]
      have heq : J₀ ∪ J' ∪ (wedgeOf (base sn) (ap sn) ∪
          (Sl'.filter (fun s => ¬ pos s)).biUnion (fun s => wedgeOf (base s) (ap s))) =
          (J₀ ∪ wedgeOf (base sn) (ap sn)) ∪
          (J' ∪ (Sl'.filter (fun s => ¬ pos s)).biUnion (fun s => wedgeOf (base s) (ap s))) := by
        ext; simp only [Finset.mem_union]; tauto
      rw [heq]
      refine Basal.union (by rw [hWn]; exact hJ₀.2.2.1) hJ'neg ?_
      refine Finset.disjoint_union_left.2 ⟨Finset.disjoint_union_right.2 ⟨?_, ?_⟩,
        Finset.disjoint_union_right.2 ⟨?_, ?_⟩⟩
      · exact hJ₀in.disjoint_fresh hJ'U
      · exact ((hS.inside_wedges _ hnegsub).disjoint_fresh hJ₀fresh).symm
      · exact (hWnin.mono Finset.subset_union_left).disjoint_fresh hJ'U
      · exact hS.wedge_disjoint_biUnion hsn.1 _ hnegsub (fun h' => hsnSl'
          (Finset.mem_filter.1 h').1)
    · rw [hposeq, Finset.biUnion_insert]
      have heq : J₀ ∪ J' ∪ (wedgeOf (base sp) (ap sp) ∪
          (Sl'.filter pos).biUnion (fun s => wedgeOf (base s) (ap s))) ∪ P =
          (J₀ ∪ wedgeOf (base sp) (ap sp)) ∪
          (J' ∪ (Sl'.filter pos).biUnion (fun s => wedgeOf (base s) (ap s)) ∪ P) := by
        ext; simp only [Finset.mem_union]; tauto
      rw [heq]
      refine Basal.union (by rw [hWp]; exact hJ₀.2.2.2) hJ'pos ?_
      refine Finset.disjoint_union_left.2 ⟨Finset.disjoint_union_right.2
        ⟨Finset.disjoint_union_right.2 ⟨?_, ?_⟩, ?_⟩, Finset.disjoint_union_right.2
        ⟨Finset.disjoint_union_right.2 ⟨?_, ?_⟩, ?_⟩⟩
      · exact hJ₀in.disjoint_fresh hJ'U
      · exact ((hS.inside_wedges _ hpossub).disjoint_fresh hJ₀fresh).symm
      · exact (hS.insideP.disjoint_fresh hJ₀fresh).symm
      · exact (hWpin.mono Finset.subset_union_left).disjoint_fresh hJ'U
      · exact hS.wedge_disjoint_biUnion hspS _ hpossub (fun h' => hspSl'
          (Finset.mem_filter.1 h').1)
      · rw [Finset.disjoint_right]
        intro f hf
        exact not_mem_wedgeOf_of_not_mem (hS.apexP f hf sp hspS)
    · have heq : U ∪ support (J₀ ∪ J') = U' ∪ support J' := by
        rw [support_union]; simp only [U', Finset.union_assoc]
      rw [heq]
      have : U.card + (N + 1) * (2 * h - 3) = U.card + (2 * h - 3) + N * (2 * h - 3) := by ring
      omega
    · refine (Finset.card_union_le _ _).trans ?_
      rw [Nat.succ_mul]
      omega

    · rw [support_union,supportIncrementCost_union,Nat.cast_add]
      change (supportIncrementCost ι R U (support J₀):ℝ)+
        (supportIncrementCost ι R U' (support J'):ℝ) ≤ _
      calc (supportIncrementCost ι R U (support J₀):ℝ)+
            (supportIncrementCost ι R U' (support J'):ℝ)
          ≤ compositePotentialCost ι α h Ub L+(N:ℝ)*compositePotentialCost ι α h Ub L :=
            add_le_add hPay₀ hPay'
        _ = ((N+1:ℕ):ℝ)*compositePotentialCost ι α h Ub L := by push_cast; ring


theorem slot_absorber_avoiding_vertices_with_support_budget (ι : V ↪ Ω) {H : Host V I} {F : Set (Multiset I)} {α : ℝ} {h : ℕ}
    (hα : 0 < α) (hH3 : CommonNbrCond H F α) (hH4 : HingeCond H F α h)
    (R : Finset (Finset Ω)) (L : ℕ) (hL : PairCodegreeBound R L) (Bad : Finset V)
    (B : Finset (Sym2 V)) (d : ℕ) (hdeg : ∀ x, degIn B x ≤ d) (P : Finset (Sym2 V))
    (O : Finset τ) (tri : τ → Finset V) (sgn : τ → Prop) (hO : ∀ o ∈ O, IsAllowed H F (tri o))
    (hOBad : ∀ o ∈ O, Disjoint (tri o) Bad)
    (hcert : ∀ e, ((O.filter (fun o => sgn o ∧ e ∈ triEdges (tri o))).card : ℤ) =
      (O.filter (fun o => ¬ sgn o ∧ e ∈ triEdges (tri o))).card + if e ∈ P then 1 else 0)
    (Z : Finset V) (hZBad : Disjoint Z Bad) (hPZ : Inside Z P) (Ub : ℕ)
    (hUb : (Z ∪ O.biUnion tri).card + O.card * (2 * h - 2) + 3 * O.card * (2 * h - 3) ≤ Ub)
    (hwin1 : (Ub : ℝ) + Bad.card + 3 + 4 * d ≤ α/2 * Fintype.card V)
    (hwin2 : ((Ub : ℝ) + Bad.card + 1 + h + 5 * d) * 2 ^ Nat.choose h 2 ≤ α / 2 * Fintype.card V) :
    ∃ A, IsAbsorber H F A P ∧ Disjoint A B ∧ Fresh (Z ∪ O.biUnion tri) A ∧
      ((Z ∪ O.biUnion tri) ∪ support A).card ≤
        (Z ∪ O.biUnion tri).card + O.card * (2 * h - 2) + 3 * O.card * (2 * h - 3) ∧
      A.card ≤ O.card * (4 * (2 * h - 2).choose 2 + 6) ∧
      (supportIncrementCost ι R (Z ∪ O.biUnion tri) (support A):ℝ) ≤
        (O.card:ℝ)*absorptionPotentialCost ι α h Ub L ∧ Disjoint (support A) Bad := by
  set U₀ := Z ∪ O.biUnion tri
  have htriU₀ : ∀ o ∈ O, tri o ⊆ U₀ := fun o ho =>
    (Finset.subset_biUnion_of_mem tri ho).trans Finset.subset_union_right
  have hZU₀ : Z ⊆ U₀ := Finset.subset_union_left
  have hU₀Bad : Disjoint U₀ Bad := by
    apply disjoint_union_left.mpr
    refine ⟨hZBad,?_⟩
    apply disjoint_left.mpr
    intro v hv hb
    obtain ⟨o,ho,hv⟩ := mem_biUnion.mp hv
    exact disjoint_left.mp (hOBad o ho) hv hb
  obtain ⟨Y, ap, U₁, hU₀₁, hU₁c, hap, hinj, hYpos, hYneg, hYWd, hYB, hYU₀, hYin, hYe, hGadgetPay, hU₁Bad⟩ :=
    gadget_phase_avoiding_vertices_with_support_budget ι hα hH3 hH4 R L hL Bad B d hdeg tri sgn Ub hwin1 hwin2 O U₀ hU₀Bad
      (fun o ho => ⟨hO o ho, htriU₀ o ho⟩) (by omega)
  set Sl := occSlots O tri
  have hbaseU₀ : ∀ s ∈ Sl, ∀ p ∈ s.2, p ∈ U₀ := fun s hs p hp =>
    htriU₀ _ (mem_occSlots.1 hs).1 (mem_of_mem_triEdges (mem_occSlots.1 hs).2 hp)
  have hSF : SlotFamily H F Prod.snd ap Sl U₁ P :=
    ⟨fun s hs => ⟨not_isDiag_of_mem_triEdges (mem_occSlots.1 hs).2, (hap s hs).2.2.1,
      (hap s hs).2.2.2⟩, hinj, fun s hs s' hs' h' => (hap s hs).1 (hbaseU₀ s' hs' _ h'),
      fun s hs => ⟨fun p hp => hU₀₁ (hbaseU₀ s hs p hp), (hap s hs).2.1⟩,
      (hPZ.mono hZU₀).mono hU₀₁, fun e he s hs h' => (hap s hs).1 (hZU₀ (hPZ e he _ h'))⟩
  have hSC : SlotCount Prod.snd (fun s : τ × Sym2 V => sgn s.1) Sl P := by
    intro e
    have h1 := occSlots_filter_card (O := O) (tri := tri) sgn e
    have h2 := occSlots_filter_card (O := O) (tri := tri) (fun o => ¬ sgn o) e
    rw [h1, h2]; exact hcert e
  have hN : (Sl.filter (fun s => ¬ sgn s.1)).card ≤ 3 * O.card :=
    (Finset.card_filter_le _ _).trans (occSlots_card_le (fun o ho => (hO o ho).1))
  obtain ⟨J, hJneg, hJpos, hJB, hJU₁, hJc, hJe, hPairPay, hJBad⟩ :=
    pairing_phase_avoiding_vertices_with_support_budget ι hα hH3 hH4 R L hL Bad B d hdeg P Prod.snd ap (fun s => sgn s.1) Ub (by linarith)
      (le_trans (mul_le_mul_of_nonneg_right (by linarith) (by positivity)) hwin2)
      (3 * O.card) Sl U₁ hU₁Bad hN (by nlinarith) hSF hSC
  set Wpos := (Sl.filter (fun s => sgn s.1)).biUnion (fun s => wedgeOf s.2 (ap s))
  set Wneg := (Sl.filter (fun s => ¬ sgn s.1)).biUnion (fun s => wedgeOf s.2 (ap s))
  have hWall : Sl.biUnion (fun s => wedgeOf s.2 (ap s)) = Wpos ∪ Wneg := by
    show _ = (Sl.filter _).biUnion _ ∪ (Sl.filter _).biUnion _
    rw [← Finset.union_biUnion, Finset.filter_union_filter_not_eq]
  have hWposneg : Disjoint Wpos Wneg := by
    rw [Finset.disjoint_biUnion_left]
    intro s hs
    exact hSF.wedge_disjoint_biUnion (Finset.mem_filter.1 hs).1 _ (Finset.filter_subset _ _)
      (fun h' => (Finset.mem_filter.1 h').2 (Finset.mem_filter.1 hs).2)
  have hWposin : Inside U₁ Wpos := hSF.inside_wedges _ (Finset.filter_subset _ _)
  have hWnegin : Inside U₁ Wneg := hSF.inside_wedges _ (Finset.filter_subset _ _)
  have hYWpos : Disjoint Y Wpos := Disjoint.mono_right (by rw [hWall]; exact
    Finset.subset_union_left) hYWd
  have hYWneg : Disjoint Y Wneg := Disjoint.mono_right (by rw [hWall]; exact
    Finset.subset_union_right) hYWd
  have hPU₁ : Inside U₁ P := hSF.insideP
  have hWP : ∀ X ⊆ Sl, Disjoint (X.biUnion (fun s => wedgeOf s.2 (ap s))) P := by
    intro X hX
    rw [Finset.disjoint_biUnion_left]
    intro s hs
    rw [Finset.disjoint_right]
    intro f hf
    exact not_mem_wedgeOf_of_not_mem (hSF.apexP f hf s (hX hs))
  have hYP : Disjoint Y P := ((hPZ.mono hZU₀).disjoint_fresh hYU₀).symm
  have hJP : Disjoint J P := (hPU₁.disjoint_fresh hJU₁).symm
  refine ⟨Y ∪ (Wpos ∪ Wneg) ∪ J, ⟨?_, ?_, ?_⟩, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · refine Finset.disjoint_union_left.2 ⟨Finset.disjoint_union_left.2 ⟨hYP,
      Finset.disjoint_union_left.2 ⟨hWP _ (Finset.filter_subset _ _),
        hWP _ (Finset.filter_subset _ _)⟩⟩, hJP⟩
  · have heq : Y ∪ (Wpos ∪ Wneg) ∪ J = (Y ∪ Wpos) ∪ (J ∪ Wneg) := by
      ext; simp only [Finset.mem_union]; tauto
    rw [heq]
    refine Basal.union hYpos hJneg ?_
    refine Finset.disjoint_union_left.2 ⟨Finset.disjoint_union_right.2
      ⟨hYin.disjoint_fresh hJU₁, hYWneg⟩, Finset.disjoint_union_right.2
      ⟨hWposin.disjoint_fresh hJU₁, hWposneg⟩⟩
  · have heq : Y ∪ (Wpos ∪ Wneg) ∪ J ∪ P = (Y ∪ Wneg) ∪ (J ∪ Wpos ∪ P) := by
      ext; simp only [Finset.mem_union]; tauto
    rw [heq]
    refine Basal.union hYneg hJpos ?_
    refine Finset.disjoint_union_left.2 ⟨Finset.disjoint_union_right.2
      ⟨Finset.disjoint_union_right.2 ⟨hYin.disjoint_fresh hJU₁, hYWpos⟩, hYP⟩,
      Finset.disjoint_union_right.2 ⟨Finset.disjoint_union_right.2
      ⟨hWnegin.disjoint_fresh hJU₁, hWposneg.symm⟩, hWP _ (Finset.filter_subset _ _)⟩⟩
  · rw [← hWall]
    exact Finset.disjoint_union_left.2 ⟨hYB, hJB⟩
  · rw [← hWall]
    exact (hYU₀.union (fresh_wedges (fun s hs => (hap s hs).1))).union (hJU₁.anti hU₀₁)
  · have hsub : U₀ ∪ support (Y ∪ (Wpos ∪ Wneg) ∪ J) ⊆ U₁ ∪ support J := by
      rw [support_union, support_union, support_union]
      intro w hw
      simp only [Finset.mem_union] at hw ⊢
      rcases hw with hw | ((hw | hw | hw) | hw)
      · exact Or.inl (hU₀₁ hw)
      · exact Or.inl (support_subset_of_inside hYin hw)
      · exact Or.inl (support_subset_of_inside hWposin hw)
      · exact Or.inl (support_subset_of_inside hWnegin hw)
      · exact Or.inr hw
    refine (Finset.card_le_card hsub).trans (hJc.trans ?_)
    omega
  · have hSl : Sl.card ≤ 3 * O.card := occSlots_card_le (fun o ho => (hO o ho).1)
    have hW : (Wpos ∪ Wneg).card ≤ 2 * Sl.card := by
      rw [← hWall]
      refine Finset.card_biUnion_le.trans ?_
      rw [mul_comm, ← smul_eq_mul, ← Finset.sum_const]
      refine Finset.sum_le_sum fun s _ => ?_
      refine Finset.card_image_le.trans ?_
      induction s.2 using Sym2.ind with
      | _ x y => rw [Sym2.toFinset_mk_eq]; exact Finset.card_le_two
    refine (Finset.card_union_le _ _).trans ?_
    refine (Nat.add_le_add_right (Finset.card_union_le _ _) _).trans ?_
    have : 3 * O.card * (2 * h - 2).choose 2 = O.card * (3 * (2 * h - 2).choose 2) := by ring
    nlinarith

  · have hInsideAll : Inside (U₁ ∪ support J) (Y ∪ (Wpos ∪ Wneg) ∪ J) :=
      ((hYin.mono subset_union_left).union
        ((hWposin.mono subset_union_left).union (hWnegin.mono subset_union_left))).union
        ((inside_support J).mono subset_union_right)
    have hMono := supportIncrementCost_mono ι R U₀ (support_subset_of_inside hInsideAll)
    have hLedger : supportIncrementCost ι R U₀ (U₁ ∪ support J) =
        supportIncrementCost ι R U₀ U₁+supportIncrementCost ι R U₁ (support J) := by
      simpa only [union_eq_right.mpr hU₀₁] using supportIncrementCost_union ι R U₀ U₁ (support J)
    have hReal : (supportIncrementCost ι R U₀ (support (Y ∪ (Wpos ∪ Wneg) ∪ J)):ℝ) ≤
        (supportIncrementCost ι R U₀ U₁:ℝ)+(supportIncrementCost ι R U₁ (support J):ℝ) := by
      exact_mod_cast hMono.trans_eq hLedger
    calc (supportIncrementCost ι R U₀ (support (Y ∪ (Wpos ∪ Wneg) ∪ J)):ℝ)
        ≤ (supportIncrementCost ι R U₀ U₁:ℝ)+(supportIncrementCost ι R U₁ (support J):ℝ) := hReal
      _ ≤ (O.card:ℝ)*gadgetPotentialCost ι α h Ub L+
          ((3*O.card:ℕ):ℝ)*compositePotentialCost ι α h Ub L := add_le_add hGadgetPay hPairPay
      _ = (O.card:ℝ)*absorptionPotentialCost ι α h Ub L := by
        unfold absorptionPotentialCost
        push_cast
        ring

  · apply disjoint_left.mpr
    intro v hv hvBad
    rw [support_union,support_union,support_union] at hv
    simp only [mem_union] at hv
    rcases hv with (hv | hv | hv) | hv
    · exact disjoint_left.mp hU₁Bad (support_subset_of_inside hYin hv) hvBad
    · exact disjoint_left.mp hU₁Bad (support_subset_of_inside hWposin hv) hvBad
    · exact disjoint_left.mp hU₁Bad (support_subset_of_inside hWnegin hv) hvBad
    · exact disjoint_left.mp hJBad hv hvBad

theorem slot_absorber_of_coeffs_avoiding_vertices_with_support_budget (ι : V ↪ Ω) {H : Host V I} {F : Set (Multiset I)} {α : ℝ} {h : ℕ}
    (hα : 0 < α) (hH3 : CommonNbrCond H F α) (hH4 : HingeCond H F α h)
    (R : Finset (Finset Ω)) (L : ℕ) (hL : PairCodegreeBound R L) (Bad : Finset V)
    (B : Finset (Sym2 V)) (d : ℕ) (hdeg : ∀ x, degIn B x ≤ d) (P : Finset (Sym2 V))
    (S : Finset (Finset V)) (hS : ∀ T ∈ S, IsAllowed H F T) (c : Finset V → ℤ)
    (hSBad : ∀ T ∈ S, c T ≠ 0 → Disjoint T Bad)
    (hP : ∀ e, ind P e = ∑ T ∈ S, c T * ind (triEdges T) e) (K : ℕ)
    (hK : ∑ T ∈ S, (c T).natAbs ≤ K) (Z : Finset V) (hZBad : Disjoint Z Bad) (hPZ : Inside Z P) (Ub : ℕ)
    (hUb : (Z ∪ (S.filter (fun T => c T ≠ 0)).biUnion id).card + K * (2 * h - 2) +
      3 * K * (2 * h - 3) ≤ Ub)
    (hwin1 : (Ub : ℝ) + Bad.card + 3 + 4 * d ≤ α/2 * Fintype.card V)
    (hwin2 : ((Ub : ℝ) + Bad.card + 1 + h + 5 * d) * 2 ^ Nat.choose h 2 ≤ α / 2 * Fintype.card V) :
    ∃ A, IsAbsorber H F A P ∧ Disjoint A B ∧
      Fresh (Z ∪ (S.filter (fun T => c T ≠ 0)).biUnion id) A ∧
      ((Z ∪ (S.filter (fun T => c T ≠ 0)).biUnion id) ∪ support A).card ≤
        (Z ∪ (S.filter (fun T => c T ≠ 0)).biUnion id).card + K * (2 * h - 2) +
          3 * K * (2 * h - 3) ∧
      A.card ≤ K * (4 * (2 * h - 2).choose 2 + 6) ∧
      (supportIncrementCost ι R (Z ∪ (S.filter (fun T => c T ≠ 0)).biUnion id) (support A):ℝ) ≤
        (K:ℝ)*absorptionPotentialCost ι α h Ub L ∧ Disjoint (support A) Bad := by
  set O := coeffOcc S c
  have hOS : O.biUnion Prod.fst = (S.filter (fun T => c T ≠ 0)).biUnion id := by
    ext x
    simp only [Finset.mem_biUnion, mem_coeffOcc, Finset.mem_filter, id, O]
    constructor
    · rintro ⟨⟨T, j⟩, ⟨hT, hj⟩, hx⟩
      exact ⟨T, ⟨hT, fun h0 => by simp [h0] at hj⟩, hx⟩
    · rintro ⟨T, ⟨hT, hc⟩, hx⟩
      exact ⟨(T, 0), ⟨hT, by simpa [Int.natAbs_pos] using hc⟩, hx⟩
  have hOcard : O.card ≤ K := by
    have := coeffOcc_filter_card S c (fun _ => True)
    simp only [Finset.filter_true] at this
    show (coeffOcc S c).card ≤ K
    rw [this]; exact hK
  have hcert : ∀ e, ((O.filter (fun o => 0 < c o.1 ∧ e ∈ triEdges o.1)).card : ℤ) =
      (O.filter (fun o => ¬ 0 < c o.1 ∧ e ∈ triEdges o.1)).card + if e ∈ P then 1 else 0 := by
    intro e
    rw [coeffOcc_filter_card S c (fun T => 0 < c T ∧ e ∈ triEdges T),
      coeffOcc_filter_card S c (fun T => ¬ 0 < c T ∧ e ∈ triEdges T)]
    have hind : (if e ∈ P then (1 : ℤ) else 0) = ∑ T ∈ S.filter (fun T => e ∈ triEdges T), c T := by
      have := hP e
      simp only [ind] at this
      rw [this, Finset.sum_filter]
      exact Finset.sum_congr rfl fun T _ => by split_ifs <;> simp
    rw [hind, ← Finset.sum_filter_add_sum_filter_not (S.filter (fun T => e ∈ triEdges T))
      (fun T => 0 < c T), Finset.filter_filter, Finset.filter_filter]
    push_cast
    have h1 : ∑ T ∈ S.filter (fun T => 0 < c T ∧ e ∈ triEdges T), |c T| =
        ∑ T ∈ S.filter (fun T => e ∈ triEdges T ∧ 0 < c T), c T := by
      rw [show S.filter (fun T => e ∈ triEdges T ∧ 0 < c T) =
        S.filter (fun T => 0 < c T ∧ e ∈ triEdges T) from Finset.filter_congr (fun _ _ => and_comm)]
      exact Finset.sum_congr rfl fun T hT => by
        rw [abs_of_pos (Finset.mem_filter.1 hT).2.1]
    have h2 : ∑ T ∈ S.filter (fun T => ¬ 0 < c T ∧ e ∈ triEdges T), |c T| =
        -∑ T ∈ S.filter (fun T => e ∈ triEdges T ∧ ¬ 0 < c T), c T := by
      rw [show S.filter (fun T => e ∈ triEdges T ∧ ¬ 0 < c T) =
        S.filter (fun T => ¬ 0 < c T ∧ e ∈ triEdges T) from
          Finset.filter_congr (fun _ _ => and_comm), ← Finset.sum_neg_distrib]
      exact Finset.sum_congr rfl fun T hT => by
        rw [abs_of_nonpos (not_lt.1 (Finset.mem_filter.1 hT).2.1)]
    rw [h1, h2]; ring
  have hUb' : (Z ∪ O.biUnion Prod.fst).card + O.card * (2 * h - 2) +
      3 * O.card * (2 * h - 3) ≤ Ub := by
    rw [hOS]
    have := Nat.mul_le_mul_right (2 * h - 2) hOcard
    have := Nat.mul_le_mul_right (2 * h - 3) (Nat.mul_le_mul_left 3 hOcard)
    omega
  obtain ⟨A, hA, hAB, hAF, hAc, hAe, hPay, hAvoid⟩ := slot_absorber_avoiding_vertices_with_support_budget ι hα hH3 hH4 R L hL Bad B d hdeg P O Prod.fst
    (fun o => 0 < c o.1) (fun o ho => hS _ (mem_coeffOcc.1 ho).1)
    (fun o ho => hSBad o.1 (mem_coeffOcc.mp ho).1 (by
      intro hc0
      have hj := (mem_coeffOcc.mp ho).2
      simpa [hc0] using hj)) (fun e => by convert hcert e)
    Z hZBad hPZ Ub hUb' hwin1 hwin2
  rw [hOS] at hAF hAc hPay
  refine ⟨A, hA, hAB, hAF, hAc.trans ?_, hAe.trans (Nat.mul_le_mul_right _ hOcard),
    hPay.trans (mul_le_mul_of_nonneg_right (by exact_mod_cast hOcard)
      (by unfold absorptionPotentialCost gadgetPotentialCost compositePotentialCost hingePotentialCost apexPotentialCost orderRatio; positivity)),hAvoid⟩
  have := Nat.mul_le_mul_right (2 * h - 2) hOcard
  have := Nat.mul_le_mul_right (2 * h - 3) (Nat.mul_le_mul_left 3 hOcard)
  omega



theorem surviving_certificate_weighted_absorber (ι : V ↪ Ω) {H : Host V I} {F : Set (Multiset I)}
    {α : ℝ} {h K : ℕ} (hα : 0 < α) (hH3 : CommonNbrCond H F α)
    (hH4 : HingeCond H F α h) (Bad : Finset V)
    (hcert : UniformCert (restrictedHost H Bad) F K)
    (R : Finset (Finset Ω)) (L : ℕ) (hL : PairCodegreeBound R L)
    (B : Finset (Sym2 V)) (d : ℕ) (hdeg : ∀ x, degIn B x ≤ d)
    (P : Finset (Sym2 V)) (hP : IsPhysical (vertexDeleted H Bad) F P)
    (Z : Finset V) (hZBad : Disjoint Z Bad) (hPZ : Inside Z P) (Ub : ℕ)
    (hUb : Z.card + 3*(K*P.card) + K*P.card*(2*h-2) +
      3*(K*P.card)*(2*h-3) ≤ Ub)
    (hwin1 : (Ub:ℝ) + Bad.card + 3 + 4*d ≤ α/2*Fintype.card V)
    (hwin2 : ((Ub:ℝ) + Bad.card + 1 + h + 5*d)*2^h.choose 2 ≤ α/2*Fintype.card V) :
    ∃ (A : Finset (Sym2 V)) (U : Finset V), IsAbsorber H F A P ∧ Disjoint A B ∧
      Z ⊆ U ∧ U.card ≤ Z.card + 3*(K*P.card) ∧ Inside U P ∧ Fresh U A ∧
      A.card ≤ K*P.card*(4*(2*h-2).choose 2+6) ∧ (U ∪ support A).card ≤ Ub ∧
      (supportIncrementCost ι R U (support A):ℝ) ≤
        ((K*P.card:ℕ):ℝ)*absorptionPotentialCost ι α h Ub L ∧
      Disjoint U Bad ∧ Disjoint (support A) Bad := by
  obtain ⟨S, c, hS, hPc, hK⟩ := surviving_uniformCert_coefficients H F Bad K hcert P hP
  have hVerts : ((S.filter (fun T => c T ≠ 0)).biUnion id).card ≤ 3*(K*P.card) := by
    refine card_biUnion_le.trans ?_
    calc ∑ T ∈ S.filter (fun T => c T ≠ 0), (id T).card =
          ∑ _T ∈ S.filter (fun T => c T ≠ 0), 3 :=
        sum_congr rfl (fun T hT => (hS T (mem_filter.mp hT).1).1.1)
      _ = 3*(S.filter (fun T => c T ≠ 0)).card := by
        rw [sum_const, smul_eq_mul, mul_comm]
      _ ≤ 3*∑ T ∈ S, (c T).natAbs := by
        apply Nat.mul_le_mul_left
        rw [card_eq_sum_ones, sum_filter]
        exact sum_le_sum (fun T _ => by
          split_ifs with hT
          · exact Int.natAbs_pos.mpr hT
          · exact Nat.zero_le _)
      _ ≤ 3*(K*P.card) := Nat.mul_le_mul_left 3 hK
  let U := Z ∪ (S.filter (fun T => c T ≠ 0)).biUnion id
  have hZU : Z ⊆ U := subset_union_left
  have hUc : U.card ≤ Z.card + 3*(K*P.card) :=
    (card_union_le _ _).trans (Nat.add_le_add_left hVerts Z.card)
  have hUBad : Disjoint U Bad := by
    apply disjoint_union_left.mpr
    refine ⟨hZBad, ?_⟩
    rw [disjoint_left]
    intro v hv hvBad
    obtain ⟨T, hT, hvT⟩ := mem_biUnion.mp hv
    exact disjoint_left.mp (hS T (mem_filter.mp hT).1).2 hvT hvBad
  have hUb' : U.card + (K*P.card)*(2*h-2) + 3*(K*P.card)*(2*h-3) ≤ Ub := by omega
  obtain ⟨A, hA, hAB, hFresh, hSupport, hCard, hPay, hAvoid⟩ :=
    slot_absorber_of_coeffs_avoiding_vertices_with_support_budget ι hα hH3 hH4
      R L hL Bad B d hdeg P S (fun T hT => (hS T hT).1) c
      (fun T hT _ => (hS T hT).2) hPc (K*P.card) hK Z hZBad hPZ Ub hUb' hwin1 hwin2
  exact ⟨A, U, hA, hAB, hZU, hUc, hPZ.mono hZU, hFresh, hCard,
    hSupport.trans hUb', hPay, hUBad, hAvoid⟩

#print axioms exists_low_cost_slot_gadget_avoiding_vertices
#print axioms exists_low_cost_composite_hinge_avoiding_vertices
#print axioms gadget_phase_avoiding_vertices_with_support_budget
#print axioms pairing_phase_avoiding_vertices_with_support_budget
#print axioms slot_absorber_avoiding_vertices_with_support_budget
#print axioms slot_absorber_of_coeffs_avoiding_vertices_with_support_budget
#print axioms surviving_certificate_weighted_absorber
end TypedTriangle.Pasch.Ambient
