module
public import RequestProject.TypedTriangle.RobustHinge
public import Mathlib.Data.Fintype.EquivFin
set_option maxHeartbeats 4000000 -- build option (original: -DmaxHeartbeats=1600000; raised)
set_option maxRecDepth 16384 -- build option (original: -DmaxRecDepth=8192; raised)
@[expose] public section
open Finset Classical
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 800000
namespace TypedTriangle.Pasch
variable {V I : Type*} [Fintype V]

private theorem enumerate_support (S : Finset V) (f : ℕ) (hS : S.card = f) :
    ∃ e : Fin f → V, Function.Injective e ∧ univ.image e = S := by
  let t : S ≃ Fin f := S.equivFinOfCardEq hS
  let e : Fin f → V := fun j => (t.symm j).val
  refine ⟨e,?_,?_⟩
  · intro j k hjk
    exact t.symm.injective (Subtype.ext hjk)
  · ext v
    constructor
    · intro hv
      obtain ⟨j,_,rfl⟩ := mem_image.mp hv
      exact (t.symm j).property
    · intro hv
      refine mem_image.mpr ⟨t ⟨v,hv⟩,mem_univ _,?_⟩
      exact congrArg Subtype.val (t.symm_apply_apply ⟨v,hv⟩)

/-- Encode an actual edge-set family by enumerations of its free support.
The only loss is the proved number of edge sets on a fixed support. -/
theorem edge_family_has_assignment_family (K : Finset (Finset (Sym2 V)))
    (roots : Finset V) (i : ℕ)
    (hDiag : ∀ J ∈ K, ∀ e ∈ J, ¬ e.IsDiag)
    (hRoot : ∀ J ∈ K, roots ⊆ support J) (hOrder : ∀ J ∈ K, (support J).card = i) :
    ∃ P : Finset (Fin (i-roots.card) → V),
      K.card ≤ P.card * 2^Nat.choose i 2 ∧
      ∀ f ∈ P, Function.Injective f ∧ ∃ J ∈ K, univ.image f = support J\roots := by
  have hFree (J : {J // J ∈ K}) : (support J.val\roots).card = i-roots.card := by
    rw [card_sdiff_of_subset (hRoot J.val J.property),hOrder J.val J.property]
  choose e he using fun J : {J // J ∈ K} =>
    enumerate_support (support J.val\roots) (i-roots.card) (hFree J)
  let P : Finset (Fin (i-roots.card) → V) := univ.image e
  have hFull (J : {J // J ∈ K}) : support J.val = roots ∪ univ.image (e J) := by
    rw [(he J).2,union_comm,sdiff_union_of_subset (hRoot J.val J.property)]
  have hFiber (f : Fin (i-roots.card) → V) (hf : f ∈ P) :
      (univ.filter (fun J : {J // J ∈ K} => e J = f)).card ≤ 2^Nat.choose i 2 := by
    obtain ⟨J0,_,hJ0⟩ := mem_image.mp hf
    have hSub : (univ.filter (fun J : {J // J ∈ K} => e J = f)).card ≤
        (K.filter (fun J => support J = support J0.val)).card := by
      apply card_le_card_of_injOn (fun J : {J // J ∈ K} => J.val)
      · intro J hJ
        refine mem_filter.mpr ⟨J.property,?_⟩
        rw [hFull J,hFull J0,(mem_filter.mp hJ).2,hJ0]
      · intro J _ J' _ hh
        exact Subtype.ext hh
    have hCap := rooted_family_card_le (K.filter (fun J => support J = support J0.val))
      (support J0.val) i (by simpa only [hOrder J0.val J0.property] using (Nat.le_refl i))
      (fun J hJ => hDiag J (mem_filter.mp hJ).1)
      (fun J hJ => by simpa only [(mem_filter.mp hJ).2] using (subset_refl (support J0.val)))
      (fun J hJ => hOrder J (mem_filter.mp hJ).1)
    have hc : (support J0.val).card = i := hOrder J0.val J0.property
    exact hSub.trans (by simpa only [hc,Nat.sub_self,Nat.choose_zero_right,one_mul] using hCap)
  refine ⟨P,?_,?_⟩
  · have hmaps : Set.MapsTo e (univ : Finset {J // J ∈ K}) P := by
      intro J _
      exact mem_image_of_mem e (mem_univ J)
    have hs := card_eq_sum_card_fiberwise hmaps
    have hsum : K.card = ∑ f ∈ P, (univ.filter (fun J : {J // J ∈ K} => e J = f)).card := by
      simpa only [card_univ,Fintype.card_coe] using hs
    rw [hsum]
    calc (∑ f ∈ P, (univ.filter (fun J : {J // J ∈ K} => e J = f)).card)
        ≤ ∑ _f ∈ P, 2^Nat.choose i 2 := sum_le_sum (fun f hf => hFiber f hf)
      _ = P.card * 2^Nat.choose i 2 := by simp
  · intro f hf
    obtain ⟨J,_,rfl⟩ := mem_image.mp hf
    exact ⟨(he J).1,J.val,J.property,(he J).2⟩

/-- H4 supplies a genuine positive-density family of injective assignments
for the same fresh hinges. No family or spread provider is assumed. -/
theorem exists_robust_hinge_assignment_family {H : Host V I} {F : Set (Multiset I)}
    {α : ℝ} {h : ℕ} (hα : 0 < α) (hH4 : HingeCond H F α h)
    {u v a b : V} (hab : a ≠ b)
    (hTa : IsAllowed H F {u,v,a}) (hTb : IsAllowed H F {u,v,b}) (Z : Finset V)
    (B : Finset (Sym2 V)) (d : ℕ) (hdeg : ∀ v, degIn B v ≤ d) (hB : s(a,b) ∉ B)
    (hZ : ((Z.card:ℝ)+5*d)*2^Nat.choose h 2 ≤ α/2*Fintype.card V) :
    ∃ i : ℕ, 6 ≤ i ∧ i ≤ h ∧ ∃ P : Finset (Fin (i-4) → V),
      α/(2*2^Nat.choose i 2)*(Fintype.card V:ℝ)^(i-4) ≤ P.card ∧
      ∀ f ∈ P, Function.Injective f ∧ Disjoint (univ.image f) Z ∧
        ∃ J ∈ hinges H F u v a b i,
          (∀ z ∈ Z, z ∈ support J → z ∈ ({u,v,a,b}:Finset V)) ∧ Disjoint J B ∧
          support J = ({u,v,a,b}:Finset V) ∪ univ.image f := by
  obtain ⟨i,hi6,hih,hSupply⟩ := hH4 u v a b hab hTa hTb
  obtain ⟨huv,hua,hva⟩ := distinct_of_card_three hTa.1
  obtain ⟨_,hub,hvb⟩ := distinct_of_card_three hTb.1
  have hRoots : ({u,v,a,b}:Finset V).card = 4 := roots_card huv hua hva hub hvb hab
  have hPow : (Fintype.card V:ℝ)^(i-4) = Fintype.card V*(Fintype.card V:ℝ)^(i-5) := by
    rw [←pow_succ']; congr 1; omega
  have hChoose : (2:ℝ)^Nat.choose i 2 ≤ 2^Nat.choose h 2 :=
    pow_le_pow_right₀ (by norm_num) (Nat.choose_le_choose 2 (by omega))
  have hZ' : ((Z.card:ℝ)+5*d)*(Fintype.card V:ℝ)^(i-5)*2^Nat.choose i 2 ≤
      α/2*(Fintype.card V:ℝ)^(i-4) := by
    rw [hPow]
    calc ((Z.card:ℝ)+5*d)*(Fintype.card V:ℝ)^(i-5)*2^Nat.choose i 2
        ≤ ((Z.card:ℝ)+5*d)*(Fintype.card V:ℝ)^(i-5)*2^Nat.choose h 2 :=
          mul_le_mul_of_nonneg_left hChoose (by positivity)
      _ = (((Z.card:ℝ)+5*d)*2^Nat.choose h 2)*(Fintype.card V:ℝ)^(i-5) := by ring
      _ ≤ (α/2*Fintype.card V)*(Fintype.card V:ℝ)^(i-5) :=
        mul_le_mul_of_nonneg_right hZ (by positivity)
      _ = _ := by ring
  let K := (hinges H F u v a b i).filter
    (fun J => (∀ z ∈ Z, z ∈ support J → z ∈ ({u,v,a,b}:Finset V)) ∧ Disjoint J B)
  have hK : α/2*(Fintype.card V:ℝ)^(i-4) ≤ K.card :=
    robust_fresh_hinges hab hTa hTb i hi6 α Z B d hdeg hB hSupply hZ'
  have hRoot (J : Finset (Sym2 V)) (hJ : J ∈ K) : ({u,v,a,b}:Finset V) ⊆ support J := by
    have hh := (mem_filter.mp hJ).1
    have ht : IsHinge H F u v a b J ∧ (support J).card = i := by
      simpa only [hinges,mem_filter,mem_univ,true_and] using hh
    exact (hinge_order_ge_six hab hTa hTb ht.1).1
  have hOrder (J : Finset (Sym2 V)) (hJ : J ∈ K) : (support J).card = i := by
    have hh := (mem_filter.mp hJ).1
    have ht : IsHinge H F u v a b J ∧ (support J).card = i := by
      simpa only [hinges,mem_filter,mem_univ,true_and] using hh
    exact ht.2
  have hDiag (J : Finset (Sym2 V)) (hJ : J ∈ K) : ∀ e ∈ J, ¬ e.IsDiag := by
    have hh := (mem_filter.mp hJ).1
    have ht : IsHinge H F u v a b J ∧ (support J).card = i := by
      simpa only [hinges,mem_filter,mem_univ,true_and] using hh
    exact ht.1.not_isDiag
  let roots : Finset V := {u,v,a,b}
  have hRootCount : roots.card = 4 := hRoots
  let Family (f : ℕ) : Prop := ∃ P : Finset (Fin f → V),
    K.card ≤ P.card * 2^Nat.choose i 2 ∧
    ∀ f ∈ P, Function.Injective f ∧ ∃ J ∈ K, univ.image f = support J\roots
  have hFamily0 : Family (i-roots.card) :=
    edge_family_has_assignment_family K roots i hDiag hRoot hOrder
  have hIndex : i-roots.card = i-4 := congrArg (fun r : ℕ => i-r) hRootCount
  have hFamily : Family (i-4) := hIndex ▸ hFamily0
  obtain ⟨P,hCard,hWitness⟩ := hFamily
  have hCardReal : (K.card:ℝ) ≤ (P.card:ℝ)*(2:ℝ)^Nat.choose i 2 := by exact_mod_cast hCard
  have hCapPos : (0:ℝ) < (2:ℝ)^Nat.choose i 2 := by positivity
  refine ⟨i,hi6,hih,P,?_,?_⟩
  · calc α/(2*2^Nat.choose i 2)*(Fintype.card V:ℝ)^(i-4)
        = (α/2*(Fintype.card V:ℝ)^(i-4))/2^Nat.choose i 2 := by
          field_simp [ne_of_gt hCapPos] <;> ring
      _ ≤ P.card := (div_le_iff₀ hCapPos).mpr (hK.trans hCardReal)
  · intro f hf
    obtain ⟨hinj,J,hJK,hImage⟩ := hWitness f hf
    have hFresh := (mem_filter.mp hJK).2.1
    have hFull : support J = ({u,v,a,b}:Finset V) ∪ univ.image f := by
      rw [hImage,union_comm,sdiff_union_of_subset (hRoot J hJK)]
    refine ⟨hinj,?_,J,(mem_filter.mp hJK).1,hFresh,(mem_filter.mp hJK).2.2,hFull⟩
    apply disjoint_left.mpr
    intro z hz hzZ
    rw [hImage] at hz
    obtain ⟨hzSupp,hzNot⟩ := mem_sdiff.mp hz
    exact hzNot (hFresh z hzZ hzSupp)

#print axioms edge_family_has_assignment_family
#print axioms exists_robust_hinge_assignment_family
end TypedTriangle.Pasch
