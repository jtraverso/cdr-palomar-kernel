module
public import RequestProject.TypedTriangle.PaschSupportLedger
public import RequestProject.TypedTriangle.PaschWeightedSupportApex
set_option maxHeartbeats 4000000 -- build option (original: -DmaxHeartbeats=1600000; raised)
set_option maxRecDepth 16384 -- build option (original: -DmaxRecDepth=8192; raised)
@[expose] public section
open Finset Classical
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1200000
namespace TypedTriangle.Pasch
variable {V I : Type*} [Fintype V]

theorem supportIncrementCost_apex_le_pair_sum (R : Finset (Finset V)) (S : Finset V) (t : V) :
    supportIncrementCost R S {t} ≤ ∑ p : S × S,
      rootedCount (insert {p.1.val,p.2.val,t} R) {p.1.val,p.2.val,t} := by
  let N := ((S ∪ {t}).powersetCard 3).filter (fun Q => ¬ Q ⊆ S)
  let tri (p : S × S) : Finset V := {p.1.val,p.2.val,t}
  have hSub : N ⊆ univ.image tri := by
    intro Q hQ
    obtain ⟨hQ,hNew⟩ := mem_filter.mp hQ
    obtain ⟨hSupp,hCard⟩ := mem_powersetCard.mp hQ
    have ht : t ∈ Q := by
      by_contra hnot
      apply hNew
      intro x hx
      rcases mem_union.mp (hSupp hx) with hxs | hxt
      · exact hxs
      · exact (hnot ((mem_singleton.mp hxt) ▸ hx)).elim
    have he : (Q.erase t).card = 2 := by rw [card_erase_of_mem ht,hCard]
    obtain ⟨a,b,hab,heq⟩ := card_eq_two.mp he
    have ha : a ∈ Q.erase t := by rw [heq]; simp
    have hb : b ∈ Q.erase t := by rw [heq]; simp
    have haS : a ∈ S := by
      rcases mem_union.mp (hSupp (mem_of_mem_erase ha)) with hs | hs
      · exact hs
      · exact ((mem_erase.mp ha).1 (mem_singleton.mp hs)).elim
    have hbS : b ∈ S := by
      rcases mem_union.mp (hSupp (mem_of_mem_erase hb)) with hs | hs
      · exact hs
      · exact ((mem_erase.mp hb).1 (mem_singleton.mp hs)).elim
    have hEq : Q = {a,b,t} := by
      have hRepr : Q = insert t {a,b} := by rw [←heq,insert_erase ht]
      rw [hRepr]
      ext x
      simp only [mem_insert,mem_singleton]
      tauto
    exact mem_image.mpr ⟨(⟨a,haS⟩,⟨b,hbS⟩),mem_univ _,hEq.symm⟩
  exact (sum_le_sum_of_subset hSub).trans (sum_image_le_of_nonneg (fun _ _ => Nat.zero_le _))

def compositePotentialCost (α : ℝ) (h Ub L : ℕ) : ℝ :=
  (Ub:ℝ)^2*(L:ℝ)^3/(α/2) + hingePotentialCost α h (Ub+1) L +
    hingePotentialCost α h (Ub+1+h) L

/-- A robust composite hinge, selected with the concrete support potential.
The local bounded support S is separate from the global forbidden history U. -/
theorem exists_low_cost_robust_composite_hinge {H : Host V I} {F : Set (Multiset I)}
    {α : ℝ} {h : ℕ} (hα : 0 < α) (hH3 : CommonNbrCond H F α) (hH4 : HingeCond H F α h)
    {u v a b : V} (hab : a ≠ b) (hTa : IsAllowed H F {u,v,a}) (hTb : IsAllowed H F {u,v,b})
    (R : Finset (Finset V)) (L : ℕ) (hL : PairCodegreeBound R L)
    (S : Finset V) (Ub : ℕ) (hS : S.card ≤ Ub) (hRoots : ({u,v,a,b}:Finset V) ⊆ S)
    (U : Finset V) (B : Finset (Sym2 V)) (d : ℕ) (hdeg : ∀ x, degIn B x ≤ d)
    (hwin1 : (U.card:ℝ)+2+4*d ≤ α/2*Fintype.card V)
    (hwin2 : ((U.card:ℝ)+h+5*d)*2^Nat.choose h 2 ≤ α/2*Fintype.card V) :
    ∃ J, IsHinge H F u v a b J ∧ Disjoint J B ∧ s(a,b) ∉ J ∧
      (∀ z ∈ U, z ∈ support J → z ∈ ({u,v,a,b}:Finset V)) ∧
      (support J).card ≤ 2*h-3 ∧
      (supportIncrementCost R S (support J):ℝ) ≤ compositePotentialCost α h Ub L := by
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
  obtain ⟨t,htX,hTt,htBu,htBv,hPair⟩ := exists_low_total_cost_fresh_apex
    hα hH3 hTa R L hL p q B d hdeg X hMargin
  have hApex0 : (supportIncrementCost R S {t}:ℝ) ≤ (S.card:ℝ)^2*(L:ℝ)^3/(α/2) := by
    have hNatural := supportIncrementCost_apex_le_pair_sum R S t
    have hReal : (supportIncrementCost R S {t}:ℝ) ≤
        ∑ x : S × S, (rootedCount (insert {x.1.val,x.2.val,t} R) {x.1.val,x.2.val,t}:ℝ) := by
      exact_mod_cast hNatural
    exact hReal.trans (by simpa only [p,q,Fintype.card_prod,Fintype.card_coe,Nat.cast_mul,pow_two] using hPair)
  have hApex : (supportIncrementCost R S {t}:ℝ) ≤ (Ub:ℝ)^2*(L:ℝ)^3/(α/2) := by
    have hsPow : (S.card:ℝ)^2 ≤ (Ub:ℝ)^2 := by exact_mod_cast Nat.pow_le_pow_left hS 2
    exact hApex0.trans (div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_right hsPow (by positivity)) (by positivity))
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
    exists_low_cost_robust_hinge hα hH4 hat hTa hTt R L hL S1 (Ub+1) hS1 hRoots1
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
    exists_low_cost_robust_hinge hα hH4 hbt.symm hTt hTb R L hL S2 (Ub+1+h) hS2 hRoots2
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
    have hMono : supportIncrementCost R S (support H₁ ∪ support H₂) ≤
        supportIncrementCost R S ({t} ∪ (support H₁ ∪ support H₂)) :=
      supportIncrementCost_mono R S subset_union_right
    have hBase : S ∪ {t} = S1 := by ext x; simp [S1,or_comm]
    have hLedger : supportIncrementCost R S ({t} ∪ (support H₁ ∪ support H₂)) =
        supportIncrementCost R S {t}+supportIncrementCost R S1 (support H₁)+
          supportIncrementCost R S2 (support H₂) := by
      rw [supportIncrementCost_union,supportIncrementCost_union,hBase]
      simp only [S2,Nat.add_assoc]
    have hReal : (supportIncrementCost R S (support H₁ ∪ support H₂):ℝ) ≤
        (supportIncrementCost R S {t}:ℝ)+(supportIncrementCost R S1 (support H₁):ℝ)+
          (supportIncrementCost R S2 (support H₂):ℝ) := by
      exact_mod_cast hMono.trans_eq hLedger
    exact hReal.trans (add_le_add (add_le_add hApex hPay₁) hPay₂)

#print axioms supportIncrementCost_apex_le_pair_sum
#print axioms exists_low_cost_robust_composite_hinge
end TypedTriangle.Pasch
