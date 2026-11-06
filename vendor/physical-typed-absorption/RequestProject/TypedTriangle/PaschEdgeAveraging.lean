module
public import RequestProject.TypedTriangle.PaschUnrestrictedInfluence
set_option maxHeartbeats 4000000 -- build option (original: -DmaxHeartbeats=1600000; raised)
set_option maxRecDepth 16384 -- build option (original: -DmaxRecDepth=8192; raised)
@[expose] public section
open Finset Classical
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace TypedTriangle.Pasch
variable {V : Type*} [DecidableEq V]

/-- A pair has at most L completions in the old family. -/
def PairCodegreeBound (R : Finset (Finset V)) (L : ℕ) : Prop :=
  ∀ a b, a ≠ b → (R.filter (fun T => a ∈ T ∧ b ∈ T)).card ≤ L

private theorem not_mem_three {S : Finset (Finset V)} (hS : IsPasch S)
    {A B C : Finset V} (hA : A ∈ S) (hB : B ∈ S) (hC : C ∈ S)
    (hAB : A ≠ B) (hAC : A ≠ C) (hBC : B ≠ C) {v : V}
    (ha : v ∈ A) (hb : v ∈ B) : v ∉ C := by
  intro hc
  have hs : ({A,B,C} : Finset (Finset V)) ⊆ S.filter (fun T => v ∈ T) := by
    intro T hT
    rcases mem_insert.mp hT with rfl | hT
    · exact mem_filter.mpr ⟨hA,ha⟩
    rcases mem_insert.mp hT with rfl | hT
    · exact mem_filter.mpr ⟨hB,hb⟩
    have he := mem_singleton.mp hT
    subst T
    exact mem_filter.mpr ⟨hC,hc⟩
  have hn := card_le_card hs
  have ht : ({A,B,C} : Finset (Finset V)).card = 3 := by simp [hAB,hAC,hBC]
  have hd := hS.degree_zero_or_two v
  omega

private theorem triple_eq {A : Finset V} (hA : A.card = 3)
    {a b c : V} (ha : a ∈ A) (hb : b ∈ A) (hc : c ∈ A)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) : A = {a,b,c} := by
  have hs : ({a,b,c} : Finset V) ⊆ A := by
    intro v hv
    simp only [mem_insert,mem_singleton] at hv
    rcases hv with rfl | rfl | rfl <;> assumption
  have ht : ({a,b,c} : Finset V).card = 3 := by simp [hab,hac,hbc]
  exact (eq_of_subset_of_card_le hs (by omega)).symm

/-- A rooted Pasch has three old blocks in the explicit crossing form.
This statement also covers a new root which was not in the old family. -/
theorem rooted_completion_model {R S : Finset (Finset V)} {a b c : V}
    (hS : IsPasch S) (hQ : ({a,b,c} : Finset V) ∈ S)
    (hSub : S ⊆ insert {a,b,c} R) (hab : a ≠ b) :
    ∃ x y z, {a,x,y} ∈ R ∧ {b,x,z} ∈ R ∧ {c,y,z} ∈ R ∧
      a ≠ x ∧ a ≠ y ∧ x ≠ y ∧ b ≠ x ∧ b ≠ z ∧ x ≠ z ∧
      c ≠ y ∧ c ≠ z ∧ y ≠ z ∧
      TripleWitness S {a,b,c} a b (x,y,z) := by
  let Q : Finset V := {a,b,c}
  have haQ : a ∈ Q := by simp [Q]
  have hbQ : b ∈ Q := by simp [Q]
  have hcQ : c ∈ Q := by simp [Q]
  obtain ⟨x,A,B,hAS,hBS,hAQ,hBQ,hAB,haA,hbB,hxA,hxB,hxQ⟩ :=
    exists_rooted_witness hS hQ haQ hbQ hab
  have hQc : Q.card = 3 := hS.2.1 Q hQ
  have hac : a ≠ c := by
    intro he
    have hsmall : Q.card ≤ 2 := by simpa [Q,he] using (card_le_two (a := b) (b := c))
    omega
  have hbc : b ≠ c := by
    intro he
    have hsmall : Q.card ≤ 2 := by simpa [Q,he] using (card_le_two (a := a) (b := c))
    omega
  obtain ⟨C,⟨hCS,hCQ,hcC⟩,_⟩ := exists_unique_other hS hQ hcQ
  have hAC : A ≠ C := by
    intro he
    have hcA : c ∈ A := by simpa only [he] using hcC
    exact hAQ (eq_of_common_pair hS.2.2.2.2 hAS hQ hac haA hcA haQ hcQ)
  have hBC : B ≠ C := by
    intro he
    have hcB : c ∈ B := by simpa only [he] using hcC
    exact hBQ (eq_of_common_pair hS.2.2.2.2 hBS hQ hbc hbB hcB hbQ hcQ)
  obtain ⟨y,hy⟩ := inter_nonempty hS hAS hCS hAC
  obtain ⟨z,hz⟩ := inter_nonempty hS hBS hCS hBC
  have hyA := (mem_inter.mp hy).1
  have hyC := (mem_inter.mp hy).2
  have hzB := (mem_inter.mp hz).1
  have hzC := (mem_inter.mp hz).2
  have hyQ : y ∉ Q := not_mem_three hS hAS hCS hQ hAC hAQ hCQ hyA hyC
  have hzQ : z ∉ Q := not_mem_three hS hBS hCS hQ hBC hBQ hCQ hzB hzC
  have hax : a ≠ x := by intro he; exact hxQ (he ▸ haQ)
  have hay : a ≠ y := by intro he; exact hyQ (he ▸ haQ)
  have hxy : x ≠ y := by
    intro he
    exact not_mem_three hS hAS hBS hCS hAB hAC hBC hxA hxB (he.symm ▸ hyC)
  have hbx : b ≠ x := by intro he; exact hxQ (he ▸ hbQ)
  have hbz : b ≠ z := by intro he; exact hzQ (he ▸ hbQ)
  have hxz : x ≠ z := by
    intro he
    exact not_mem_three hS hAS hBS hCS hAB hAC hBC hxA hxB (he.symm ▸ hzC)
  have hcy : c ≠ y := by intro he; exact hyQ (he ▸ hcQ)
  have hcz : c ≠ z := by intro he; exact hzQ (he ▸ hcQ)
  have hyz : y ≠ z := by
    intro he
    exact not_mem_three hS hAS hCS hBS hAC hAB (Ne.symm hBC) hyA hyC (he.symm ▸ hzB)
  have heA := triple_eq (hS.2.1 A hAS) haA hxA hyA hax hay hxy
  have heB := triple_eq (hS.2.1 B hBS) hbB hxB hzB hbx hbz hxz
  have heC := triple_eq (hS.2.1 C hCS) hcC hyC hzC hcy hcz hyz
  have hAR : A ∈ R := (mem_insert.mp (hSub hAS)).resolve_left hAQ
  have hBR : B ∈ R := (mem_insert.mp (hSub hBS)).resolve_left hBQ
  have hCR : C ∈ R := (mem_insert.mp (hSub hCS)).resolve_left hCQ
  refine ⟨x,y,z,heA ▸ hAR,heB ▸ hBR,heC ▸ hCR,hax,hay,hxy,hbx,hbz,hxz,hcy,hcz,hyz,?_⟩
  exact ⟨A,B,hAS,hBS,hAQ,hBQ,hAB,heA,heB⟩

def pairThirds [Fintype V] (R : Finset (Finset V)) (a b : V) : Finset V :=
  univ.filter (fun c => {a,b,c} ∈ R ∧ c ≠ a ∧ c ≠ b ∧ a ≠ b)

theorem card_pairThirds_le [Fintype V] {R : Finset (Finset V)} {L : ℕ}
    (hL : PairCodegreeBound R L) (a b : V) : (pairThirds R a b).card ≤ L := by
  by_cases hab : a = b
  · simp [pairThirds,hab]
  have hinj : Set.InjOn (fun c : V => ({a,b,c} : Finset V)) (pairThirds R a b) := by
    intro c hc d hd he
    obtain ⟨_,_,hca,hcb,_⟩ := mem_filter.mp hc
    obtain ⟨_,_,hda,hdb,_⟩ := mem_filter.mp hd
    change ({a,b,c} : Finset V) = {a,b,d} at he
    have hm : c ∈ ({a,b,d} : Finset V) := by rw [←he]; simp
    simpa only [mem_insert,mem_singleton,hca,hcb,false_or] using hm
  calc
    (pairThirds R a b).card ≤ (R.filter (fun T => a ∈ T ∧ b ∈ T)).card := by
      apply card_le_card_of_injOn (fun c : V => ({a,b,c} : Finset V))
      · intro c hc
        exact mem_filter.mpr ⟨(mem_filter.mp hc).2.1,by simp⟩
      · exact hinj
    _ ≤ L := hL a b hab

/-- Averaging over the third vertex costs only L³ per ambient vertex.
The root is inserted into R, so no membership of the new triangle in R is assumed. -/
theorem sum_rooted_completions_le [Fintype V] (R : Finset (Finset V))
    (L : ℕ) (hL : PairCodegreeBound R L) (a b : V) (hab : a ≠ b) :
    (∑ c : V, rootedCount (insert {a,b,c} R) {a,b,c}) ≤ Fintype.card V * L^3 := by
  let roots (c : V) := (configurations (insert {a,b,c} R)).filter (fun S => {a,b,c} ∈ S)
  let domain := univ.sigma roots
  let choices := univ.sigma (fun x : V => (pairThirds R a x).sigma (fun y =>
    (pairThirds R b x).sigma (fun z => pairThirds R y z)))
  have hw (d : {d // d ∈ domain}) : ∃ x y z,
      y ∈ pairThirds R a x ∧ z ∈ pairThirds R b x ∧ d.val.1 ∈ pairThirds R y z ∧
      TripleWitness d.val.2 {a,b,d.val.1} a b (x,y,z) := by
    have hd := (mem_sigma.mp d.property).2
    obtain ⟨hCfg,hQ⟩ := mem_filter.mp hd
    obtain ⟨hSub,_,hS⟩ := mem_configurations.mp hCfg
    obtain ⟨x,y,z,hA,hB,hC,hax,hay,hxy,hbx,hbz,hxz,hcy,hcz,hyz,ht⟩ :=
      rooted_completion_model hS hQ hSub hab
    have hPerm : ({y,z,d.val.1} : Finset V) = {d.val.1,y,z} := by
      ext v
      simp only [mem_insert,mem_singleton]
      tauto
    exact ⟨x,y,z,by simp [pairThirds,hA,Ne.symm hay,Ne.symm hxy,hax],
      by simp [pairThirds,hB,Ne.symm hbz,Ne.symm hxz,hbx],
      mem_filter.mpr ⟨mem_univ _,by simpa only [hPerm] using hC,hcy,hcz,hyz⟩,ht⟩
  choose x y z hf using hw
  let f (d : {d // d ∈ domain}) : {s // s ∈ choices} :=
    ⟨⟨x d,⟨y d,⟨z d,d.val.1⟩⟩⟩,
      mem_sigma.mpr ⟨mem_univ _,mem_sigma.mpr ⟨(hf d).1,
        mem_sigma.mpr ⟨(hf d).2.1,(hf d).2.2.1⟩⟩⟩⟩
  have hinj : Function.Injective f := by
    intro d e he
    have hx : x d = x e := congrArg (fun s => s.val.1) he
    have hy : y d = y e := congrArg (fun s => s.val.2.1) he
    have hz : z d = z e := congrArg (fun s => s.val.2.2.1) he
    have hc : d.val.1 = e.val.1 := congrArg (fun s => s.val.2.2.2) he
    have hd := mem_filter.mp (mem_sigma.mp d.property).2
    have he' := mem_filter.mp (mem_sigma.mp e.property).2
    have ht : TripleWitness e.val.2 {a,b,d.val.1} a b (x d,y d,z d) := by
      simpa only [hc,hx,hy,hz] using (hf e).2.2.2
    have hroot : ({a,b,d.val.1} : Finset V) ∈ e.val.2 := by simpa only [hc] using he'.2
    have hs : d.val.2 = e.val.2 := eq_of_triple_witness (mem_configurations.mp hd.1).2.2
      (mem_configurations.mp he'.1).2.2 hd.2 hroot (hf d).2.2.2 ht
    apply Subtype.ext
    exact Sigma.ext hc (heq_of_eq hs)
  have hcard : domain.card ≤ choices.card := by
    simpa only [Fintype.card_coe] using Fintype.card_le_of_injective f hinj
  have hchoices : choices.card ≤ Fintype.card V * L^3 := by
    simp only [choices,card_sigma]
    calc (∑ x : V, ∑ y ∈ pairThirds R a x, ∑ z ∈ pairThirds R b x, (pairThirds R y z).card)
        ≤ ∑ _x : V, L*(L*L) := by
          apply sum_le_sum
          intro x _
          calc (∑ y ∈ pairThirds R a x, ∑ z ∈ pairThirds R b x, (pairThirds R y z).card)
              ≤ ∑ _y ∈ pairThirds R a x, ∑ _z ∈ pairThirds R b x, L := by
                apply sum_le_sum; intro y _
                apply sum_le_sum; intro z _
                exact card_pairThirds_le hL y z
            _ = (pairThirds R a x).card*((pairThirds R b x).card*L) := by
              simp [sum_const,nsmul_eq_mul]
            _ ≤ L*(L*L) := Nat.mul_le_mul (card_pairThirds_le hL a x)
              (Nat.mul_le_mul_right L (card_pairThirds_le hL b x))
      _ = Fintype.card V * L^3 := by simp [pow_succ,Nat.mul_assoc]
  have hdom : domain.card = ∑ c : V, rootedCount (insert {a,b,c} R) {a,b,c} := by
    simp only [domain,card_sigma,roots,rootedCount]
  rw [←hdom]
  exact hcard.trans hchoices

#print axioms rooted_completion_model
#print axioms card_pairThirds_le
#print axioms sum_rooted_completions_le
end TypedTriangle.Pasch
