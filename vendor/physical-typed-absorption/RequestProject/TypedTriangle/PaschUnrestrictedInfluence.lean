module
public import RequestProject.TypedTriangle.PaschRootedInfluence
set_option maxHeartbeats 4000000 -- build option (original: -DmaxHeartbeats=1600000; raised)
set_option maxRecDepth 16384 -- build option (original: -DmaxRecDepth=8192; raised)
@[expose] public section
open Finset Classical
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace TypedTriangle.Pasch
variable {V : Type*} [DecidableEq V]

private theorem triple_of_pair {A : Finset V} (hA : A.card = 3)
    {a x : V} (ha : a ∈ A) (hx : x ∈ A) (hax : a ≠ x) :
    ∃ y, A = {a,x,y} := by
  have hp : ({a,x}:Finset V).card = 2 := by simp [hax]
  obtain ⟨y,hy,hyn⟩ := exists_mem_notMem_of_card_lt_card
    (show ({a,x}:Finset V).card < A.card by omega)
  have hn : y ≠ a ∧ y ≠ x := by simpa only [mem_insert,mem_singleton,not_or] using hyn
  have hsub : ({a,x,y}:Finset V) ⊆ A := by
    intro v hv
    simp only [mem_insert,mem_singleton] at hv
    rcases hv with rfl | rfl | rfl <;> assumption
  have hc : ({a,x,y}:Finset V).card = 3 := by
    simp [hax,hn.1,hn.2,Ne.symm hn.1,Ne.symm hn.2]
  exact ⟨y,(eq_of_subset_of_card_le hsub (by omega)).symm⟩

def TripleWitness (S : Finset (Finset V)) (Q : Finset V) (a b : V)
    (t : V × V × V) : Prop :=
  ∃ A B, A ∈ S ∧ B ∈ S ∧ A ≠ Q ∧ B ≠ Q ∧ A ≠ B ∧
    A = {a,t.1,t.2.1} ∧ B = {b,t.1,t.2.2}

theorem exists_triple_witness {S : Finset (Finset V)} (hS : IsPasch S)
    {Q : Finset V} (hQ : Q ∈ S) {a b : V} (ha : a ∈ Q) (hb : b ∈ Q) (hab : a ≠ b) :
    ∃ t, TripleWitness S Q a b t := by
  obtain ⟨x,A,B,hAS,hBS,hAQ,hBQ,hAB,haA,hbB,hxA,hxB,hxQ⟩ :=
    exists_rooted_witness hS hQ ha hb hab
  have hax : a ≠ x := by intro he; exact hxQ (he ▸ ha)
  have hbx : b ≠ x := by intro he; exact hxQ (he ▸ hb)
  obtain ⟨y,hy⟩ := triple_of_pair (hS.2.1 A hAS) haA hxA hax
  obtain ⟨z,hz⟩ := triple_of_pair (hS.2.1 B hBS) hbB hxB hbx
  exact ⟨(x,y,z),A,B,hAS,hBS,hAQ,hBQ,hAB,hy,hz⟩

theorem eq_of_triple_witness {S T : Finset (Finset V)}
    (hS : IsPasch S) (hT : IsPasch T) {Q : Finset V} (hQS : Q ∈ S) (hQT : Q ∈ T)
    {a b : V} {t : V × V × V} (hwS : TripleWitness S Q a b t)
    (hwT : TripleWitness T Q a b t) : S = T := by
  obtain ⟨A,B,hAS,hBS,hAQ,hBQ,hAB,hA,hB⟩ := hwS
  obtain ⟨A',B',hAT,hBT,hA'Q,hB'Q,hA'B',hA',hB'⟩ := hwT
  have haa : A = A' := hA.trans hA'.symm
  have hbb : B = B' := hB.trans hB'.symm
  have hAT' : A ∈ T := by rw [haa]; exact hAT
  have hBT' : B ∈ T := by rw [hbb]; exact hBT
  have hcard : ({Q,A,B}:Finset (Finset V)).card = 3 := by
    simp [hAQ,hBQ,hAB,Ne.symm hAQ,Ne.symm hBQ]
  apply hS.eq_of_common_triple hT hcard
  · intro U hU
    simp only [mem_insert,mem_singleton] at hU
    rcases hU with rfl | rfl | rfl <;> assumption
  · intro U hU
    simp only [mem_insert,mem_singleton] at hU
    rcases hU with rfl | rfl | rfl <;> assumption

/-- The full allowed universe needs no packing premise: three external
vertices determine each Pasch configuration containing a fixed triple. -/
theorem rootedCount_le_cube [Fintype V] (D : Finset (Finset V))
    (Q : Finset V) (hQ : Q.card = 3) : rootedCount D Q ≤ (Fintype.card V)^3 := by
  obtain ⟨a,ha⟩ := card_pos.mp (show 0 < Q.card by omega)
  obtain ⟨b,hb,hba⟩ := exists_mem_ne (show 1 < Q.card by omega) a
  let R := (configurations D).filter (fun S => Q ∈ S)
  have hw (S : {S // S ∈ R}) : ∃ t : V × V × V, TripleWitness S.val Q a b t := by
    have hm := mem_filter.mp S.property
    exact exists_triple_witness (mem_configurations.mp hm.1).2.2 hm.2 ha hb (Ne.symm hba)
  choose f hf using hw
  have hinj : Function.Injective f := by
    intro S T he
    apply Subtype.ext
    have hs := mem_filter.mp S.property
    have ht := mem_filter.mp T.property
    have hwT : TripleWitness T.val Q a b (f S) := he.symm ▸ hf T
    exact eq_of_triple_witness (mem_configurations.mp hs.1).2.2
      (mem_configurations.mp ht.1).2.2 hs.2 ht.2 (hf S) hwT
  have hc := Fintype.card_le_of_injective f hinj
  change R.card ≤ _
  simpa only [Fintype.card_coe,Fintype.card_prod,pow_succ,pow_zero,Nat.mul_one,Nat.one_mul,Nat.mul_assoc] using hc

#print axioms exists_triple_witness
#print axioms eq_of_triple_witness
#print axioms rootedCount_le_cube
end TypedTriangle.Pasch
