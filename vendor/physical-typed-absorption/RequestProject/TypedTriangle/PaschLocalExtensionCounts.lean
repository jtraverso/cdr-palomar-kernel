module
public import RequestProject.TypedTriangle.PaschPairExtensionBounds
public import RequestProject.TypedTriangle.PaschUnrestrictedInfluence
set_option maxHeartbeats 4000000 -- build option (original: -DmaxHeartbeats=1600000; raised)
set_option maxRecDepth 16384 -- build option (original: -DmaxRecDepth=8192; raised)
@[expose] public section
open Finset Classical
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1200000
namespace TypedTriangle.Pasch
variable {V : Type*} [DecidableEq V]

private theorem local_third_vertex {T : Finset V} (hT : T.card = 3)
    {a x : V} (ha : a ∈ T) (hx : x ∈ T) (hax : a ≠ x) :
    ∃ z, T = {a,x,z} := by
  have hp : ({a,x} : Finset V).card = 2 := by simp [hax]
  obtain ⟨z,hz,hzn⟩ := exists_mem_notMem_of_card_lt_card
    (show ({a,x} : Finset V).card < T.card by omega)
  have hn : z ≠ a ∧ z ≠ x := by simpa only [mem_insert,mem_singleton,not_or] using hzn
  have hSub : ({a,x,z} : Finset V) ⊆ T := by
    intro y hy
    simp only [mem_insert,mem_singleton] at hy
    rcases hy with rfl | rfl | rfl <;> assumption
  have hc : ({a,x,z} : Finset V).card = 3 := by
    simp [hax,hn.1,hn.2,Ne.symm hn.1,Ne.symm hn.2]
  exact ⟨z,(eq_of_subset_of_card_le hSub (by omega)).symm⟩

def localPairExtensions (D : Finset (Finset V)) (X Q B : Finset V) :=
  (pairExtensions D Q B).filter (fun S => ∀ T ∈ S, T ≠ Q → T ≠ B → T ⊆ X)

/-- The two unfixed blocks are in the child. The free vertex in the
two-block extension witness therefore ranges over the child alone. -/
theorem localPairExtensions_card_le (D : Finset (Finset V)) (X Q B : Finset V)
    (hQB : Q ≠ B) : (localPairExtensions D X Q B).card ≤ 2*X.card := by
  let E := localPairExtensions D X Q B
  by_cases hEmpty : E = ∅
  · change E.card ≤ _
    simp only [hEmpty, card_empty, Nat.zero_le]
  obtain ⟨S0,hS0⟩ := nonempty_iff_ne_empty.mpr hEmpty
  obtain ⟨hPair0,_⟩ := mem_filter.mp hS0
  obtain ⟨hConf0,hQ0,hB0⟩ := mem_filter.mp hPair0
  have hPasch0 := (mem_configurations.mp hConf0).2.2
  have hInter := inter_card_eq_one hPasch0 hQ0 hB0 hQB
  obtain ⟨v,hv⟩ := card_pos.mp (by omega : 0 < (Q ∩ B).card)
  have hvQ := (mem_inter.mp hv).1
  have hvB := (mem_inter.mp hv).2
  obtain ⟨a,haQ,haNot⟩ := Finset.not_subset.mp (show ¬ Q ⊆ {v} by
    intro hSub
    have hh := card_le_card hSub
    have hc := hPasch0.2.1 Q hQ0
    simp only [card_singleton] at hh
    omega)
  have hva : v ≠ a := by intro h; exact haNot (by simp [h])
  have hWitness : ∀ S ∈ E, ∃ p : ↥(B \ Q) × X, ∃ T,
      T ∈ S ∧ T ≠ Q ∧ T ≠ B ∧ T = {a,p.1.val,p.2.val} := by
    intro S hS
    obtain ⟨hPair,hLocal⟩ := mem_filter.mp hS
    obtain ⟨hConf,hQ,hB⟩ := mem_filter.mp hPair
    have hPasch := (mem_configurations.mp hConf).2.2
    obtain ⟨x,A,T,hAS,hTS,hAQ,hTQ,hAT,hvA,haT,hxA,hxT,hxQ⟩ :=
      exists_rooted_witness hPasch hQ hvQ haQ hva
    have hUnique := exists_unique_other hPasch hQ hvQ
    have hAB : A = B := hUnique.unique ⟨hAS,hAQ,hvA⟩ ⟨hB,Ne.symm hQB,hvB⟩
    subst A
    have hax : a ≠ x := by intro he; exact hxQ (he ▸ haQ)
    obtain ⟨z,hT⟩ := local_third_vertex (hPasch.2.1 T hTS) haT hxT hax
    have hzX : z ∈ X := (hLocal T hTS hTQ (Ne.symm hAT)) (by rw [hT]; simp)
    exact ⟨(⟨x,mem_sdiff.mpr ⟨hxA,hxQ⟩⟩,⟨z,hzX⟩),T,hTS,hTQ,Ne.symm hAT,hT⟩
  let f : ↥E → ↥(B \ Q) × X := fun S => Classical.choose (hWitness S.val S.property)
  have hf : Function.Injective f := by
    intro S T hEq
    obtain ⟨A,hAS,hAQ,hAB,hA⟩ := Classical.choose_spec (hWitness S.val S.property)
    obtain ⟨A',hAT,hA'Q,hA'B,hA'⟩ := Classical.choose_spec (hWitness T.val T.property)
    have hAA : A = A' := by
      change A = {a,(f S).1.val,(f S).2.val} at hA
      change A' = {a,(f T).1.val,(f T).2.val} at hA'
      rw [hA,hA',hEq]
    have hATcommon : A ∈ T.val := by rw [hAA]; exact hAT
    obtain ⟨hPairS,_⟩ := mem_filter.mp S.property
    obtain ⟨hPairT,_⟩ := mem_filter.mp T.property
    obtain ⟨hConfS,hQS,hBS⟩ := mem_filter.mp hPairS
    obtain ⟨hConfT,hQT,hBT⟩ := mem_filter.mp hPairT
    have hPaschS := (mem_configurations.mp hConfS).2.2
    have hPaschT := (mem_configurations.mp hConfT).2.2
    have hCard : ({Q,B,A} : Finset (Finset V)).card = 3 := by
      simp [hQB,hAQ,hAB,Ne.symm hAQ,Ne.symm hAB]
    apply Subtype.ext
    apply hPaschS.eq_of_common_triple hPaschT hCard
    · intro U hU
      simp only [mem_insert,mem_singleton] at hU
      rcases hU with rfl | rfl | rfl <;> assumption
    · intro U hU
      simp only [mem_insert,mem_singleton] at hU
      rcases hU with rfl | rfl | rfl <;> assumption
  have hCard := Fintype.card_le_of_injective f hf
  have hDiff : (B \ Q).card = 2 := by
    rw [card_sdiff,hInter,hPasch0.2.1 B hB0]
  change E.card ≤ _
  simpa only [Fintype.card_coe,Fintype.card_prod,hDiff] using hCard

def localRootedConfigurations (D : Finset (Finset V)) (X Q : Finset V) :=
  (configurations D).filter (fun S => Q ∈ S ∧ ∀ T ∈ S, T ≠ Q → T ⊆ X)

/-- Three blocks in the child give a child-cubed rooted extension bound,
even when the fixed old block is expressed in the ambient carrier. -/
theorem localRootedConfigurations_card_le_cube (D : Finset (Finset V)) (X Q : Finset V)
    (hQ : Q.card = 3) : (localRootedConfigurations D X Q).card ≤ X.card^3 := by
  obtain ⟨a,ha⟩ := card_pos.mp (show 0 < Q.card by omega)
  obtain ⟨b,hb,hba⟩ := exists_mem_ne (show 1 < Q.card by omega) a
  let E := localRootedConfigurations D X Q
  have hw (S : ↥E) : ∃ t : X × X × X,
      TripleWitness S.val Q a b (t.1.val,t.2.1.val,t.2.2.val) := by
    obtain ⟨hConf,hQS,hLocal⟩ := mem_filter.mp S.property
    obtain ⟨t,ht⟩ := exists_triple_witness (mem_configurations.mp hConf).2.2 hQS ha hb (Ne.symm hba)
    obtain ⟨A,B,hAS,hBS,hAQ,hBQ,hAB,hA,hB⟩ := ht
    have hAx := hLocal A hAS hAQ
    have hBx := hLocal B hBS hBQ
    have ht1 : t.1 ∈ X := hAx (by rw [hA]; simp)
    have ht2 : t.2.1 ∈ X := hAx (by rw [hA]; simp)
    have ht3 : t.2.2 ∈ X := hBx (by rw [hB]; simp)
    exact ⟨(⟨t.1,ht1⟩,⟨t.2.1,ht2⟩,⟨t.2.2,ht3⟩),A,B,hAS,hBS,hAQ,hBQ,hAB,hA,hB⟩
  choose f hf using hw
  have hInjective : Function.Injective f := by
    intro S T he
    apply Subtype.ext
    have hs := mem_filter.mp S.property
    have ht := mem_filter.mp T.property
    have hwT : TripleWitness T.val Q a b ((f S).1.val,(f S).2.1.val,(f S).2.2.val) := he.symm ▸ hf T
    exact eq_of_triple_witness (mem_configurations.mp hs.1).2.2
      (mem_configurations.mp ht.1).2.2 hs.2.1 ht.2.1 (hf S) hwT
  have hc := Fintype.card_le_of_injective f hInjective
  change E.card ≤ _
  simpa only [Fintype.card_coe,Fintype.card_prod,pow_succ,pow_zero,
    Nat.mul_one,Nat.one_mul,Nat.mul_assoc] using hc

#print axioms localPairExtensions_card_le
#print axioms localRootedConfigurations_card_le_cube
end TypedTriangle.Pasch
