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

def pairExtensions (D : Finset (Finset V)) (Q B : Finset V) : Finset (Finset (Finset V)) :=
  (configurations D).filter (fun S => Q ∈ S ∧ B ∈ S)

def tripleExtensions (D : Finset (Finset V)) (K : Finset (Finset V)) :
    Finset (Finset (Finset V)) :=
  (configurations D).filter (fun S => K ⊆ S)

private theorem third_vertex {T : Finset V} (hT : T.card = 3)
    {a x : V} (ha : a ∈ T) (hx : x ∈ T) (hax : a ≠ x) :
    ∃ z, T = {a,x,z} := by
  have hNot : ¬ T ⊆ {a,x} := by
    intro h
    have hh := card_le_card h
    have hp : ({a,x} : Finset V).card = 2 := by simp [hax]
    omega
  obtain ⟨z,hz,hzNot⟩ := Finset.not_subset.mp hNot
  have haz : a ≠ z := by intro h; exact hzNot (by simp [h])
  have hxz : x ≠ z := by intro h; exact hzNot (by simp [h])
  refine ⟨z, (eq_of_subset_of_card_le ?_ ?_).symm⟩
  · intro y hy
    simp only [mem_insert,mem_singleton] at hy
    rcases hy with rfl | rfl | rfl <;> assumption
  · have hp : ({a,x,z} : Finset V).card = 3 := by simp [hax,haz,hxz]
    omega

private theorem pair_extension_witness {S : Finset (Finset V)} (hS : IsPasch S)
    {Q B : Finset V} (hQ : Q ∈ S) (hB : B ∈ S) (hQB : Q ≠ B)
    {v a : V} (hvQ : v ∈ Q) (hvB : v ∈ B) (haQ : a ∈ Q) (hva : v ≠ a) :
    ∃ p : ↥(B\Q) × V, ∃ T, T ∈ S ∧ T ≠ Q ∧ T ≠ B ∧
      T = {a,p.1.val,p.2} := by
  obtain ⟨x,A,T,hAS,hTS,hAQ,hTQ,hAT,hvA,haT,hxA,hxT,hxQ⟩ :=
    exists_rooted_witness hS hQ hvQ haQ hva
  have hUnique := exists_unique_other hS hQ hvQ
  have hAB : A = B := hUnique.unique ⟨hAS,hAQ,hvA⟩ ⟨hB,Ne.symm hQB,hvB⟩
  subst A
  have hax : a ≠ x := by intro h; exact hxQ (h ▸ haQ)
  obtain ⟨z,hT⟩ := third_vertex (hS.2.1 T hTS) haT hxT hax
  exact ⟨(⟨x,mem_sdiff.mpr ⟨hxA,hxQ⟩⟩,z),T,hTS,hTQ,Ne.symm hAT,hT⟩

/-- Two fixed distinct blocks have at most `2*n` extensions to a Pasch in
an arbitrary triangle domain. No packing hypothesis is used. -/
theorem pairExtensions_card_le [Fintype V] (D : Finset (Finset V))
    (Q B : Finset V) (hQB : Q ≠ B) :
    (pairExtensions D Q B).card ≤ 2*Fintype.card V := by
  let E := pairExtensions D Q B
  by_cases hEmpty : E = ∅
  · simp only [E] at hEmpty
    simp only [hEmpty,card_empty,Nat.zero_le]
  have hNonempty : E.Nonempty := nonempty_iff_ne_empty.mpr hEmpty
  obtain ⟨S0,hS0⟩ := hNonempty
  obtain ⟨hConf0,hQ0,hB0⟩ := mem_filter.mp hS0
  have hPasch0 := (mem_configurations.mp hConf0).2.2
  have hIntersect := inter_card_eq_one hPasch0 hQ0 hB0 hQB
  obtain ⟨v,hv⟩ := card_pos.mp (by omega : 0 < (Q∩B).card)
  have hvQ := (mem_inter.mp hv).1
  have hvB := (mem_inter.mp hv).2
  have hNot : ¬ Q ⊆ {v} := by
    intro h
    have hh := card_le_card h
    have hQcard := hPasch0.2.1 Q hQ0
    simp only [card_singleton] at hh
    omega
  obtain ⟨a,haQ,haNot⟩ := Finset.not_subset.mp hNot
  have hva : v ≠ a := by intro h; exact haNot (by simp [h])
  have hWitness : ∀ S ∈ E, ∃ p : ↥(B\Q) × V, ∃ T,
      T ∈ S ∧ T ≠ Q ∧ T ≠ B ∧ T = {a,p.1.val,p.2} := by
    intro S hS
    obtain ⟨hConf,hQ,hB⟩ := mem_filter.mp hS
    exact pair_extension_witness (mem_configurations.mp hConf).2.2 hQ hB hQB hvQ hvB haQ hva
  let f : ↥E → ↥(B\Q) × V := fun S => Classical.choose (hWitness S.val S.property)
  have hf : Function.Injective f := by
    intro S T hEq
    obtain ⟨A,hAS,hAQ,hAB,hA⟩ := Classical.choose_spec (hWitness S.val S.property)
    obtain ⟨A',hAT,hA'Q,hA'B,hA'⟩ := Classical.choose_spec (hWitness T.val T.property)
    have hAA : A = A' := by
      change A = A'
      change A = {a,(f S).1.val,(f S).2} at hA
      change A' = {a,(f T).1.val,(f T).2} at hA'
      rw [hA,hA',hEq]
    have hATcommon : A ∈ T.val := by rw [hAA]; exact hAT
    obtain ⟨hConfS,hQS,hBS⟩ := mem_filter.mp S.property
    obtain ⟨hConfT,hQT,hBT⟩ := mem_filter.mp T.property
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
  have hDiff : (B\Q).card = 2 := by
    rw [card_sdiff,hIntersect,hPasch0.2.1 B hB0]
  simpa only [Fintype.card_coe,Fintype.card_prod,hDiff] using hCard

/-- Three fixed blocks determine at most one Pasch, even before a packing
has been selected. -/
theorem tripleExtensions_card_le (D : Finset (Finset V))
    (K : Finset (Finset V)) (hK : K.card = 3) :
    (tripleExtensions D K).card ≤ 1 := by
  apply card_le_one.mpr
  intro S hS T hT
  obtain ⟨hS,hKS⟩ := mem_filter.mp hS
  obtain ⟨hT,hKT⟩ := mem_filter.mp hT
  exact (mem_configurations.mp hS).2.2.eq_of_common_triple
    (mem_configurations.mp hT).2.2 hK hKS hKT

end TypedTriangle.Pasch

#print axioms TypedTriangle.Pasch.pairExtensions_card_le
#print axioms TypedTriangle.Pasch.tripleExtensions_card_le
