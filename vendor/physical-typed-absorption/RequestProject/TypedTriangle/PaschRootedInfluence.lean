module
public import RequestProject.TypedTriangle.PaschFourthUniqueness
public import RequestProject.TypedTriangle.Packing
set_option maxHeartbeats 4000000 -- build option (original: -DmaxHeartbeats=1600000; raised)
set_option maxRecDepth 16384 -- build option (original: -DmaxRecDepth=8192; raised)
@[expose] public section
open Finset Classical
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 800000
namespace TypedTriangle.Pasch
variable {V : Type*} [DecidableEq V]

/-- Every pair of triples in a Pasch intersects. The six-point support and
linearity exclude a disjoint pair. -/
theorem inter_nonempty {S : Finset (Finset V)} (hS : IsPasch S)
    {A B : Finset V} (hA : A ∈ S) (hB : B ∈ S) (hAB : A ≠ B) :
    (A ∩ B).Nonempty := by
  by_contra hn
  have hdis : Disjoint A B := disjoint_iff_inter_eq_empty.mpr
    (not_nonempty_iff_eq_empty.mp hn)
  have hc : (A ∪ B).card = 6 := by rw [card_union_of_disjoint hdis, hS.2.1 A hA, hS.2.1 B hB]
  have hsub : A ∪ B ⊆ S.biUnion id := by
    intro v hv
    rcases mem_union.mp hv with hv | hv
    · exact mem_biUnion.mpr ⟨A,hA,hv⟩
    · exact mem_biUnion.mpr ⟨B,hB,hv⟩
  have heq : A ∪ B = S.biUnion id := eq_of_subset_of_card_le hsub (by rw [hS.2.2.1,hc])
  have hnot : ¬ S ⊆ {A,B} := by
    intro h
    have hle := card_le_card h
    have hp : ({A,B} : Finset (Finset V)).card ≤ 2 := by simp [hAB]
    rw [hS.1] at hle
    omega
  obtain ⟨Q,hQ,hQnot⟩ := Finset.not_subset.mp hnot
  have hQA : Q ≠ A := by intro he; exact hQnot (by simp [he])
  have hQB : Q ≠ B := by intro he; exact hQnot (by simp [he])
  have hQsub : Q ⊆ A ∪ B := by
    intro v hv
    rw [heq]
    exact mem_biUnion.mpr ⟨Q,hQ,hv⟩
  have hcard : Q.card ≤ (Q ∩ A).card + (Q ∩ B).card := by
    calc Q.card = (Q ∩ (A ∪ B)).card := by rw [inter_eq_left.mpr hQsub]
      _ = ((Q ∩ A) ∪ (Q ∩ B)).card := by rw [inter_union_distrib_left]
      _ ≤ _ := card_union_le _ _
  have hqA := hS.2.2.2.2 hQ hA hQA
  have hqB := hS.2.2.2.2 hQ hB hQB
  have hq3 := hS.2.1 Q hQ
  omega

theorem inter_card_eq_one {S : Finset (Finset V)} (hS : IsPasch S)
    {A B : Finset V} (hA : A ∈ S) (hB : B ∈ S) (hAB : A ≠ B) :
    (A ∩ B).card = 1 := by
  have hp := card_pos.mpr (inter_nonempty hS hA hB hAB)
  have hu := hS.2.2.2.2 hA hB hAB
  omega

/-- In a linear family, an edge is contained in at most one triple. -/
theorem eq_of_common_pair {D : Finset (Finset V)}
    (hD : (D : Set (Finset V)).Pairwise (fun A B => (A ∩ B).card ≤ 1))
    {A B : Finset V} (hA : A ∈ D) (hB : B ∈ D) {a b : V} (hab : a ≠ b)
    (haA : a ∈ A) (hbA : b ∈ A) (haB : a ∈ B) (hbB : b ∈ B) : A = B := by
  by_contra hne
  have hcard := hD hA hB hne
  have hsub : ({a,b} : Finset V) ⊆ A ∩ B := by
    intro v hv
    rcases mem_insert.mp hv with rfl | hv
    · exact mem_inter.mpr ⟨haA,haB⟩
    · have hvb := mem_singleton.mp hv
      subst v
      exact mem_inter.mpr ⟨hbA,hbB⟩
  have hc := card_le_card hsub
  have ht : ({a,b} : Finset V).card = 2 := by simp [hab]
  omega

/-- At each vertex of a rooted triple there is exactly one other triple. -/
theorem exists_unique_other {S : Finset (Finset V)} (hS : IsPasch S)
    {Q : Finset V} (hQ : Q ∈ S) {a : V} (ha : a ∈ Q) :
    ∃! A, A ∈ S ∧ A ≠ Q ∧ a ∈ A := by
  have has : a ∈ S.biUnion id := mem_biUnion.mpr ⟨Q,hQ,ha⟩
  have hc := hS.2.2.2.1 a has
  obtain ⟨A,B,hAB,hEq⟩ := card_eq_two.mp hc
  have hQf : Q ∈ S.filter (fun T => a ∈ T) := mem_filter.mpr ⟨hQ,ha⟩
  rw [hEq] at hQf
  rcases mem_insert.mp hQf with hQA | hQB
  · subst Q
    refine ⟨B,?_,?_⟩
    · have hBf : B ∈ S.filter (fun T => a ∈ T) := by rw [hEq]; simp
      exact ⟨(mem_filter.mp hBf).1,Ne.symm hAB,(mem_filter.mp hBf).2⟩
    · rintro T ⟨hT,hTA,haT⟩
      have hTf : T ∈ S.filter (fun T => a ∈ T) := mem_filter.mpr ⟨hT,haT⟩
      rw [hEq] at hTf
      rcases mem_insert.mp hTf with h | h
      · exact (hTA h).elim
      · exact mem_singleton.mp h
  · have hQB := mem_singleton.mp hQB
    subst Q
    refine ⟨A,?_,?_⟩
    · have hAf : A ∈ S.filter (fun T => a ∈ T) := by rw [hEq]; simp
      exact ⟨(mem_filter.mp hAf).1,hAB,(mem_filter.mp hAf).2⟩
    · rintro T ⟨hT,hTB,haT⟩
      have hTf : T ∈ S.filter (fun T => a ∈ T) := mem_filter.mpr ⟨hT,haT⟩
      rw [hEq] at hTf
      rcases mem_insert.mp hTf with h | h
      · exact h
      · exact (hTB (mem_singleton.mp h)).elim

/-- The two non-root blocks through fixed distinct root vertices meet at an
external vertex. This vertex will encode the rooted configuration. -/
def RootedWitness (S : Finset (Finset V)) (Q : Finset V) (a b x : V) : Prop :=
  ∃ A B, A ∈ S ∧ B ∈ S ∧ A ≠ Q ∧ B ≠ Q ∧ A ≠ B ∧
    a ∈ A ∧ b ∈ B ∧ x ∈ A ∧ x ∈ B ∧ x ∉ Q

theorem exists_rooted_witness {S : Finset (Finset V)} (hS : IsPasch S)
    {Q : Finset V} (hQ : Q ∈ S) {a b : V} (ha : a ∈ Q) (hb : b ∈ Q) (hab : a ≠ b) :
    ∃ x, RootedWitness S Q a b x := by
  obtain ⟨A,⟨hAS,hAQ,haA⟩,_⟩ := exists_unique_other hS hQ ha
  obtain ⟨B,⟨hBS,hBQ,hbB⟩,_⟩ := exists_unique_other hS hQ hb
  have hAB : A ≠ B := by
    intro he
    have hbA : b ∈ A := by simpa only [he] using hbB
    exact hAQ (eq_of_common_pair hS.2.2.2.2 hAS hQ hab haA hbA ha hb)
  obtain ⟨x,hx⟩ := inter_nonempty hS hAS hBS hAB
  have hxA := (mem_inter.mp hx).1
  have hxB := (mem_inter.mp hx).2
  have hxQ : x ∉ Q := by
    intro hxQ
    have hxa : x = a := by
      by_contra hne
      exact hAQ (eq_of_common_pair hS.2.2.2.2 hAS hQ hne hxA haA hxQ ha)
    have hxb : x = b := by
      by_contra hne
      exact hBQ (eq_of_common_pair hS.2.2.2.2 hBS hQ hne hxB hbB hxQ hb)
    exact hab (hxa.symm.trans hxb)
  exact ⟨x,A,B,hAS,hBS,hAQ,hBQ,hAB,haA,hbB,hxA,hxB,hxQ⟩

theorem eq_of_rooted_witness {D S T : Finset (Finset V)}
    (hD : (D : Set (Finset V)).Pairwise (fun A B => (A ∩ B).card ≤ 1))
    (hS : IsPasch S) (hT : IsPasch T) (hSD : S ⊆ D) (hTD : T ⊆ D)
    {Q : Finset V} (hQS : Q ∈ S) (hQT : Q ∈ T) {a b x : V}
    (ha : a ∈ Q) (hb : b ∈ Q)
    (hwS : RootedWitness S Q a b x) (hwT : RootedWitness T Q a b x) : S = T := by
  obtain ⟨A,B,hAS,hBS,hAQ,hBQ,hAB,haA,hbB,hxA,hxB,hxQ⟩ := hwS
  obtain ⟨A',B',hAT,hBT,hA'Q,hB'Q,hA'B',haA',hbB',hxA',hxB',_⟩ := hwT
  have hax : a ≠ x := by intro he; exact hxQ (he ▸ ha)
  have hbx : b ≠ x := by intro he; exact hxQ (he ▸ hb)
  have hAA : A = A' := eq_of_common_pair hD (hSD hAS) (hTD hAT) hax haA hxA haA' hxA'
  have hBB : B = B' := eq_of_common_pair hD (hSD hBS) (hTD hBT) hbx hbB hxB hbB' hxB'
  subst A'
  subst B'
  have hcard : ({Q,A,B} : Finset (Finset V)).card = 3 := by
    simp [hAQ,hBQ,hAB,Ne.symm hAQ,Ne.symm hBQ]
  apply hS.eq_of_common_triple hT hcard
  · intro U hU
    simp only [mem_insert,mem_singleton] at hU
    rcases hU with rfl | rfl | rfl <;> assumption
  · intro U hU
    simp only [mem_insert,mem_singleton] at hU
    rcases hU with rfl | rfl | rfl <;> assumption

theorem rootedCount_le_complement [Fintype V] {D : Finset (Finset V)}
    (hD : (D : Set (Finset V)).Pairwise (fun A B => (A ∩ B).card ≤ 1))
    (Q : Finset V) (hQcard : Q.card = 3) :
    rootedCount D Q ≤ Fintype.card V - 3 := by
  obtain ⟨a,ha⟩ := card_pos.mp (show 0 < Q.card by omega)
  obtain ⟨b,hb,hba⟩ := exists_mem_ne (show 1 < Q.card by omega) a
  let R := (configurations D).filter (fun S => Q ∈ S)
  let U := (univ : Finset V) \ Q
  have hw (S : {S // S ∈ R}) : ∃ x : {v // v ∈ U}, RootedWitness S.val Q a b x.val := by
    have hSm := mem_filter.mp S.property
    have hSc := mem_configurations.mp hSm.1
    obtain ⟨x,hx⟩ := exists_rooted_witness hSc.2.2 hSm.2 ha hb (Ne.symm hba)
    have hxQ : x ∉ Q := by obtain ⟨_,_,_,_,_,_,_,_,_,_,_,hxQ⟩ := hx; exact hxQ
    exact ⟨⟨x,mem_sdiff.mpr ⟨mem_univ _,hxQ⟩⟩,hx⟩
  choose f hf using hw
  have hinj : Function.Injective f := by
    intro S T he
    apply Subtype.ext
    have hSm := mem_filter.mp S.property
    have hTm := mem_filter.mp T.property
    have hSc := mem_configurations.mp hSm.1
    have hTc := mem_configurations.mp hTm.1
    have heval : (f S).val = (f T).val := congrArg Subtype.val he
    have hT' : RootedWitness T.val Q a b (f S).val := heval.symm ▸ hf T
    exact eq_of_rooted_witness hD hSc.2.2 hTc.2.2 hSc.1 hTc.1 hSm.2 hTm.2 ha hb (hf S) hT'
  have hcard := Fintype.card_le_of_injective f hinj
  have hc : R.card ≤ U.card := by simpa only [Fintype.card_coe] using hcard
  have hU : U.card = Fintype.card V - 3 := by
    dsimp only [U]
    rw [card_sdiff_of_subset (subset_univ Q),card_univ,hQcard]
  change R.card ≤ _
  exact hc.trans_eq hU

theorem packing_linear {I : Type*} [Fintype V] {H : Host V I}
    {F : Set (Multiset I)} {D : Finset (Finset V)} (hD : IsPacking H F D) :
    (D : Set (Finset V)).Pairwise (fun A B => (A ∩ B).card ≤ 1) := by
  intro A hA B hB hAB
  apply card_le_one.mpr
  intro a ha b hb
  by_contra hab
  have hEA : s(a,b) ∈ triEdges A := mem_triEdges.mpr
    ⟨(mem_inter.mp ha).1,(mem_inter.mp hb).1,hab⟩
  have hEB : s(a,b) ∈ triEdges B := mem_triEdges.mpr
    ⟨(mem_inter.mp ha).2,(mem_inter.mp hb).2,hab⟩
  exact (Finset.disjoint_left.mp (hD.2 hA hB hAB)) hEA hEB

theorem rootedCount_le_of_packing {I : Type*} [Fintype V] {H : Host V I}
    {F : Set (Multiset I)} {D : Finset (Finset V)} (hD : IsPacking H F D)
    {Q : Finset V} (hQ : Q ∈ D) : rootedCount D Q ≤ Fintype.card V - 3 :=
  rootedCount_le_complement (packing_linear hD) Q (hD.1 Q hQ).1

/-- An actual bound on configuration weights scales the proved root count;
there is no extra hypothesis on the final decomposition. -/
theorem rootedInfluence_le_weight_mul_count (w : Finset (Finset V) → ℝ)
    (D : Finset (Finset V)) (Q : Finset V) (B : ℝ)
    (hw : ∀ S ∈ configurations D, |w S| ≤ B) :
    rootedInfluence w D Q ≤ B * rootedCount D Q := by
  rw [rootedInfluence_eq_sum]
  calc (∑ S ∈ (configurations D).filter (fun S => Q ∈ S), |w S|)
      ≤ ∑ _S ∈ (configurations D).filter (fun S => Q ∈ S), B :=
      sum_le_sum (fun S hS => hw S (mem_filter.mp hS).1)
    _ = B * rootedCount D Q := by simp [rootedCount,mul_comm]

theorem rootedInfluence_one_le_of_packing {I : Type*} [Fintype V] {H : Host V I}
    {F : Set (Multiset I)} {D : Finset (Finset V)} (hD : IsPacking H F D)
    {Q : Finset V} (hQ : Q ∈ D) :
    rootedInfluence (fun _ => 1) D Q ≤ (Fintype.card V - 3 : ℕ) := by
  rw [← rootedCount_eq_influence_one]
  exact_mod_cast rootedCount_le_of_packing hD hQ

/-- A concrete deletion/completion budget for two actual packings. The
factor n−3 is proved combinatorially, not imposed as a final hypothesis. -/
theorem count_difference_le_of_packings {I : Type*} [Fintype V] {H : Host V I}
    {F : Set (Multiset I)} {D E : Finset (Finset V)}
    (hD : IsPacking H F D) (hE : IsPacking H F E) :
    |(count D : ℝ) - count E| ≤
      ((Fintype.card V - 3 : ℕ) : ℝ) * max ((D \ E).card : ℝ) ((E \ D).card : ℝ) := by
  have hs := nonnegative_statistic_difference_le_max (fun _ => (1:ℝ)) D E (fun _ => zero_le_one)
  rw [← count_eq_statistic_one,← count_eq_statistic_one] at hs
  have hd : (∑ Q ∈ D \ E, rootedInfluence (fun _ => 1) D Q) ≤
      ((Fintype.card V - 3 : ℕ) : ℝ) * (D \ E).card := by
    calc _ ≤ ∑ _Q ∈ D \ E, ((Fintype.card V - 3 : ℕ) : ℝ) :=
      sum_le_sum (fun Q hQ => rootedInfluence_one_le_of_packing hD (mem_sdiff.mp hQ).1)
      _ = _ := by simp [mul_comm]
  have he : (∑ Q ∈ E \ D, rootedInfluence (fun _ => 1) E Q) ≤
      ((Fintype.card V - 3 : ℕ) : ℝ) * (E \ D).card := by
    calc _ ≤ ∑ _Q ∈ E \ D, ((Fintype.card V - 3 : ℕ) : ℝ) :=
      sum_le_sum (fun Q hQ => rootedInfluence_one_le_of_packing hE (mem_sdiff.mp hQ).1)
      _ = _ := by simp [mul_comm]
  exact hs.trans ((max_le_max hd he).trans_eq (mul_max_of_nonneg ((D \ E).card : ℝ) ((E \ D).card : ℝ) (Nat.cast_nonneg (Fintype.card V - 3))).symm)

#print axioms inter_nonempty
#print axioms inter_card_eq_one
#print axioms eq_of_common_pair
#print axioms exists_unique_other
#print axioms exists_rooted_witness
#print axioms eq_of_rooted_witness
#print axioms rootedCount_le_complement
#print axioms packing_linear
#print axioms rootedCount_le_of_packing
#print axioms rootedInfluence_le_weight_mul_count
#print axioms rootedInfluence_one_le_of_packing
#print axioms count_difference_le_of_packings
end TypedTriangle.Pasch
