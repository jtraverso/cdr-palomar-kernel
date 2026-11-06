module
public import RequestProject.TypedTriangle.PaschMixedAssembly
public import RequestProject.TypedTriangle.PaschEdgeAveraging
set_option maxHeartbeats 4000000 -- build option (original: -DmaxHeartbeats=1600000; raised)
set_option maxRecDepth 16384 -- build option (original: -DmaxRecDepth=8192; raised)
@[expose] public section
open Finset Classical
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1500000
namespace TypedTriangle.Pasch
variable {V : Type*} [DecidableEq V]

private theorem crossing_points_ne {S : Finset (Finset V)} (hS : IsPasch S)
    {Q B T : Finset V} (hQ : Q ∈ S) (hB : B ∈ S) (hT : T ∈ S)
    (hQB : Q ≠ B) (hTQ : T ≠ Q) (hTB : T ≠ B)
    {a b : V} (haQ : a ∈ Q) (haT : a ∈ T) (hbB : b ∈ B) (hbT : b ∈ T) : a ≠ b := by
  intro hab
  subst b
  have hSub : ({Q,B,T} : Finset (Finset V)) ⊆ S.filter (fun C => a ∈ C) := by
    intro C hC
    simp only [mem_insert,mem_singleton] at hC
    rcases hC with rfl | rfl | rfl
    · exact mem_filter.mpr ⟨hQ,haQ⟩
    · exact mem_filter.mpr ⟨hB,hbB⟩
    · exact mem_filter.mpr ⟨hT,haT⟩
  have hCard : ({Q,B,T} : Finset (Finset V)).card = 3 := by
    simp [hQB,hTQ,hTB,Ne.symm hTQ,Ne.symm hTB]
  have hDegree := hS.degree_zero_or_two a
  have hh := card_le_card hSub
  omega

/-- A two-block new part leaves only boundedly many completions in an old
family of bounded pair-codegree. The old family need not be a packing. -/
theorem completionCount_pair_le {R : Finset (Finset V)} {L : ℕ}
    (hL : PairCodegreeBound R L) (Q B : Finset V) (hQB : Q ≠ B) :
    completionCount R {Q,B} ≤ 9*L := by
  let C := (configurations (({Q,B} : Finset (Finset V)) ∪ R)).filter
    (fun K => K\R = {Q,B})
  change C.card ≤ _
  by_cases hC : C = ∅
  · simp only [hC,card_empty,Nat.zero_le]
  obtain ⟨K0,hK0⟩ := nonempty_iff_ne_empty.mpr hC
  obtain ⟨hConf0,hDiff0⟩ := mem_filter.mp hK0
  have hPasch0 := (mem_configurations.mp hConf0).2.2
  have hQ0 : Q ∈ K0 := sdiff_subset (hDiff0.symm ▸ mem_insert_self Q {B})
  have hB0 : B ∈ K0 := sdiff_subset (hDiff0.symm ▸ (by simp : B ∈ ({Q,B} : Finset (Finset V))))
  have hQcard := hPasch0.2.1 Q hQ0
  have hBcard := hPasch0.2.1 B hB0
  let U := Q.biUnion (fun a => B.biUnion (fun b =>
    if a = b then ∅ else R.filter (fun T => a ∈ T ∧ b ∈ T)))
  have hWitness : ∀ K ∈ C, ∃ T ∈ U, T ∈ K ∧ T ≠ Q ∧ T ≠ B := by
    intro K hK
    obtain ⟨hConf,hDiff⟩ := mem_filter.mp hK
    have hPasch := (mem_configurations.mp hConf).2.2
    have hQK : Q ∈ K := sdiff_subset (hDiff.symm ▸ mem_insert_self Q {B})
    have hBK : B ∈ K := sdiff_subset (hDiff.symm ▸ (by simp : B ∈ ({Q,B} : Finset (Finset V))))
    have hNot : ¬ K ⊆ {Q,B} := by
      intro hSub
      have hh := card_le_card hSub
      have hp : ({Q,B} : Finset (Finset V)).card = 2 := by simp [hQB]
      have hk := hPasch.1
      omega
    obtain ⟨T,hTK,hTNot⟩ := Finset.not_subset.mp hNot
    have hTQ : T ≠ Q := by intro h; exact hTNot (by simp [h])
    have hTB : T ≠ B := by intro h; exact hTNot (by simp [h])
    have hTR : T ∈ R := by
      have hUnion := (mem_configurations.mp hConf).1 hTK
      exact (mem_union.mp hUnion).resolve_left hTNot
    obtain ⟨a,ha⟩ := inter_nonempty hPasch hTK hQK hTQ
    obtain ⟨b,hb⟩ := inter_nonempty hPasch hTK hBK hTB
    have haT := (mem_inter.mp ha).1
    have haQ := (mem_inter.mp ha).2
    have hbT := (mem_inter.mp hb).1
    have hbB := (mem_inter.mp hb).2
    have hab := crossing_points_ne hPasch hQK hBK hTK hQB hTQ hTB haQ haT hbB hbT
    refine ⟨T,mem_biUnion.mpr ⟨a,haQ,mem_biUnion.mpr ⟨b,hbB,?_⟩⟩,hTK,hTQ,hTB⟩
    rw [if_neg hab]
    exact mem_filter.mpr ⟨hTR,haT,hbT⟩
  let f : ↥C → ↥U := fun K =>
    ⟨Classical.choose (hWitness K.val K.property),
      (Classical.choose_spec (hWitness K.val K.property)).1⟩
  have hf : Function.Injective f := by
    intro K K' heq
    have hT := (Classical.choose_spec (hWitness K.val K.property)).2
    have hT' := (Classical.choose_spec (hWitness K'.val K'.property)).2
    have hTT : (f K).val = (f K').val := congrArg Subtype.val heq
    obtain ⟨hConf,hDiff⟩ := mem_filter.mp K.property
    obtain ⟨hConf',hDiff'⟩ := mem_filter.mp K'.property
    have hPasch := (mem_configurations.mp hConf).2.2
    have hPasch' := (mem_configurations.mp hConf').2.2
    have hQK : Q ∈ K.val := sdiff_subset (hDiff.symm ▸ mem_insert_self Q {B})
    have hBK : B ∈ K.val := sdiff_subset (hDiff.symm ▸ (by simp : B ∈ ({Q,B} : Finset (Finset V))))
    have hQK' : Q ∈ K'.val := sdiff_subset (hDiff'.symm ▸ mem_insert_self Q {B})
    have hBK' : B ∈ K'.val := sdiff_subset (hDiff'.symm ▸ (by simp : B ∈ ({Q,B} : Finset (Finset V))))
    change (f K).val ∈ K.val ∧ (f K).val ≠ Q ∧ (f K).val ≠ B at hT
    change (f K').val ∈ K'.val ∧ (f K').val ≠ Q ∧ (f K').val ≠ B at hT'
    have hTK : (f K).val ∈ K.val := hT.1
    have hTK' : (f K).val ∈ K'.val := hTT.symm ▸ hT'.1
    have hCard : ({Q,B,(f K).val} : Finset (Finset V)).card = 3 := by
      simp [hQB,hT.2.1,hT.2.2,Ne.symm hT.2.1,Ne.symm hT.2.2]
    apply Subtype.ext
    apply hPasch.eq_of_common_triple hPasch' hCard
    · intro T hTmem
      simp only [mem_insert,mem_singleton] at hTmem
      rcases hTmem with rfl | rfl | rfl <;> assumption
    · intro T hTmem
      simp only [mem_insert,mem_singleton] at hTmem
      rcases hTmem with rfl | rfl | rfl <;> assumption
  have hCU : C.card ≤ U.card := by
    simpa only [Fintype.card_coe] using Fintype.card_le_of_injective f hf
  have hU : U.card ≤ 9*L := by
    calc
      U.card ≤ ∑ a ∈ Q, (B.biUnion (fun b =>
          if a = b then ∅ else R.filter (fun T => a ∈ T ∧ b ∈ T))).card := card_biUnion_le
      _ ≤ ∑ _a ∈ Q, B.card*L := by
        apply sum_le_sum
        intro a ha
        apply card_biUnion_le.trans
        calc
          _ ≤ ∑ _b ∈ B, L := by
            apply sum_le_sum
            intro b hb
            split_ifs with hab
            · simp
            · exact hL a b hab
          _ = B.card*L := by simp
      _ = 9*L := by simp only [sum_const_nat,hQcard,hBcard]; omega
  exact hCU.trans hU

theorem completionCount_two_le {R : Finset (Finset V)} {L : ℕ}
    (hL : PairCodegreeBound R L) (S : Finset (Finset V)) (hS : S.card = 2) :
    completionCount R S ≤ 9*L := by
  obtain ⟨Q,B,hQB,rfl⟩ := card_eq_two.mp hS
  exact completionCount_pair_le hL Q B hQB

theorem completionCount_three_le (R S : Finset (Finset V)) (hS : S.card = 3) :
    completionCount R S ≤ 1 := by
  apply card_le_one.mpr
  intro K hK K' hK'
  obtain ⟨hConf,hDiff⟩ := mem_filter.mp hK
  obtain ⟨hConf',hDiff'⟩ := mem_filter.mp hK'
  have hSK : S ⊆ K := hDiff ▸ sdiff_subset
  have hSK' : S ⊆ K' := hDiff' ▸ sdiff_subset
  exact (mem_configurations.mp hConf).2.2.eq_of_common_triple
    (mem_configurations.mp hConf').2.2 hS hSK hSK'

end TypedTriangle.Pasch

#print axioms TypedTriangle.Pasch.completionCount_pair_le
#print axioms TypedTriangle.Pasch.completionCount_two_le
#print axioms TypedTriangle.Pasch.completionCount_three_le
