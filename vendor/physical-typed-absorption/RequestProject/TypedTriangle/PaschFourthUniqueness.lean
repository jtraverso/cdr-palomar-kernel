module
public import RequestProject.TypedTriangle.PaschStatistics
set_option maxHeartbeats 4000000 -- build option (original: -DmaxHeartbeats=1600000; raised)
set_option maxRecDepth 16384 -- build option (original: -DmaxRecDepth=8192; raised)
@[expose] public section
open Finset Classical
set_option autoImplicit false
set_option maxHeartbeats 800000
namespace TypedTriangle.Pasch

theorem IsPasch.degree_zero_or_two {V : Type*} [DecidableEq V]
    {S : Finset (Finset V)} (hS : IsPasch S) (v : V) :
    (S.filter (fun Q => v ∈ Q)).card = 0 ∨ (S.filter (fun Q => v ∈ Q)).card = 2 := by
  by_cases hv : v ∈ S.biUnion id
  · exact Or.inr (hS.2.2.2.1 v hv)
  · left
    apply card_eq_zero.mpr
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro Q hQ
    obtain ⟨hQS,hvQ⟩ := mem_filter.mp hQ
    exact hv (mem_biUnion.mpr ⟨Q,hQS,hvQ⟩)

/-- Three common triples determine the fourth triple of a Pasch configuration. -/
theorem IsPasch.eq_of_common_triple {V : Type*} [DecidableEq V]
    {S T K : Finset (Finset V)} (hS : IsPasch S) (hT : IsPasch T)
    (hK : K.card = 3) (hKS : K ⊆ S) (hKT : K ⊆ T) : S = T := by
  have hSC : (S \ K).card = 1 := by rw [card_sdiff_of_subset hKS,hS.1,hK]
  have hTC : (T \ K).card = 1 := by rw [card_sdiff_of_subset hKT,hT.1,hK]
  obtain ⟨D,hD⟩ := card_eq_one.mp hSC
  obtain ⟨E,hE⟩ := card_eq_one.mp hTC
  have hDM : D ∈ S \ K := by rw [hD]; exact mem_singleton_self _
  have hEM : E ∈ T \ K := by rw [hE]; exact mem_singleton_self _
  have hDn := (mem_sdiff.mp hDM).2
  have hEn := (mem_sdiff.mp hEM).2
  have hSI : S = insert D K := by
    calc S = (S \ K) ∪ K := (sdiff_union_of_subset hKS).symm
      _ = insert D K := by rw [hD]; exact singleton_union _ _
  have hTI : T = insert E K := by
    calc T = (T \ K) ∪ K := (sdiff_union_of_subset hKT).symm
      _ = insert E K := by rw [hE]; exact singleton_union _ _
  have hDE : D = E := by
    ext v
    have hs := hS.degree_zero_or_two v
    have ht := hT.degree_zero_or_two v
    have hDF : D ∉ K.filter (fun Q => v ∈ Q) := fun hd => hDn (mem_filter.mp hd).1
    have hEF : E ∉ K.filter (fun Q => v ∈ Q) := fun he => hEn (mem_filter.mp he).1
    by_cases hd : v ∈ D <;> by_cases he : v ∈ E
    · simp only [hd,he]
    · simp only [hSI,hTI,filter_insert,hd,he,ite_true,ite_false,
        card_insert_of_notMem hDF,card_insert_of_notMem hEF] at hs ht
      omega
    · simp only [hSI,hTI,filter_insert,hd,he,ite_true,ite_false,
        card_insert_of_notMem hDF,card_insert_of_notMem hEF] at hs ht
      omega
    · simp only [hd,he]
  exact hSI.trans (hDE ▸ hTI.symm)

#print axioms IsPasch.degree_zero_or_two
#print axioms IsPasch.eq_of_common_triple
end TypedTriangle.Pasch
