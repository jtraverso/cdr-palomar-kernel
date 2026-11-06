module
public import RequestProject.TypedTriangle.CoreForkOnPool
public import RequestProject.TypedTriangle.PaschModeUniverse
public import RequestProject.TypedTriangle.PaschEmbeddingIncidence
set_option maxHeartbeats 4000000 -- build option (original: -DmaxHeartbeats=1600000; raised)
set_option maxRecDepth 16384 -- build option (original: -DmaxRecDepth=8192; raised)
@[expose] public section
open Finset Classical S07V26
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace TypedTriangle.Pasch
variable {V I : Type*} [Fintype V]

/-- The two literal positive modes, fixed before any later demand. -/
def forkModes (T : Finset (Sym2 V)) (fk : Sym2 V → Fork V) : Finset (Finset V) :=
  modeDec fk T ∅ ∪ modeDec fk T T

theorem forkModes_biUnion (T : Finset (Sym2 V)) (fk : Sym2 V → Fork V) :
    forkModes T fk = T.biUnion (fun e => {(fk e).T0,(fk e).T1,(fk e).T2}) := by
  have hOff : modeDec fk T ∅ = T.biUnion (fun e => {(fk e).T1,(fk e).T2}) := by
    unfold modeDec
    simp
  have hOn : modeDec fk T T = T.biUnion (fun e => {(fk e).T0}) := by
    unfold modeDec
    apply biUnion_congr rfl
    intro e he
    rw [if_pos he]
  rw [forkModes,hOff,hOn]
  ext Q
  simp only [mem_union,mem_biUnion,mem_insert,mem_singleton]
  constructor
  · rintro (⟨e,he,hQ⟩ | ⟨e,he,hQ⟩)
    · exact ⟨e,he,Or.inr hQ⟩
    · exact ⟨e,he,Or.inl hQ⟩
  · rintro ⟨e,he,hQ | hQ⟩
    · exact Or.inr ⟨e,he,hQ⟩
    · exact Or.inl ⟨e,he,hQ⟩

theorem fork_modes_subset_universe (T J : Finset (Sym2 V)) (fk : Sym2 V → Fork V) :
    modeDec fk T J ⊆ forkModes T fk := by
  rw [forkModes_biUnion]
  intro Q hQ
  obtain ⟨e,he,hQ⟩ := mem_biUnion.mp hQ
  refine mem_biUnion.mpr ⟨e,he,?_⟩
  by_cases heJ : e ∈ J
  · rw [if_pos heJ] at hQ
    exact mem_insert.mpr (Or.inl (mem_singleton.mp hQ))
  · rw [if_neg heJ] at hQ
    exact mem_insert_of_mem hQ

theorem fork_modes_pairCodegree {H : Host V I} {F : Set (Multiset I)}
    {W : Finset V} {X P : Finset (Sym2 V)} {fk : Sym2 V → Fork V}
    (hFS : ForkSystem H.G H.lab F W X P fk) :
    PairCodegreeBound (forkModes (XZ X W) fk) 2 := by
  have hOff := (hFS.fork_modes (I' := ∅) (empty_subset _)).1
  have hOn := (hFS.fork_modes (I' := XZ X W) (subset_refl _)).1
  have hOffP : IsPacking H F (modeDec fk (XZ X W) ∅) := ⟨hOff.1,hOff.2.1⟩
  have hOnP : IsPacking H F (modeDec fk (XZ X W) (XZ X W)) := ⟨hOn.1,hOn.2.1⟩
  exact pairCodegreeBound_two_modes hOffP hOnP

/-- The processed roots form their own literal fork system. This proves
codegree two once for the whole partial family, not once per fork. -/
theorem fork_modes_partial_pairCodegree {H : Host V I} {F : Set (Multiset I)}
    {W : Finset V} {X P T : Finset (Sym2 V)} {fk : Sym2 V → Fork V}
    (hTX : T ⊆ XZ X W)
    (hValid : ∀ e ∈ T, (fk e).root = e ∧ (fk e).Valid H.G H.lab F W)
    (hDis : ∀ e ∈ T, ∀ e' ∈ T, e ≠ e' → Disjoint (fk e).E (fk e').E)
    (hAvoid : ∀ e ∈ T, Disjoint (fk e).E (X∪P)) :
    PairCodegreeBound (forkModes T fk) 2 := by
  have hXZ : XZ T W = T := by
    apply Subset.antisymm (XZ_subset T W)
    intro e he
    exact mem_XZ.mpr ⟨he,(mem_XZ.mp (hTX he)).2⟩
  have hFS : ForkSystem H.G H.lab F W T P fk := by
    refine ⟨?_,?_,?_⟩
    · intro e he
      exact hValid e (XZ_subset T W he)
    · intro e he e' he' hne
      exact hDis e (XZ_subset T W he) e' (XZ_subset T W he') hne
    · intro e he
      exact (hAvoid e (XZ_subset T W he)).mono_right
        (union_subset_union (hTX.trans (XZ_subset X W)) (subset_refl _))
  simpa only [hXZ] using fork_modes_pairCodegree hFS

theorem forkModes_insert_update (T : Finset (Sym2 V)) (fk : Sym2 V → Fork V)
    (e : Sym2 V) (f : Fork V) (he : e ∉ T) :
    forkModes (insert e T) (Function.update fk e f) =
      {f.T0,f.T1,f.T2} ∪ forkModes T fk := by
  rw [forkModes_biUnion,biUnion_insert,Function.update_self,forkModes_biUnion]
  congr 1
  apply biUnion_congr rfl
  intro e' he'
  rw [Function.update_of_ne (fun h : e' = e => he (h ▸ he'))]

#print axioms forkModes_biUnion
#print axioms fork_modes_subset_universe
#print axioms fork_modes_pairCodegree
#print axioms fork_modes_partial_pairCodegree
#print axioms forkModes_insert_update
end TypedTriangle.Pasch
