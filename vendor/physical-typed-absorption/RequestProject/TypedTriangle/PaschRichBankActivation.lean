module
public import RequestProject.TypedTriangle.PaschRichBankHistory
set_option maxHeartbeats 4000000 -- build option (original: -DmaxHeartbeats=1600000; raised)
set_option maxRecDepth 16384 -- build option (original: -DmaxRecDepth=8192; raised)
@[expose] public section
open Finset Classical
noncomputable section
set_option autoImplicit false
namespace TypedTriangle.Pasch.RichBank
variable {V I Q C : Type*} [Fintype V] [AddCommGroup Q] [Fintype C]

private theorem off_subset {P : ℕ} {e : Entry V C P} {es : List (Entry V C P)}
    (he : e ∈ es) : e.off ⊆ offFamily es := by
  induction es with
  | nil => simp at he
  | cons f es ih =>
    rcases List.mem_cons.mp he with rfl | he
    · exact subset_union_left
    · exact (ih he).trans subset_union_right

private theorem on_subset {P : ℕ} {e : Entry V C P} {es : List (Entry V C P)}
    (he : e ∈ es) : e.on ⊆ onFamily es := by
  induction es with
  | nil => simp at he
  | cons f es ih =>
    rcases List.mem_cons.mp he with rfl | he
    · exact subset_union_left
    · exact (ih he).trans subset_union_right

private theorem decomposition_biUnion {J : Type*} (s : Finset J)
    {H : Host V I} {F : Set (Multiset I)}
    (E : J → Finset (Sym2 V)) (D : J → Finset (Finset V))
    (hE : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → Disjoint (E i) (E j))
    (hD : ∀ i ∈ s, IsDecomposition H F (E i) (D i)) :
    IsDecomposition H F (s.biUnion E) (s.biUnion D) := by
  have hSub : ∀ i ∈ s, ∀ T ∈ D i, triEdges T ⊆ E i := fun i hi T hT => (hD i hi).subset hT
  refine ⟨?_, ?_, ?_⟩
  · intro T hT
    obtain ⟨i,hi,hT⟩ := mem_biUnion.mp hT
    exact (hD i hi).1 T hT
  · intro T hT U hU hne
    obtain ⟨i,hi,hT⟩ := mem_biUnion.mp hT
    obtain ⟨j,hj,hU⟩ := mem_biUnion.mp hU
    by_cases hij : i=j
    · subst j
      exact (hD i hi).2.1 hT hU hne
    · exact (hE i hi j hj hij).mono (hSub i hi T hT) (hSub j hj U hU)
  · rw [biUnion_biUnion]
    exact biUnion_congr rfl (fun i hi => (hD i hi).2.2)

/-- Activation uses the stored off/on decompositions. In particular, this
does not call the legacy adapter that chooses new decompositions from Basal. -/
theorem fixed_cover_decomposition {H : Host V I} {F : Set (Multiset I)}
    {S : S07V40.MacroSetting V Q C} {Ub : ℕ} {pay : ℝ}
    {es : List (Entry V C S.P)} (h : ValidHistory H F S Ub pay es)
    (z : Fin S.P → C → ℤ) (hs : (toBank es).Supplies z) :
    ∃ D, IsDecomposition H F (S07V43.Bank.cover hs) D ∧ D ⊆ modes es ∧
      (count D:ℝ) ≤ es.length*pay := by
  let b := toBank es
  let Choice : Fin es.length → Finset (Finset V) := fun i =>
    if i ∈ S07V43.Bank.selJ hs then (es.get i).off else (es.get i).on
  have hChoice : ∀ i ∈ (univ : Finset (Fin es.length)),
      IsDecomposition H F (S07V43.Bank.mode hs i) (Choice i) := by
    intro i _
    have hi := h.good (es.get i) (List.get_mem ..)
    dsimp only [S07V43.Bank.mode, Choice]
    split_ifs
    · exact hi.off
    · exact hi.on
  have hDis : ∀ i ∈ (univ : Finset (Fin es.length)), ∀ j ∈ (univ : Finset (Fin es.length)),
      i ≠ j → Disjoint (S07V43.Bank.mode hs i) (S07V43.Bank.mode hs j) := by
    intro i _ j _ hij
    exact (h.bank_valid.pw i j hij).mono
      (S07V43.Bank.mode_subset hs i) (S07V43.Bank.mode_subset hs j)
  let D := univ.biUnion Choice
  have hSub : D ⊆ modes es := by
    intro T hT
    obtain ⟨i, _, hi⟩ := mem_biUnion.mp hT
    dsimp only [Choice] at hi
    split_ifs at hi with hsel
    · exact mem_union_left _ (off_subset (List.get_mem ..) hi)
    · exact mem_union_right _ (on_subset (List.get_mem ..) hi)
  have hCount : count D ≤ count (modes es) := by
    apply card_le_card
    intro P hP
    obtain ⟨hPD, hPcard, hPasch⟩ := mem_configurations.mp hP
    exact mem_configurations.mpr ⟨hPD.trans hSub, hPcard, hPasch⟩
  refine ⟨D, decomposition_biUnion univ _ Choice hDis hChoice, hSub, ?_⟩
  exact (show (count D:ℝ) ≤ count (modes es) by exact_mod_cast hCount).trans h.budget

end TypedTriangle.Pasch.RichBank
#print axioms TypedTriangle.Pasch.RichBank.fixed_cover_decomposition
