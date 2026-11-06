module
public import RequestProject.TypedTriangle.PaschSeededBankRun
public import RequestProject.S07V43.Bridge
set_option maxHeartbeats 4000000 -- build option (original: -DmaxHeartbeats=1600000; raised)
set_option maxRecDepth 16384 -- build option (original: -DmaxRecDepth=8192; raised)
@[expose] public section
open Finset Classical
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1200000
namespace TypedTriangle.Pasch.RichBank.Actual
open S07V40 S07V43
variable {V I Q C A : Type*} [Fintype V] [AddCommGroup Q] [Fintype C] [Fintype A]

/-- A bank indexed by actual positions; repeated or empty cells remain distinct occurrences. -/
def occurrenceBank {P : ℕ} (es : List (Entry V C P)) (κ : A ↪ Fin es.length) : Bank V A C P where
  sgn i := (es.get (κ i)).lab.1
  cat i := (es.get (κ i)).lab.2.1
  col i := (es.get (κ i)).lab.2.2
  A i := (es.get (κ i)).cell.A
  Y i := (es.get (κ i)).cell.Y

abbrev SliceOcc {P : ℕ} (es : List (Entry V C P)) (p : ℕ → Prop) :=
  {i : Fin es.length // p (es.get i).round}

def sliceBank {P : ℕ} (es : List (Entry V C P)) (p : ℕ → Prop) :
    Bank V (SliceOcc es p) C P := occurrenceBank es (Function.Embedding.subtype _)

theorem occurrence_valid {H : Host V I} {F : Set (Multiset I)} {S : MacroSetting V Q C}
    {Ub : ℕ} {pay : ℝ} {es : List (Entry V C S.P)} (h : ValidHistory H F S Ub pay es)
    (κ : A ↪ Fin es.length) : (occurrenceBank es κ).Valid S.basal S.w S.g := by
  have hv := h.bank_valid
  refine ⟨fun i => hv.disj (κ i), ?_, fun i => hv.basalA (κ i),
    fun i => hv.basalT (κ i),fun i => hv.charge (κ i)⟩
  intro i j hij
  exact hv.pw (κ i) (κ j) (fun hh => hij (κ.injective hh))

theorem occurrence_total_subset {P : ℕ} (es : List (Entry V C P)) (κ : A ↪ Fin es.length) :
    (occurrenceBank es κ).total ⊆ usedEdges es := by
  intro e he
  obtain ⟨i,_,he⟩ := mem_biUnion.mp he
  exact total_subset_used (List.get_mem ..) he

theorem occurrence_cell_size {H : Host V I} {F : Set (Multiset I)} {S : MacroSetting V Q C}
    {Ub : ℕ} {pay : ℝ} {es : List (Entry V C S.P)} (h : ValidHistory H F S Ub pay es)
    (κ : A ↪ Fin es.length) (i : A) : ((occurrenceBank es κ).tot i).card ≤ S.E :=
  (h.good (es.get (κ i)) (List.get_mem ..)).good.2.2.2.2.2.1

theorem occurrence_card_le {P : ℕ} (es : List (Entry V C P)) (κ : A ↪ Fin es.length) :
    Fintype.card A ≤ es.length := by
  simpa only [Fintype.card_fin] using Fintype.card_le_of_injective κ κ.injective

theorem occurrence_degree_le {H : Host V I} {F : Set (Multiset I)} {S : MacroSetting V Q C}
    {Ub : ℕ} {pay : ℝ} {R0 : Finset (Finset V)} {N : ℕ} {es : List (Entry V C S.P)}
    (h : Seeded.RunInv H F S Ub pay R0 N es) (κ : A ↪ Fin es.length) (v : V) :
    deg (occurrenceBank es κ).total v < S.q+S.Bstar*S.E :=
  (deg_mono (occurrence_total_subset es κ) v).trans_lt (h.maxdeg v)

/-- Exact capacity in a slice of this list, without any canonical-run equality. -/
theorem slice_fiber_card {P : ℕ} (es : List (Entry V C P)) (p : ℕ → Prop)
    (s : Bool) (c : C) (a : Fin P) :
    ((sliceBank es p).fiber s c a).card =
      es.countP (fun e => decide (p e.round ∧ e.lab=(s,c,a))) := by
  rw [←card_filter_get]
  unfold Bank.fiber sliceBank occurrenceBank
  refine Finset.card_bij (fun i _ => i.1) ?_ ?_ ?_
  · intro i hi
    have hp := (mem_filter.mp hi).2
    exact mem_filter.mpr ⟨mem_univ _,by
      simp only [decide_eq_true_eq]
      exact ⟨i.2,Prod.ext hp.1 (Prod.ext hp.2.1 hp.2.2)⟩⟩
  · intro i _ j _ hij
    exact Subtype.ext hij
  · intro i hi
    have hh := (mem_filter.mp hi).2
    simp only [decide_eq_true_eq] at hh
    refine ⟨⟨i,hh.1⟩,mem_filter.mpr ⟨mem_univ _,?_⟩,rfl⟩
    change (es.get i).lab.1=s ∧ (es.get i).lab.2.1=c ∧ (es.get i).lab.2.2=a
    rw [hh.2]
    exact ⟨rfl,rfl,rfl⟩

theorem slice_supplies_of_counts {P : ℕ} (es : List (Entry V C P)) (p : ℕ → Prop)
    (z : Fin P → C → ℤ)
    (hz : ∀ a c, (z a c).natAbs ≤ es.countP (fun e =>
      decide (p e.round ∧ e.lab=(decide (0<z a c),c,a)))) :
    (sliceBank es p).Supplies z := by
  intro a c
  rw [slice_fiber_card]
  exact hz a c

theorem slice_totals_disjoint {H : Host V I} {F : Set (Multiset I)} {S : MacroSetting V Q C}
    {Ub : ℕ} {pay : ℝ} {es : List (Entry V C S.P)} (h : ValidHistory H F S Ub pay es)
    (p q : ℕ → Prop) (hpq : ∀ r, ¬ (p r ∧ q r)) :
    Disjoint (sliceBank es p).total (sliceBank es q).total := by
  rw [disjoint_left]
  intro e heP heQ
  obtain ⟨i,_,hi⟩ := mem_biUnion.mp heP
  obtain ⟨j,_,hj⟩ := mem_biUnion.mp heQ
  have hij : i.1 ≠ j.1 := by
    intro hh
    exact hpq (es.get i.1).round ⟨i.2,by simpa only [hh] using j.2⟩
  exact disjoint_left.mp (h.bank_valid.pw i.1 j.1 hij) hi hj

private theorem used_mem {P : ℕ} {es : List (Entry V C P)} {f : Sym2 V} :
    f∈usedEdges es ↔ ∃e∈es,f∈e.cell.tot := by
  induction es with
  | nil => simp [usedEdges]
  | cons a es ih => simp [usedEdges,ih]

theorem toBank_tot {P : ℕ} (es : List (Entry V C P)) (i : Fin es.length) :
    (toBank es).tot i=(es.get i).cell.tot := by
  ext f
  simp only [Bank.tot,toBank,Cell.tot,mem_union]

theorem toBank_total {P : ℕ} (es : List (Entry V C P)) : (toBank es).total=usedEdges es := by
  ext f
  constructor
  · intro hf
    obtain ⟨i,_,hi⟩ := mem_biUnion.mp hf
    rw [toBank_tot] at hi
    exact total_subset_used (List.get_mem ..) hi
  · intro hf
    obtain ⟨e,he,hf⟩ := used_mem.mp hf
    obtain ⟨i,hi⟩ := List.get_of_mem he
    exact mem_biUnion.mpr ⟨i,mem_univ _,by change f∈(es.get i).cell.tot; rwa [hi]⟩

def selectedPayload {P : ℕ} (es : List (Entry V C P)) (s : Finset (Fin es.length)) :
    Finset (Sym2 V) := s.biUnion (fun i => (es.get i).cell.Y)

def selectedCover {P : ℕ} (es : List (Entry V C P)) (s : Finset (Fin es.length)) :
    Finset (Sym2 V) := univ.biUnion (fun i => if i∈s then (es.get i).cell.A else (es.get i).cell.tot)

def selectedFamily {P : ℕ} (es : List (Entry V C P)) (s : Finset (Fin es.length)) :
    Finset (Finset V) := univ.biUnion (fun i => if i∈s then (es.get i).off else (es.get i).on)

private theorem off_subset {P : ℕ} {e : Entry V C P} {es : List (Entry V C P)}
    (he : e∈es) : e.off⊆offFamily es := by
  induction es with
  | nil => simp at he
  | cons a es ih =>
    rcases List.mem_cons.mp he with rfl | he
    · exact subset_union_left
    · exact (ih he).trans subset_union_right

private theorem on_subset {P : ℕ} {e : Entry V C P} {es : List (Entry V C P)}
    (he : e∈es) : e.on⊆onFamily es := by
  induction es with
  | nil => simp at he
  | cons a es ih =>
    rcases List.mem_cons.mp he with rfl | he
    · exact subset_union_left
    · exact (ih he).trans subset_union_right

theorem selectedFamily_subset {P : ℕ} (es : List (Entry V C P)) (s : Finset (Fin es.length)) :
    selectedFamily es s ⊆ modes es := by
  intro T hT
  obtain ⟨i,_,hi⟩ := mem_biUnion.mp hT
  split_ifs at hi with hs
  · exact mem_union_left _ (off_subset (List.get_mem ..) hi)
  · exact mem_union_right _ (on_subset (List.get_mem ..) hi)

private theorem decomposition_biUnion {J : Type*} (s : Finset J)
    {H : Host V I} {F : Set (Multiset I)}
    (E : J → Finset (Sym2 V)) (D : J → Finset (Finset V))
    (hE : ∀ i∈s,∀ j∈s,i≠j → Disjoint (E i) (E j))
    (hD : ∀ i∈s,IsDecomposition H F (E i) (D i)) :
    IsDecomposition H F (s.biUnion E) (s.biUnion D) := by
  have hSub : ∀ i∈s,∀ T∈D i,triEdges T⊆E i := fun i hi T hT => (hD i hi).subset hT
  refine ⟨?_,?_,?_⟩
  · intro T hT
    obtain ⟨i,hi,hT⟩ := mem_biUnion.mp hT
    exact (hD i hi).1 T hT
  · intro T hT U hU hne
    obtain ⟨i,hi,hT⟩ := mem_biUnion.mp hT
    obtain ⟨j,hj,hU⟩ := mem_biUnion.mp hU
    by_cases hij : i=j
    · subst j; exact (hD i hi).2.1 hT hU hne
    · exact (hE i hi j hj hij).mono (hSub i hi T hT) (hSub j hj U hU)
  · rw [biUnion_biUnion]
    exact biUnion_congr rfl (fun i hi => (hD i hi).2.2)

theorem selectedCover_decomposition {H : Host V I} {F : Set (Multiset I)} {S : MacroSetting V Q C}
    {Ub : ℕ} {pay : ℝ} {es : List (Entry V C S.P)} (h : ValidHistory H F S Ub pay es)
    (s : Finset (Fin es.length)) : IsDecomposition H F (selectedCover es s) (selectedFamily es s) := by
  apply decomposition_biUnion univ
  · intro i _ j _ hij
    apply (h.bank_valid.pw i j hij).mono
    · split_ifs
      · exact subset_union_left
      · exact subset_refl _
    · split_ifs
      · exact subset_union_left
      · exact subset_refl _
  · intro i _
    have hi := h.good (es.get i) (List.get_mem ..)
    split_ifs
    · exact hi.off
    · exact hi.on

theorem selected_partition {H : Host V I} {F : Set (Multiset I)} {S : MacroSetting V Q C}
    {Ub : ℕ} {pay : ℝ} {es : List (Entry V C S.P)} (h : ValidHistory H F S Ub pay es)
    (s : Finset (Fin es.length)) :
    usedEdges es=selectedCover es s∪selectedPayload es s ∧
      Disjoint (selectedCover es s) (selectedPayload es s) := by
  have hUsed := toBank_total es
  constructor
  · rw [←hUsed]
    ext e
    simp only [Bank.total,toBank_tot,selectedCover,selectedPayload,mem_union,mem_biUnion,mem_univ,true_and]
    constructor
    · rintro ⟨i,he⟩
      by_cases hi : i∈s
      · change e∈(es.get i).cell.A∪(es.get i).cell.Y at he
        rcases mem_union.mp he with he | he
        · exact Or.inl ⟨i,by simpa only [if_pos hi] using he⟩
        · exact Or.inr ⟨i,hi,he⟩
      · exact Or.inl ⟨i,by simpa only [if_neg hi] using he⟩
    · rintro (⟨i,he⟩ | ⟨i,_,he⟩)
      · refine ⟨i,?_⟩
        by_cases hi : i∈s
        · rw [if_pos hi] at he
          exact mem_union_left (es.get i).cell.Y he
        · rwa [if_neg hi] at he
      · exact ⟨i,mem_union_right _ he⟩
  · rw [disjoint_left]
    intro e heC heY
    obtain ⟨i,_,hi⟩ := mem_biUnion.mp heC
    obtain ⟨j,hj,heY⟩ := mem_biUnion.mp heY
    by_cases hij : i=j
    · subst j
      rw [if_pos hj] at hi
      exact disjoint_left.mp (h.bank_valid.disj i) hi heY
    · have hiTot : e∈(es.get i).cell.tot := by
        split_ifs at hi
        · exact mem_union_left _ hi
        · exact hi
      exact disjoint_left.mp (h.bank_valid.pw i j hij) hiTot (mem_union_right _ heY)

/-- The actual selected cover, including every unselected ON cell, has both budgets. -/
theorem selectedCover_two_budgets {H : Host V I} {F : Set (Multiset I)} {S : MacroSetting V Q C}
    {Ub : ℕ} {pay : ℝ} {R0 : Finset (Finset V)} {es : List (Entry V C S.P)}
    (h : Seeded.History H F S Ub pay R0 es) (s : Finset (Fin es.length)) :
    IsDecomposition H F (selectedCover es s) (selectedFamily es s) ∧
    selectedFamily es s ⊆ modes es ∧
    (count (selectedFamily es s):ℝ) ≤ es.length*pay ∧
    (count (R0∪selectedFamily es s):ℝ) ≤ count R0+es.length*pay := by
  have hSub := selectedFamily_subset es s
  have hc {D E : Finset (Finset V)} (hDE : D⊆E) : count D≤count E := by
    apply card_le_card
    intro P hP
    obtain ⟨hPD,hCard,hPasch⟩ := mem_configurations.mp hP
    exact mem_configurations.mpr ⟨hPD.trans hDE,hCard,hPasch⟩
  exact ⟨selectedCover_decomposition h.local_history s,hSub,
    (show (count (selectedFamily es s):ℝ)≤count (modes es) by exact_mod_cast hc hSub).trans h.local_history.budget,
    (show (count (R0∪selectedFamily es s):ℝ)≤count (R0∪modes es) by
      exact_mod_cast hc (union_subset_union (subset_refl R0) hSub)).trans h.external_budget⟩

theorem selectedCover_eq_activation {H : Host V I} {F : Set (Multiset I)} {S : MacroSetting V Q C}
    {Ub : ℕ} {pay : ℝ} {es : List (Entry V C S.P)} (h : ValidHistory H F S Ub pay es)
    (z : Fin S.P → C → ℤ) (hs : (toBank es).Supplies z) :
    selectedCover es (Bank.selJ hs)=Bank.cover hs := by
  have hp := selected_partition h (Bank.selJ hs)
  have heq : selectedCover es (Bank.selJ hs)=usedEdges es\selectedPayload es (Bank.selJ hs) := by
    ext f
    constructor
    · intro hf
      refine mem_sdiff.mpr ⟨?_,?_⟩
      · rw [hp.1]; exact mem_union_left _ hf
      · exact fun hY => disjoint_left.mp hp.2 hf hY
    · intro hf
      obtain ⟨hf,hNot⟩ := mem_sdiff.mp hf
      rw [hp.1] at hf
      exact (mem_union.mp hf).resolve_right hNot
  calc selectedCover es (Bank.selJ hs)=usedEdges es\selectedPayload es (Bank.selJ hs) := heq
    _ = (toBank es).total\Bank.payload hs := by rw [toBank_total]; rfl
    _ = Bank.cover hs := (Bank.cover_eq_sdiff hs h.bank_valid).symm

theorem selectedPayload_eq_activation {P : ℕ} (es : List (Entry V C P))
    (z : Fin P → C → ℤ) (hs : (toBank es).Supplies z) :
    selectedPayload es (Bank.selJ hs)=Bank.payload hs := rfl

end TypedTriangle.Pasch.RichBank.Actual
#print axioms TypedTriangle.Pasch.RichBank.Actual.occurrence_valid
#print axioms TypedTriangle.Pasch.RichBank.Actual.slice_fiber_card
#print axioms TypedTriangle.Pasch.RichBank.Actual.slice_supplies_of_counts
#print axioms TypedTriangle.Pasch.RichBank.Actual.slice_totals_disjoint
#print axioms TypedTriangle.Pasch.RichBank.Actual.toBank_total
#print axioms TypedTriangle.Pasch.RichBank.Actual.selectedCover_decomposition
#print axioms TypedTriangle.Pasch.RichBank.Actual.selected_partition
#print axioms TypedTriangle.Pasch.RichBank.Actual.selectedCover_two_budgets
#print axioms TypedTriangle.Pasch.RichBank.Actual.selectedCover_eq_activation
