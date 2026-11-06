module
public import RequestProject.TypedTriangle.PaschNativeCatalogCell
public import RequestProject.S07V43.Activation
set_option maxHeartbeats 4000000 -- build option (original: -DmaxHeartbeats=1600000; raised)
set_option maxRecDepth 16384 -- build option (original: -DmaxRecDepth=8192; raised)
@[expose] public section
open Finset Classical
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1200000
namespace TypedTriangle.Pasch.RichBank
open S07V40
variable {V I Q C : Type*} [Fintype V] [AddCommGroup Q] [Fintype C] {P : ℕ}

/-- Actual chosen data. Histories are stored in reverse chronological order. -/
structure Entry (V C : Type*) (P : ℕ) where
  round : ℕ
  lab : Lab C P
  cell : Cell V
  anchors : Finset V
  off : Finset (Finset V)
  on : Finset (Finset V)
  previous : Finset (Finset V)
  used : Finset (Sym2 V)
  deleted : Finset V

def usedEdges : List (Entry V C P) → Finset (Sym2 V)
  | [] => ∅
  | e :: es => e.cell.tot ∪ usedEdges es

def offEdges : List (Entry V C P) → Finset (Sym2 V)
  | [] => ∅
  | e :: es => e.cell.A ∪ offEdges es

def offFamily : List (Entry V C P) → Finset (Finset V)
  | [] => ∅
  | e :: es => e.off ∪ offFamily es

def onFamily : List (Entry V C P) → Finset (Finset V)
  | [] => ∅
  | e :: es => e.on ∪ onFamily es

def modes (es : List (Entry V C P)) := offFamily es ∪ onFamily es

structure GoodEntry (H : Host V I) (F : Set (Multiset I)) (S : MacroSetting V Q C)
    (Ub : ℕ) (pay : ℝ) (e : Entry V C S.P) : Prop where
  good : GoodCell S e.used e.deleted e.lab e.cell
  off : IsDecomposition H F e.cell.A e.off
  on : IsDecomposition H F e.cell.tot e.on
  fresh : Fresh e.anchors e.cell.A
  inside : Inside e.anchors e.cell.Y
  avoids : Disjoint e.anchors e.deleted
  support : (e.anchors ∪ support e.cell.A).card ≤ Ub
  potential : (supportIncrementCost e.previous e.anchors (TypedTriangle.support e.cell.A):ℝ) ≤ pay
  increment : (count ((e.off ∪ e.on) ∪ e.previous):ℝ) ≤ count e.previous + pay

structure ValidHistory (H : Host V I) (F : Set (Multiset I)) (S : MacroSetting V Q C)
    (Ub : ℕ) (pay : ℝ) (es : List (Entry V C S.P)) : Prop where
  good : ∀ e ∈ es, GoodEntry H F S Ub pay e
  disjoint : es.Pairwise (fun e f => Disjoint e.cell.tot f.cell.tot)
  off : IsDecomposition H F (offEdges es) (offFamily es)
  on : IsDecomposition H F (usedEdges es) (onFamily es)
  budget : (count (modes es):ℝ) ≤ es.length * pay

lemma offEdges_subset_used (es : List (Entry V C P)) : offEdges es ⊆ usedEdges es := by
  induction es with
  | nil => exact subset_rfl
  | cons e es ih => exact union_subset_union subset_union_left ih

lemma total_subset_used {e : Entry V C P} {es : List (Entry V C P)} (he : e ∈ es) :
    e.cell.tot ⊆ usedEdges es := by
  induction es with
  | nil => simp at he
  | cons f es ih =>
    rcases List.mem_cons.mp he with rfl | he
    · exact subset_union_left
    · exact (ih he).trans subset_union_right

theorem empty_history (H : Host V I) (F : Set (Multiset I)) (S : MacroSetting V Q C)
    (Ub : ℕ) (pay : ℝ) : ValidHistory H F S Ub pay [] := by
  refine ⟨by simp, by simp, ?_, ?_, ?_⟩
  · exact ⟨by simp [offFamily], by simp [offFamily], by simp [offFamily, offEdges]⟩
  · exact ⟨by simp [onFamily], by simp [onFamily], by simp [onFamily, usedEdges]⟩
  · simp [modes, offFamily, onFamily, count, statistic, configurations]

theorem ValidHistory.codegree {H : Host V I} {F : Set (Multiset I)} {S : MacroSetting V Q C}
    {Ub : ℕ} {pay : ℝ} {es : List (Entry V C S.P)} (h : ValidHistory H F S Ub pay es) :
    PairCodegreeBound (modes es) 2 :=
  pairCodegreeBound_two_modes ⟨h.off.1, h.off.2.1⟩ ⟨h.on.1, h.on.2.1⟩

theorem ValidHistory.modes_edges {H : Host V I} {F : Set (Multiset I)} {S : MacroSetting V Q C}
    {Ub : ℕ} {pay : ℝ} {es : List (Entry V C S.P)} (h : ValidHistory H F S Ub pay es) :
    ∀ T ∈ modes es, triEdges T ⊆ usedEdges es := by
  intro T hT
  rcases mem_union.mp hT with hT | hT
  · exact (h.off.subset hT).trans (offEdges_subset_used es)
  · exact h.on.subset hT

/-- Insert the already chosen rich witness. No projection followed by another
choice of a cell or decomposition occurs. The two global mode families remain
packings, hence their union has codegree two independently of the cell count. -/
theorem ValidHistory.cons {H : Host V I} {F : Set (Multiset I)} {S : MacroSetting V Q C}
    {Ub : ℕ} {pay : ℝ} {es : List (Entry V C S.P)} (h : ValidHistory H F S Ub pay es)
    (e : Entry V C S.P) (he : GoodEntry H F S Ub pay e)
    (hUsed : e.used = usedEdges es) (hPrev : e.previous = modes es) :
    ValidHistory H F S Ub pay (e :: es) := by
  have hDis : Disjoint e.cell.tot (usedEdges es) := by
    simpa only [hUsed] using he.good.2.2.2.1
  have hOffDis : Disjoint e.cell.A (offEdges es) :=
    hDis.mono subset_union_left (offEdges_subset_used es)
  have hModes : modes (e::es) = (e.off ∪ e.on) ∪ modes es := by
    change (e.off ∪ offFamily es) ∪ (e.on ∪ onFamily es) =
      (e.off ∪ e.on) ∪ (offFamily es ∪ onFamily es)
    ac_rfl
  refine ⟨?_, List.Pairwise.cons (fun f hf => hDis.mono_right (total_subset_used hf)) h.disjoint,
    he.off.union h.off hOffDis, he.on.union h.on hDis, ?_⟩
  · intro f hf
    rcases List.mem_cons.mp hf with rfl | hf
    · exact he
    · exact h.good f hf
  · rw [hModes]
    have hStep := he.increment
    rw [hPrev] at hStep
    have hOld := h.budget
    simp only [List.length_cons, Nat.cast_add, Nat.cast_one]
    nlinarith only [hStep, hOld]

/-- Projection to the ordinary occurrence-bank contract is performed only
after the rich history and its fixed modes have been constructed. -/
def toBank (es : List (Entry V C P)) : S07V43.Bank V (Fin es.length) C P where
  sgn i := (es.get i).lab.1
  cat i := (es.get i).lab.2.1
  col i := (es.get i).lab.2.2
  A i := (es.get i).cell.A
  Y i := (es.get i).cell.Y

theorem ValidHistory.bank_valid {H : Host V I} {F : Set (Multiset I)} {S : MacroSetting V Q C}
    {Ub : ℕ} {pay : ℝ} {es : List (Entry V C S.P)} (h : ValidHistory H F S Ub pay es) :
    (toBank es).Valid S.basal S.w S.g := by
  have hg (i : Fin es.length) := (h.good (es.get i) (List.get_mem ..)).good
  refine ⟨fun i => (hg i).1, ?_, fun i => (hg i).2.1, fun i => (hg i).2.2.1,
    fun i => (hg i).2.2.2.2.2.2⟩
  intro i j hij
  have hpw := List.pairwise_iff_get.mp h.disjoint
  rcases lt_or_gt_of_ne hij with hij | hij
  · exact hpw i j hij
  · exact (hpw j i hij).symm

#print axioms empty_history
#print axioms ValidHistory.codegree
#print axioms ValidHistory.modes_edges
#print axioms ValidHistory.cons
#print axioms ValidHistory.bank_valid
end TypedTriangle.Pasch.RichBank
