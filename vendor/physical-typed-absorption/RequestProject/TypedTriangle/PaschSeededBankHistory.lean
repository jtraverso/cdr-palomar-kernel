module
public import RequestProject.TypedTriangle.PaschRichBankActivation
public import RequestProject.TypedTriangle.PaschSeededPotential
set_option maxHeartbeats 4000000 -- build option (original: -DmaxHeartbeats=1600000; raised)
set_option maxRecDepth 16384 -- build option (original: -DmaxRecDepth=8192; raised)
@[expose] public section
open Finset Classical
noncomputable section
set_option autoImplicit false
namespace TypedTriangle.Pasch.RichBank.Seeded
open S07V40
variable {V I Q C : Type*} [Fintype V] [AddCommGroup Q] [Fintype C]

/-- One actual choice carries two certificates. The local certificate does
not contain the number of configurations already present in the seed. -/
structure GoodEntry (H : Host V I) (F : Set (Multiset I)) (S : MacroSetting V Q C)
    (Ub : ℕ) (pay : ℝ) (R0 : Finset (Finset V)) (e : Entry V C S.P) : Prop where
  local_good : RichBank.GoodEntry H F S Ub pay e
  external_potential :
    (supportIncrementCost (R0∪e.previous) e.anchors (support e.cell.A):ℝ) ≤ pay
  external_increment :
    (count ((e.off∪e.on)∪(R0∪e.previous)):ℝ) ≤ count (R0∪e.previous)+pay

structure History (H : Host V I) (F : Set (Multiset I)) (S : MacroSetting V Q C)
    (Ub : ℕ) (pay : ℝ) (R0 : Finset (Finset V)) (es : List (Entry V C S.P)) : Prop where
  local_history : ValidHistory H F S Ub pay es
  good : ∀ e ∈ es, GoodEntry H F S Ub pay R0 e
  external_budget : (count (R0∪modes es):ℝ) ≤ count R0+es.length*pay

theorem empty_history (H : Host V I) (F : Set (Multiset I)) (S : MacroSetting V Q C)
    (Ub : ℕ) (pay : ℝ) (R0 : Finset (Finset V)) : History H F S Ub pay R0 [] := by
  refine ⟨RichBank.empty_history H F S Ub pay, by simp, ?_⟩
  simp [modes, offFamily, onFamily]

theorem History.codegree {H : Host V I} {F : Set (Multiset I)} {S : MacroSetting V Q C}
    {Ub : ℕ} {pay : ℝ} {R0 : Finset (Finset V)} {es : List (Entry V C S.P)}
    (h : History H F S Ub pay R0 es) : PairCodegreeBound (modes es) 2 := h.local_history.codegree

theorem History.external_codegree {H : Host V I} {F : Set (Multiset I)} {S : MacroSetting V Q C}
    {Ub L0 : ℕ} {pay : ℝ} {R0 : Finset (Finset V)} {es : List (Entry V C S.P)}
    (h : History H F S Ub pay R0 es) (hR0 : PairCodegreeBound R0 L0) :
    PairCodegreeBound (R0∪modes es) (L0+2) := hR0.union h.local_history.codegree

theorem History.modes_edges {H : Host V I} {F : Set (Multiset I)} {S : MacroSetting V Q C}
    {Ub : ℕ} {pay : ℝ} {R0 : Finset (Finset V)} {es : List (Entry V C S.P)}
    (h : History H F S Ub pay R0 es) : ∀ T ∈ modes es, triEdges T ⊆ usedEdges es :=
  h.local_history.modes_edges

theorem History.cons {H : Host V I} {F : Set (Multiset I)} {S : MacroSetting V Q C}
    {Ub : ℕ} {pay : ℝ} {R0 : Finset (Finset V)} {es : List (Entry V C S.P)}
    (h : History H F S Ub pay R0 es) (e : Entry V C S.P)
    (he : GoodEntry H F S Ub pay R0 e)
    (hUsed : e.used=usedEdges es) (hPrev : e.previous=modes es) :
    History H F S Ub pay R0 (e::es) := by
  have hModes : R0∪modes (e::es) = (e.off∪e.on)∪(R0∪modes es) := by
    change R0∪((e.off∪offFamily es)∪(e.on∪onFamily es)) =
      (e.off∪e.on)∪(R0∪(offFamily es∪onFamily es))
    ac_rfl
  refine ⟨h.local_history.cons e he.local_good hUsed hPrev, ?_, ?_⟩
  · intro f hf
    rcases List.mem_cons.mp hf with rfl | hf
    · exact he
    · exact h.good f hf
  · rw [hModes]
    have hStep := he.external_increment
    rw [hPrev] at hStep
    have hOld := h.external_budget
    simp only [List.length_cons, Nat.cast_add, Nat.cast_one]
    nlinarith only [hStep, hOld]

/-- The SAME activated decomposition has a local bound and a separate external
bound. The seed count occurs only in the latter. -/
theorem fixed_cover_decomposition {H : Host V I} {F : Set (Multiset I)}
    {S : MacroSetting V Q C} {Ub : ℕ} {pay : ℝ} {R0 : Finset (Finset V)}
    {es : List (Entry V C S.P)} (h : History H F S Ub pay R0 es)
    (z : Fin S.P → C → ℤ) (hs : (toBank es).Supplies z) :
    ∃ D, IsDecomposition H F (S07V43.Bank.cover hs) D ∧ D ⊆ modes es ∧
      (count D:ℝ) ≤ es.length*pay ∧ (count (R0∪D):ℝ) ≤ count R0+es.length*pay := by
  obtain ⟨D, hD, hSub, hLocal⟩ := RichBank.fixed_cover_decomposition h.local_history z hs
  have hCount : count (R0∪D) ≤ count (R0∪modes es) := by
    apply card_le_card
    intro K hK
    obtain ⟨hKS, hCard, hPasch⟩ := mem_configurations.mp hK
    exact mem_configurations.mpr
      ⟨hKS.trans (union_subset_union (subset_refl R0) hSub), hCard, hPasch⟩
  exact ⟨D, hD, hSub, hLocal,
    (show (count (R0∪D):ℝ) ≤ count (R0∪modes es) by exact_mod_cast hCount).trans h.external_budget⟩

end TypedTriangle.Pasch.RichBank.Seeded
#print axioms TypedTriangle.Pasch.RichBank.Seeded.empty_history
#print axioms TypedTriangle.Pasch.RichBank.Seeded.History.external_codegree
#print axioms TypedTriangle.Pasch.RichBank.Seeded.History.cons
#print axioms TypedTriangle.Pasch.RichBank.Seeded.fixed_cover_decomposition
