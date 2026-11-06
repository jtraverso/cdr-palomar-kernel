module
public import RequestProject.TypedTriangle.PaschSeededBankRound
public import RequestProject.TypedTriangle.PaschRichBankRun
set_option maxHeartbeats 4000000 -- build option (original: -DmaxHeartbeats=1600000; raised)
set_option maxRecDepth 16384 -- build option (original: -DmaxRecDepth=8192; raised)
@[expose] public section
open Finset Classical
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1200000
namespace TypedTriangle.Pasch.RichBank.Seeded
open S07V40
variable {V I Q C : Type*} [Fintype V] [AddCommGroup Q] [Fintype C]

structure RunInv (H : Host V I) (F : Set (Multiset I)) (S : MacroSetting V Q C)
    (Ub : ℕ) (pay : ℝ) (R0 : Finset (Finset V)) (t : ℕ) (es : List (Entry V C S.P)) : Prop where
  history : History H F S Ub pay R0 es
  trace : Trace S t es
  maxdeg : ∀ v, deg (usedEdges es) v < S.q+S.Bstar*S.E
  edges : (usedEdges es).card ≤ S.E*S.Bstar*t
  length : es.length ≤ S.Bstar*t
  rounds : ∀ e ∈ es, e.round<t

/-- Same saturation threshold and cap as V40, with the rich choices retained.
The supplied cell witness is used directly in the induction. -/
theorem exists_run {H : Host V I} {F : Set (Multiset I)} {S : MacroSetting V Q C}
    {Ub : ℕ} {pay : ℝ} {R0 : Finset (Finset V)} (hSupply : CellSupply H F S Ub pay R0) (hq : 0 < S.q)
    (N : ℕ) (hcap : 2*S.E*S.Bstar*N ≤ S.q*S.zmax) :
    ∀ t ≤ N, ∃ es : List (Entry V C S.P), RunInv H F S Ub pay R0 t es := by
  intro t
  induction t with
  | zero =>
    intro ht
    refine ⟨[], empty_history H F S Ub pay R0, Trace.zero, ?_, ?_, ?_, ?_⟩
    · intro v
      simp only [usedEdges, deg, filter_empty, card_empty]
      omega
    · simp [usedEdges]
    · simp
    · simp
  | succ t ih =>
    intro ht
    obtain ⟨es, hInv⟩ := ih (by omega)
    let Z := satSet S.q (usedEdges es)
    by_cases hStop : S.K Z = ⊥
    · refine ⟨es, hInv.history, Trace.stop hInv.trace hStop, hInv.maxdeg, ?_, ?_, ?_⟩
      · exact hInv.edges.trans (Nat.mul_le_mul_left _ (Nat.le_succ t))
      · exact hInv.length.trans (Nat.mul_le_mul_left _ (Nat.le_succ t))
      · intro e he
        exact Nat.lt_succ_of_lt (hInv.rounds e he)
    · have hSmall : Z.card ≤ S.zmax := by
        have hh : S.q*Z.card ≤ S.q*S.zmax := calc
          S.q*Z.card ≤ 2*(usedEdges es).card := mul_card_satSet_le _ _
          _ ≤ 2*(S.E*S.Bstar*t) := Nat.mul_le_mul_left 2 hInv.edges
          _ = (2*S.E*S.Bstar)*t := by ring
          _ ≤ (2*S.E*S.Bstar)*N := Nat.mul_le_mul_left _ (by omega)
          _ ≤ S.q*S.zmax := hcap
        exact Nat.le_of_mul_le_mul_left hh hq
      have hLabels : (actList S Z).length ≤ S.Bstar := card_actList_le Z
      have hOut : ∀ v, v ∉ Z → deg (usedEdges es) v+(actList S Z).length*S.E < S.q+S.Bstar*S.E := by
        intro v hv
        have hqv : deg (usedEdges es) v < S.q := by
          have hh : ¬ S.q ≤ deg (usedEdges es) v := fun hh => hv (mem_satSet.mpr hh)
          omega
        have hm := Nat.mul_le_mul_right S.E hLabels
        omega
      obtain ⟨added, hHist, hLabs, hRounds, hOutFinal, hInFinal, hCard⟩ :=
        place_round hSupply Z hSmall t (actList S Z) es hInv.history
          (fun l hl => mem_actList.mp hl) hOut (fun v _ => hInv.maxdeg v)
      have hAddedLen : added.length ≤ S.Bstar := by
        have hh := congrArg List.length hLabs
        simp only [List.length_map, List.length_reverse] at hh
        exact hh.le.trans hLabels
      refine ⟨added++es, hHist, Trace.step hInv.trace hStop hLabs hRounds, ?_, ?_, ?_, ?_⟩
      · intro v
        by_cases hv : v ∈ Z
        · rw [hInFinal v hv]
          exact hInv.maxdeg v
        · exact (hOutFinal v hv).trans_lt (hOut v hv)
      · calc (usedEdges (added++es)).card ≤ (usedEdges es).card+(actList S Z).length*S.E := hCard
          _ ≤ S.E*S.Bstar*t+S.Bstar*S.E := Nat.add_le_add hInv.edges (Nat.mul_le_mul_right S.E hLabels)
          _ = S.E*S.Bstar*(t+1) := by ring
      · simp only [List.length_append]
        calc added.length+es.length ≤ S.Bstar+S.Bstar*t := Nat.add_le_add hAddedLen hInv.length
          _ = S.Bstar*(t+1) := by ring
      · intro e he
        rcases List.mem_append.mp he with he | he
        · rw [(hRounds e he).1]
          exact Nat.lt_succ_self t
        · exact Nat.lt_succ_of_lt (hInv.rounds e he)

/-- The old occurrence-bank validity is obtained from this actual rich run,
together with its fixed mode universe and its proved linear cell budget. -/
theorem exists_valid_bank_with_budget {H : Host V I} {F : Set (Multiset I)}
    {S : MacroSetting V Q C} {Ub : ℕ} {pay : ℝ} {R0 : Finset (Finset V)}
    (hSupply : CellSupply H F S Ub pay R0) (hq : 0 < S.q) (hPay : 0 ≤ pay)
    (N : ℕ) (hcap : 2*S.E*S.Bstar*N ≤ S.q*S.zmax) :
    ∃ es : List (Entry V C S.P), RunInv H F S Ub pay R0 N es ∧
      (toBank es).Valid S.basal S.w S.g ∧ PairCodegreeBound (modes es) 2 ∧
      (count (modes es):ℝ) ≤ ((S.Bstar*N:ℕ):ℝ)*pay ∧
      (count (R0∪modes es):ℝ) ≤ count R0+((S.Bstar*N:ℕ):ℝ)*pay := by
  obtain ⟨es, hInv⟩ := exists_run hSupply hq N hcap N le_rfl
  refine ⟨es, hInv, hInv.history.local_history.bank_valid, hInv.history.codegree, ?_, ?_⟩
  · exact hInv.history.local_history.budget.trans
      (mul_le_mul_of_nonneg_right (by exact_mod_cast hInv.length) hPay)
  · have hh := mul_le_mul_of_nonneg_right (show (es.length:ℝ) ≤ (S.Bstar*N:ℕ) by exact_mod_cast hInv.length) hPay
    have hAdd : (count R0:ℝ)+es.length*pay ≤ count R0+((S.Bstar*N:ℕ):ℝ)*pay := by
      linarith only [hh]
    exact hInv.history.external_budget.trans hAdd

end TypedTriangle.Pasch.RichBank.Seeded
#print axioms TypedTriangle.Pasch.RichBank.Seeded.exists_run
#print axioms TypedTriangle.Pasch.RichBank.Seeded.exists_valid_bank_with_budget
