module
public import RequestProject.TypedTriangle.PaschActualBankOccurrences
set_option maxHeartbeats 4000000 -- build option (original: -DmaxHeartbeats=1600000; raised)
set_option maxRecDepth 16384 -- build option (original: -DmaxRecDepth=8192; raised)
@[expose] public section
open Finset Classical
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1200000
namespace TypedTriangle.Pasch.RichBank.Actual
open S07V40
variable {V I Q C : Type*} [Fintype V] [AddCommGroup Q] [Fintype C]

def roundPrefix {P : ℕ} (es : List (Entry V C P)) (r : ℕ) :=
  es.filter (fun e => decide (e.round<r))

def saturatedPrefix (S : MacroSetting V Q C) (es : List (Entry V C S.P)) (r : ℕ) :=
  satSet S.q (usedEdges (roundPrefix es r))

theorem trace_rounds_lt {S : MacroSetting V Q C} {N : ℕ} {es : List (Entry V C S.P)}
    (h : Trace S N es) : ∀ e∈es,e.round<N := by
  induction h with
  | zero => simp
  | stop h hStop ih => intro e he; exact Nat.lt_succ_of_lt (ih e he)
  | step h hAct hLabs hRounds ih =>
    intro e he
    rcases List.mem_append.mp he with he | he
    · rw [(hRounds e he).1]; omega
    · exact Nat.lt_succ_of_lt (ih e he)

theorem prefix_eq_self {P : ℕ} {es : List (Entry V C P)} {r : ℕ}
    (h : ∀ e∈es,e.round<r) : roundPrefix es r=es := by
  apply List.filter_eq_self.mpr
  intro e he
  simpa only [decide_eq_true_eq] using h e he

theorem prefix_append_early {P : ℕ} (added es : List (Entry V C P)) (t r : ℕ)
    (hr : r≤t) (hRounds : ∀ e∈added,e.round=t) : roundPrefix (added++es) r=roundPrefix es r := by
  have hEmpty : added.filter (fun e => decide (e.round<r))=[] := by
    apply List.filter_eq_nil_iff.mpr
    intro e he
    simp only [decide_eq_true_eq]
    have hh := hRounds e he
    omega
  unfold roundPrefix
  rw [List.filter_append,hEmpty,List.nil_append]

private theorem count_round_zero {P : ℕ} {es : List (Entry V C P)} {r t : ℕ}
    (hRounds : ∀ e∈es,e.round<t) (hrt : t≤r) (l : Lab C P) :
    es.countP (fun e => decide (e.round=r ∧ e.lab=l))=0 := by
  apply List.countP_eq_zero.mpr
  intro e he
  simp only [decide_eq_true_eq,not_and]
  intro hr
  have hh := hRounds e he
  omega

private theorem count_added {S : MacroSetting V Q C} {added : List (Entry V C S.P)}
    (Z : Finset V) (t r : ℕ) (l : Lab C S.P)
    (hLabs : added.map Entry.lab=(actList S Z).reverse)
    (hRounds : ∀ e∈added,e.round=t) :
    added.countP (fun e => decide (e.round=r ∧ e.lab=l)) =
      if t=r then (if S.g l.2.1∈S.K Z then 1 else 0) else 0 := by
  have hLabelsCount : added.countP (fun e => decide (e.lab=l))=(actList S Z).count l := by
    calc _ = (added.map Entry.lab).count l := by
            rw [List.count_eq_countP,List.countP_map]
            apply List.countP_congr
            intro e _
            simp only [Function.comp_apply,decide_eq_true_eq,beq_iff_eq]
         _ = _ := by rw [hLabs,List.count_reverse]
  have hc : (actList S Z).count l=if S.g l.2.1∈S.K Z then 1 else 0 := by
    have hnd : (actList S Z).Nodup := Finset.nodup_toList _
    split_ifs with hg
    · exact List.count_eq_one_of_mem hnd (mem_actList.mpr hg)
    · exact List.count_eq_zero_of_not_mem (fun hm => hg (mem_actList.mp hm))
  by_cases htr : t=r
  · subst r
    rw [if_pos rfl,←hc,←hLabelsCount]
    apply List.countP_congr
    intro e he
    simp only [(hRounds e he),true_and]
  · rw [if_neg htr]
    apply List.countP_eq_zero.mpr
    intro e he
    simp only [decide_eq_true_eq,not_and]
    intro heq
    exact (htr ((hRounds e he).symm.trans heq)).elim

/-- The exact one-per-active-label count belongs to this rich run's own roundPrefix. -/
theorem trace_round_exact {S : MacroSetting V Q C} {N : ℕ} {es : List (Entry V C S.P)}
    (h : Trace S N es) (r : ℕ) (l : Lab C S.P) :
    es.countP (fun e => decide (e.round=r ∧ e.lab=l)) =
      if r<N ∧ S.K (saturatedPrefix S es r)≠⊥ ∧ S.g l.2.1∈S.K (saturatedPrefix S es r)
      then 1 else 0 := by
  induction h with
  | zero => simp
  | @stop t es h hStop ih =>
    by_cases hr : r<t
    · simpa only [hr,Nat.lt_succ_of_lt hr,true_and] using ih
    · have hc := count_round_zero (trace_rounds_lt h) (by omega : t≤r) l
      rw [hc]
      by_cases hrt : r=t
      · subst r
        have hp := prefix_eq_self (trace_rounds_lt h)
        simp only [saturatedPrefix,hp,hStop,ne_eq,not_true_eq_false,false_and,and_false,if_false]
      · simp only [show ¬ r<t+1 by omega,false_and,if_false]
  | @step t es added h hAct hLabs hRounds ih =>
    rw [List.countP_append,count_added _ t r l hLabs (fun e he => (hRounds e he).1)]
    by_cases hr : r<t
    · have hPre := prefix_append_early added es t r (by omega) (fun e he => (hRounds e he).1)
      have hZ : saturatedPrefix S (added++es) r=saturatedPrefix S es r := by dsimp only [saturatedPrefix]; rw [hPre]
      rw [hZ,if_neg (by omega : t≠r),zero_add,ih]
      simp only [hr,Nat.lt_succ_of_lt hr,true_and]
    · by_cases hrt : r=t
      · subst r
        have hPre := prefix_append_early added es t t le_rfl (fun e he => (hRounds e he).1)
        have hSelf := prefix_eq_self (trace_rounds_lt h)
        have hZ : saturatedPrefix S (added++es) t=satSet S.q (usedEdges es) := by
          rw [saturatedPrefix,hPre,hSelf]
        rw [hZ,if_pos rfl,count_round_zero (trace_rounds_lt h) le_rfl l,add_zero]
        simp only [Nat.lt_succ_self,true_and]
        by_cases hg : S.g l.2.1∈S.K (satSet S.q (usedEdges es))
        · rw [_root_.if_pos hg,_root_.if_pos ⟨hAct,hg⟩]
        · rw [_root_.if_neg hg,_root_.if_neg (fun hh => hg hh.2)]
      · have hrBig : t+1≤r := by omega
        have hZero := count_round_zero (trace_rounds_lt h) (by omega : t≤r) l
        rw [if_neg (by omega : t≠r),hZero]
        simp only [zero_add,show ¬ r<t+1 by omega,false_and,if_false]

/-- Each stored deletion snapshot is the actual roundPrefix at its stored round. -/
theorem trace_deleted_prefix {S : MacroSetting V Q C} {N : ℕ} {es : List (Entry V C S.P)}
    (h : Trace S N es) : ∀ e∈es,e.deleted=saturatedPrefix S es e.round := by
  induction h with
  | zero => simp
  | stop h hStop ih => exact ih
  | @step t es added h hAct hLabs hRounds ih =>
    intro e he
    rcases List.mem_append.mp he with he | he
    · obtain ⟨hr,hz⟩ := hRounds e he
      rw [hr,saturatedPrefix,prefix_append_early added es t t le_rfl
        (fun e he => (hRounds e he).1),prefix_eq_self (trace_rounds_lt h)]
      exact hz
    · rw [ih e he]
      change satSet S.q (usedEdges (roundPrefix es e.round))=
        satSet S.q (usedEdges (roundPrefix (added++es) e.round))
      rw [prefix_append_early added es t e.round (trace_rounds_lt h e he).le
        (fun e he => (hRounds e he).1)]


private theorem mem_used_edges {P : ℕ} {es : List (Entry V C P)} {f : Sym2 V} :
    f∈usedEdges es ↔ ∃e∈es,f∈e.cell.tot := by
  induction es with
  | nil => simp [usedEdges]
  | cons a es ih => simp [usedEdges,ih]

theorem prefix_edges_mono {P : ℕ} (es : List (Entry V C P)) {r s : ℕ} (hrs : r≤ s) :
    usedEdges (roundPrefix es r)⊆usedEdges (roundPrefix es s) := by
  intro f hf
  obtain ⟨e,he,hf⟩ := mem_used_edges.mp hf
  simp only [roundPrefix,List.mem_filter,decide_eq_true_eq] at he
  exact mem_used_edges.mpr ⟨e,by
    simp only [roundPrefix,List.mem_filter,decide_eq_true_eq]
    exact ⟨he.1,lt_of_lt_of_le he.2 hrs⟩,hf⟩

theorem saturatedPrefix_mono (S : MacroSetting V Q C) (es : List (Entry V C S.P)) :
    Monotone (saturatedPrefix S es) := by
  intro r s hrs
  exact satSet_mono S.q (prefix_edges_mono es hrs)

theorem trace_prefix_length {S : MacroSetting V Q C} {N : ℕ} {es : List (Entry V C S.P)}
    (h : Trace S N es) : ∀ r≤N,(roundPrefix es r).length≤S.Bstar*r := by
  induction h with
  | zero =>
    intro r hr
    have h0 : r=0 := by omega
    subst r
    simp [roundPrefix]
  | @stop t es h hStop ih =>
    intro r hr
    by_cases hrt : r≤t
    · exact ih r hrt
    · have heq : r=t+1 := by omega
      subst r
      have hOld := ih t le_rfl
      rw [prefix_eq_self (trace_rounds_lt h)] at hOld
      rw [prefix_eq_self (fun e he => Nat.lt_succ_of_lt (trace_rounds_lt h e he))]
      exact hOld.trans (Nat.mul_le_mul_left _ (Nat.le_succ t))
  | @step t es added h hAct hLabs hRounds ih =>
    intro r hr
    by_cases hrt : r≤t
    · rw [prefix_append_early added es t r hrt (fun e he => (hRounds e he).1)]
      exact ih r hrt
    · have heq : r=t+1 := by omega
      subst r
      have hOld := ih t le_rfl
      rw [prefix_eq_self (trace_rounds_lt h)] at hOld
      have hAdded : added.length≤S.Bstar := by
        have hh := congrArg List.length hLabs
        simp only [List.length_map,List.length_reverse] at hh
        exact hh.le.trans (card_actList_le _)
      have hAll : ∀ e∈added++es,e.round<t+1 := by
        intro e he
        rcases List.mem_append.mp he with he | he
        · rw [(hRounds e he).1]; omega
        · exact Nat.lt_succ_of_lt (trace_rounds_lt h e he)
      rw [prefix_eq_self hAll,List.length_append]
      calc added.length+es.length ≤ S.Bstar+S.Bstar*t := Nat.add_le_add hAdded hOld
        _ = S.Bstar*(t+1) := by ring

private theorem used_card_le {P : ℕ} (E : ℕ) (es : List (Entry V C P))
    (hE : ∀ e∈es,e.cell.tot.card≤E) : (usedEdges es).card≤E*es.length := by
  induction es with
  | nil => simp [usedEdges]
  | cons e es ih =>
    have hh := card_union_le e.cell.tot (usedEdges es)
    have h0 := hE e (List.mem_cons_self ..)
    have h1 := ih (fun e he => hE e (List.mem_cons_of_mem _ he))
    change (e.cell.tot∪usedEdges es).card≤E*(es.length+1)
    calc _ ≤ E+E*es.length := hh.trans (Nat.add_le_add h0 h1)
      _ = _ := by ring

/-- The roundPrefix cap has the same constants and scale as the original run. -/
theorem saturatedPrefix_bound {H : Host V I} {F : Set (Multiset I)} {S : MacroSetting V Q C}
    {Ub : ℕ} {pay : ℝ} {R0 : Finset (Finset V)} {N : ℕ} {es : List (Entry V C S.P)}
    (h : Seeded.RunInv H F S Ub pay R0 N es) (r : ℕ) (hr : r≤N) :
    S.q*(saturatedPrefix S es r).card≤2*S.E*S.Bstar*r := by
  have hSize : (usedEdges (roundPrefix es r)).card≤S.E*(roundPrefix es r).length := by
    apply used_card_le
    intro e he
    have hm : e∈es := (List.mem_filter.mp he).1
    exact (h.history.local_history.good e hm).good.2.2.2.2.2.1
  calc S.q*(saturatedPrefix S es r).card ≤ 2*(usedEdges (roundPrefix es r)).card :=
        mul_card_satSet_le _ _
    _ ≤ 2*(S.E*(roundPrefix es r).length) := Nat.mul_le_mul_left _ hSize
    _ ≤ 2*(S.E*(S.Bstar*r)) := Nat.mul_le_mul_left _
        (Nat.mul_le_mul_left _ (trace_prefix_length h.trace r hr))
    _ = _ := by ring

theorem saturatedPrefix_small {H : Host V I} {F : Set (Multiset I)} {S : MacroSetting V Q C}
    {Ub : ℕ} {pay : ℝ} {R0 : Finset (Finset V)} {N : ℕ} {es : List (Entry V C S.P)}
    (h : Seeded.RunInv H F S Ub pay R0 N es) (hq : 0<S.q)
    (hcap : 2*S.E*S.Bstar*N≤S.q*S.zmax) (r : ℕ) (hr : r≤N) :
    (saturatedPrefix S es r).card≤S.zmax := by
  have hh := (saturatedPrefix_bound h r hr).trans
    ((Nat.mul_le_mul_left (2*S.E*S.Bstar) hr).trans hcap)
  exact Nat.le_of_mul_le_mul_left hh hq


/-- Once a trace stops it cannot restart: activity at a later roundPrefix implies
activity at every earlier roundPrefix, including in settings with no K monotonicity field. -/
theorem trace_active_of_le {S : MacroSetting V Q C} {N : ℕ} {es : List (Entry V C S.P)}
    (h : Trace S N es) : ∀ (r s : ℕ), r≤ s → s≤N →
      S.K (saturatedPrefix S es s)≠⊥ → S.K (saturatedPrefix S es r)≠⊥ := by
  induction h with
  | zero =>
    intro r s hrs hs ha
    have hr : r=0 := by omega
    have h0 : s=0 := by omega
    subst r; subst s; exact ha
  | @stop t es h hStop ih =>
    intro r s hrs hs ha
    by_cases hst : s≤t
    · exact ih r s hrs hst ha
    · have hst' : s=t+1 := by omega
      subst s
      have hp := prefix_eq_self (fun e he => Nat.lt_succ_of_lt (trace_rounds_lt h e he))
      have hb : S.K (saturatedPrefix S es (t+1))=⊥ := by
        simpa only [saturatedPrefix,hp] using hStop
      exact (ha hb).elim
  | @step t es added h hAct hLabs hRounds ih =>
    intro r s hrs hs ha
    have hp (k : ℕ) (hk : k≤t) :
        saturatedPrefix S (added++es) k=saturatedPrefix S es k := by
      dsimp only [saturatedPrefix]
      rw [prefix_append_early added es t k hk (fun e he => (hRounds e he).1)]
    by_cases hst : s≤t
    · rw [hp s hst] at ha
      rw [hp r (hrs.trans hst)]
      exact ih r s hrs hst ha
    · have hsEq : s=t+1 := by omega
      by_cases hrt : r≤t
      · rw [hp r hrt]
        apply ih r t hrt le_rfl
        simpa only [saturatedPrefix,prefix_eq_self (trace_rounds_lt h)] using hAct
      · have hrEq : r=s := by omega
        simpa only [hrEq] using ha

end TypedTriangle.Pasch.RichBank.Actual
#print axioms TypedTriangle.Pasch.RichBank.Actual.trace_rounds_lt
#print axioms TypedTriangle.Pasch.RichBank.Actual.trace_round_exact
#print axioms TypedTriangle.Pasch.RichBank.Actual.trace_deleted_prefix
#print axioms TypedTriangle.Pasch.RichBank.Actual.trace_prefix_length
#print axioms TypedTriangle.Pasch.RichBank.Actual.saturatedPrefix_mono
#print axioms TypedTriangle.Pasch.RichBank.Actual.saturatedPrefix_bound
#print axioms TypedTriangle.Pasch.RichBank.Actual.saturatedPrefix_small
#print axioms TypedTriangle.Pasch.RichBank.Actual.trace_active_of_le
