module
public import RequestProject.TypedTriangle.PaschActualBankRounds
set_option maxHeartbeats 4000000 -- build option (original: -DmaxHeartbeats=1600000; raised)
set_option maxRecDepth 16384 -- build option (original: -DmaxRecDepth=8192; raised)
@[expose] public section
open Finset Classical
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 600000
namespace TypedTriangle.Pasch.RichBank.Actual
open S07V40 S07V43
variable {V I Q C : Type*} [Fintype V] [AddCommGroup Q] [Fintype C]
variable (S : MacroSetting V Q C) (es : List (Entry V C S.P))

def numRounds (N : ℕ) : ℕ := ((range N).filter (fun r => S.K (saturatedPrefix S es r) ≠ ⊥)).card

def sidx (r : ℕ) : ℕ := ((range r).filter (fun s =>
  S.K (saturatedPrefix S es (s+1)) ≠ S.K (saturatedPrefix S es s))).card

def mStrat (N j : ℕ) : ℕ := ((range (numRounds S es N)).filter (fun r => sidx S es r=j)).card

def preStrat (N j : ℕ) : ℕ := ∑i ∈ range j,mStrat S es N i

def Zstrat (N j : ℕ) : Finset V := saturatedPrefix S es (preStrat S es N j)

def Kstrat (N j : ℕ) : AddSubgroup Q := S.K (Zstrat S es N j)

def numStrata (N : ℕ) : ℕ := if numRounds S es N=0 then 0 else sidx S es (numRounds S es N-1)+1

variable {S es}

lemma numRounds_le (N : ℕ) : numRounds S es N ≤ N := by
  unfold numRounds
  exact (card_filter_le _ _).trans (card_range N).le

lemma active_iff_lt_numRounds {N t : ℕ} (hTrace : Trace S N es) (ht : t < N) :
    S.K (saturatedPrefix S es t) ≠ ⊥ ↔ t < numRounds S es N := by
  let p : ℕ → Prop := fun r => r < N ∧ S.K (saturatedPrefix S es r) ≠ ⊥
  have hp : ∀ r s,r ≤  s → p s → p r := by
    intro r s hrs hs
    exact ⟨lt_of_le_of_lt hrs hs.1,trace_active_of_le hTrace r s hrs hs.1.le hs.2⟩
  have hFilter : (range N).filter p=(range N).filter (fun r => S.K (saturatedPrefix S es r) ≠ ⊥) := by
    ext r
    simp only [mem_filter,mem_range,p]
    tauto
  have hh := S07V40.lt_card_filter_range_iff hp ht
  rw [hFilter] at hh
  simpa only [p,ht,true_and,numRounds] using hh

lemma active_of_lt_numRounds {N t : ℕ} (hTrace : Trace S N es)
    (ht : t < numRounds S es N) : S.K (saturatedPrefix S es t) ≠ ⊥ :=
  (active_iff_lt_numRounds hTrace (lt_of_lt_of_le ht (numRounds_le N))).mpr ht

theorem stop_dichotomy {N : ℕ} (hTrace : Trace S N es) :
    S.K (saturatedPrefix S es N)=⊥ ∨ numRounds S es N=N := by
  by_cases hb : S.K (saturatedPrefix S es N)=⊥
  · exact Or.inl hb
  · right
    unfold numRounds
    rw [filter_true_of_mem,card_range]
    intro r hr
    exact trace_active_of_le hTrace r N (mem_range.mp hr).le le_rfl hb

lemma sidx_zero : sidx S es 0 = 0 := by simp [sidx]

lemma sidx_succ (r : ℕ) :
    sidx S es (r + 1) = sidx S es r + if S.K (saturatedPrefix S es (r + 1))  ≠  S.K (saturatedPrefix S es r) then 1 else 0 := by
  unfold sidx
  rw [range_add_one, filter_insert]
  split_ifs with h
  · rw [card_insert_of_notMem (by simp)]
  · simp

lemma sidx_succ_le (r : ℕ) : sidx S es (r + 1)  ≤  sidx S es r + 1 := by
  rw [sidx_succ]; split_ifs <;> omega

lemma sidx_mono : Monotone (sidx S es) :=
  monotone_nat_of_le_succ (fun r => by rw [sidx_succ]; omega)

/-- Equal stratum index forces equal `K`. -/
lemma K_eq_of_sidx_eq {r r' : ℕ} (hrr : r  ≤  r') (h : sidx S es r = sidx S es r') :
    S.K (saturatedPrefix S es r) = S.K (saturatedPrefix S es r') := by
  induction r', hrr using Nat.le_induction with
  | base => rfl
  | succ r' hr ih =>
    have h1 := sidx_mono (S := S) (es := es) hr
    have h2 := sidx_succ (S := S) (es := es) r'
    have hr' : sidx S es r = sidx S es r' := by
      have := sidx_mono (S := S) (es := es) (Nat.le_succ r'); omega
    rw [ih hr']
    by_contra hne
    rw [if_pos (Ne.symm hne)] at h2
    omega

/-- Every stratum index up to `sidx r` is attained at or before `r`. -/
lemma exists_sidx_eq (r : ℕ) : ∀ j  ≤  sidx S es r, ∃ r'  ≤  r, sidx S es r' = j := by
  induction r with
  | zero => intro j hj; rw [sidx_zero] at hj; exact ⟨0, le_rfl, by rw [sidx_zero]; omega⟩
  | succ r ih =>
    intro j hj
    by_cases hj' : j  ≤  sidx S es r
    · obtain ⟨r', hr', h⟩ := ih j hj'
      exact ⟨r', by omega, h⟩
    · have := sidx_succ_le (S := S) (es := es) r
      exact ⟨r + 1, le_rfl, by omega⟩

lemma card_filter_sidx_lt (N j : ℕ) :
    ((range (numRounds S es N)).filter (fun r => sidx S es r  <  j)).card = preStrat S es N j := by
  induction j with
  | zero => simp [preStrat]
  | succ j ih =>
    rw [preStrat, sum_range_succ, ← preStrat, ← ih, mStrat, ← card_union_of_disjoint]
    · congr 1
      ext r; simp only [mem_filter, mem_union, mem_range]; constructor <;> intro h <;> omega
    · rw [disjoint_filter]; intro r _ h1 h2; omega

lemma preStrat_le (N j : ℕ) : preStrat S es N j  ≤  numRounds S es N := by
  rw [← card_filter_sidx_lt]
  exact (card_filter_le _ _).trans (card_range _).le

lemma preStrat_succ (N j : ℕ) : preStrat S es N (j + 1) = preStrat S es N j + mStrat S es N j :=
  sum_range_succ _ _

/-- `sidx r  <  j ↔ r  <  pre j` on executed rounds. -/
lemma sidx_lt_iff {N r j : ℕ} (hr : r  <  numRounds S es N) : sidx S es r  <  j ↔ r  <  preStrat S es N j := by
  rw [← card_filter_sidx_lt]
  exact lt_card_filter_range_iff (fun s t hst h => lt_of_le_of_lt (sidx_mono (S := S) (es := es) hst) h) hr

/-- **Stratum `j` is the interval `[pre j, pre (j+1))` of executed rounds.** -/
lemma sidx_eq_iff {N r j : ℕ} (hr : r  <  numRounds S es N) :
    sidx S es r = j ↔ preStrat S es N j  ≤  r ∧ r  <  preStrat S es N (j + 1) := by
  have h1 := sidx_lt_iff (j := j) hr
  have h2 := sidx_lt_iff (j := j + 1) hr
  constructor
  · intro h
    exact ⟨not_lt.1 (fun h' => by have := h1.2 h'; omega), h2.1 (by omega)⟩
  · rintro ⟨ha, hb⟩
    have := h2.2 hb
    have : ¬ sidx S es r  <  j := fun h' => by have := h1.1 h'; omega
    omega

/-- `K` is constant on stratum `j`, equal to `Kstrat S es N j`. -/
lemma K_eq_Kstrat {N r j : ℕ} (hr : r  <  numRounds S es N) (hj : sidx S es r = j) :
    S.K (saturatedPrefix S es r) = Kstrat S es N j := by
  obtain ⟨h1, h2⟩ := (sidx_eq_iff hr).1 hj
  have hp : preStrat S es N j  <  numRounds S es N := lt_of_le_of_lt h1 hr
  have hpj : sidx S es (preStrat S es N j) = j := (sidx_eq_iff hp).2 ⟨le_rfl, by omega⟩
  exact (K_eq_of_sidx_eq h1 (by rw [hpj, hj])).symm

lemma mStrat_pos_iff {N j : ℕ} : 0  <  mStrat S es N j ↔ ∃ r  <  numRounds S es N, sidx S es r = j := by
  unfold mStrat
  rw [Finset.card_pos]
  constructor
  · rintro ⟨r, hr⟩; rw [mem_filter, mem_range] at hr; exact ⟨r, hr⟩
  · rintro ⟨r, hr, h⟩; exact ⟨r, mem_filter.2 ⟨mem_range.2 hr, h⟩⟩

/-- Nonempty strata are exactly `j  <  numStrata`. -/
lemma mStrat_pos_iff_lt_numStrata {N j : ℕ} : 0  <  mStrat S es N j ↔ j  <  numStrata S es N := by
  rw [mStrat_pos_iff, numStrata]
  split_ifs with h0
  · simp [h0]
  · constructor
    · rintro ⟨r, hr, rfl⟩
      have := sidx_mono (S := S) (es := es) (show r  ≤  numRounds S es N - 1 by omega)
      omega
    · intro hj
      obtain ⟨r', hr', h⟩ := exists_sidx_eq (S := S) (es := es) (numRounds S es N - 1) j (by omega)
      exact ⟨r', by omega, h⟩

omit [Fintype V] [Fintype C] in
/-- Decomposing a count by the round field. -/
lemma countP_eq_sum_round {P : ℕ} (N : ℕ) (f : Entry V C P → Bool) :
    ∀ (L : List (Entry V C P)), (∀ p  ∈  L, p.round  <  N) →
      L.countP f = ∑ r  ∈  range N, L.countP (fun p => f p && decide (p.round = r))
  | [], _ => by simp
  | a :: L, hL => by
    rw [List.countP_cons, countP_eq_sum_round N f L (fun p hp => hL p (List.mem_cons_of_mem _ hp))]
    simp only [List.countP_cons]
    rw [sum_add_distrib]
    congr 1
    have ha := hL a (List.mem_cons_self ..)
    by_cases hfa : f a = true
    · simp [hfa, ha]
    · simp [hfa]

/-- **Exactly `m_j` cells per active label in stratum `j`.** For every stratum `j` and label
`l`, the number of bank cells of stratum `j` with label `l` is `m_j` if `g c  ∈  Kstrat j` and `0`
otherwise.  (This is an equality, so no stratum can hide an incomplete round.) -/
theorem countP_stratum {N : ℕ} (hTrace : Trace S N es) (j : ℕ) (l : Lab C S.P) :
    es.countP (fun p => decide (sidx S es p.round = j ∧ p.lab = l)) =
      if S.g l.2.1  ∈  Kstrat S es N j then mStrat S es N j else 0 := by
  rw [countP_eq_sum_round N (fun p => sidx S es p.round = j ∧ p.lab = l) es
    (trace_rounds_lt hTrace)]
  have hterm : ∀ r  ∈  range N,
      es.countP (fun p => decide (sidx S es p.round = j ∧ p.lab = l) &&
          decide (p.round = r)) =
        if r  <  numRounds S es N ∧ sidx S es r = j ∧ S.g l.2.1  ∈  S.K (saturatedPrefix S es r) then 1 else 0 := by
    intro r hr
    rw [mem_range] at hr
    by_cases hj : sidx S es r = j
    · rw [List.countP_congr (q := fun p => decide (p.round = r ∧ p.lab = l))
        (fun p _ => by
          simp only [Bool.and_eq_true, decide_eq_true_eq]
          constructor
          · rintro ⟨⟨_, h2⟩, h3⟩; exact ⟨h3, h2⟩
          · rintro ⟨h3, h2⟩; exact ⟨⟨by rw [h3, hj], h2⟩, h3⟩),
        trace_round_exact hTrace]
      have ha := active_iff_lt_numRounds hTrace hr
      by_cases h : r  <  numRounds S es N <;> simp [hr, hj, h, ha]
    · rw [List.countP_eq_zero.2 (fun p _ => by
        simp only [Bool.and_eq_true, decide_eq_true_eq, not_and]
        intro ⟨h1, _⟩ h3; rw [h3] at h1; exact hj h1)]
      simp [hj]
  rw [sum_congr rfl hterm, sum_boole]
  simp only [Nat.cast_id]
  split_ifs with hg
  · unfold mStrat
    congr 1
    ext r
    simp only [mem_filter, mem_range]
    constructor
    · rintro ⟨_, h1, h2, _⟩; exact ⟨h1, h2⟩
    · rintro ⟨h1, h2⟩
      exact ⟨lt_of_lt_of_le h1 (numRounds_le N), h1, h2, by rw [K_eq_Kstrat h1 h2]; exact hg⟩
  · rw [card_eq_zero, filter_eq_empty_iff]
    rintro r - ⟨h1, h2, h3⟩
    rw [K_eq_Kstrat h1 h2] at h3
    exact hg h3


variable {H : Host V I} {F : Set (Multiset I)} {Ub : ℕ} {pay : ℝ}
  {R0 : Finset (Finset V)} {N L : ℕ}

/-- Chain length is evaluated on the actual monotone saturation curve. -/
theorem sidx_le (hInv : Seeded.RunInv H F S Ub pay R0 N es) (hq : 0 < S.q)
    (hL : ChainBound S L) (hcap : 2*S.E*S.Bstar*N ≤ S.q*S.zmax)
    {r : ℕ} (hr : r < numRounds S es N) : sidx S es r ≤ L := by
  have hR := numRounds_le (S:=S) (es:=es) N
  have h1 : sidx S es r ≤  sidx S es (numRounds S es N-1) := sidx_mono (by omega)
  have h2 : sidx S es (numRounds S es N-1) ≤ L :=
    hL (numRounds S es N-1) (saturatedPrefix S es) (saturatedPrefix_mono S es)
      (fun i hi => saturatedPrefix_small hInv hq hcap i (by omega))
  omega

theorem numStrata_le (hInv : Seeded.RunInv H F S Ub pay R0 N es) (hq : 0 < S.q)
    (hL : ChainBound S L) (hcap : 2*S.E*S.Bstar*N ≤ S.q*S.zmax) : numStrata S es N ≤ L+1 := by
  unfold numStrata
  split_ifs with h0
  · omega
  · have hh := sidx_le hInv hq hL hcap (show numRounds S es N-1 < numRounds S es N by omega)
    omega

theorem sum_mStrat (hInv : Seeded.RunInv H F S Ub pay R0 N es) (hq : 0 < S.q)
    (hL : ChainBound S L) (hcap : 2*S.E*S.Bstar*N ≤ S.q*S.zmax) :
    ∑j ∈ range (L+1),mStrat S es N j=numRounds S es N := by
  rw [←preStrat,←card_filter_sidx_lt,filter_true_of_mem,card_range]
  intro r hr
  have hh := sidx_le hInv hq hL hcap (mem_range.mp hr)
  omega

theorem card_Zstrat_le (hInv : Seeded.RunInv H F S Ub pay R0 N es) (j : ℕ) :
    S.q*(Zstrat S es N j).card ≤ 2*S.E*S.Bstar*∑i ∈ range j,mStrat S es N i :=
  saturatedPrefix_bound hInv _ ((preStrat_le N j).trans (numRounds_le N))

/-- An actual placed entry necessarily belongs to an executed round. -/
theorem entry_executed (hTrace : Trace S N es) {e : Entry V C S.P} (he : e ∈ es) :
    e.round < numRounds S es N := by
  have hPos : 0 < es.countP (fun a => decide (a.round=e.round ∧ a.lab=e.lab)) :=
    List.countP_pos_iff.mpr ⟨e,he,by simp⟩
  rw [trace_round_exact hTrace] at hPos
  split_ifs at hPos with ha
  · exact (active_iff_lt_numRounds hTrace ha.1).mp ha.2.1
  · omega

abbrev StratOcc (S : MacroSetting V Q C) (es : List (Entry V C S.P)) (j : ℕ) :=
  SliceOcc es (fun r => sidx S es r=j)

def stratBank (S : MacroSetting V Q C) (es : List (Entry V C S.P)) (j : ℕ) :
    Bank V (StratOcc S es j) C S.P := sliceBank es (fun r => sidx S es r=j)

theorem stratBank_fiber_card (hTrace : Trace S N es) (j : ℕ) (s : Bool) (c : C) (p : Fin S.P) :
    ((stratBank S es j).fiber s c p).card=
      if S.g c ∈ Kstrat S es N j then mStrat S es N j else 0 := by
  rw [←countP_stratum hTrace j (s,c,p),←S07V43.card_filter_get]
  unfold Bank.fiber stratBank sliceBank occurrenceBank
  refine Finset.card_bij (fun i _ => i.1) ?_ ?_ ?_
  · intro i hi
    have hp := (mem_filter.mp hi).2
    exact mem_filter.mpr ⟨mem_univ _,by
      simp only [decide_eq_true_eq]
      exact ⟨i.2,Prod.ext hp.1 (Prod.ext hp.2.1 hp.2.2)⟩⟩
  · intro i _ k _ hik
    exact Subtype.ext hik
  · intro i hi
    have hh := (mem_filter.mp hi).2
    simp only [decide_eq_true_eq] at hh
    refine ⟨⟨i,hh.1⟩,mem_filter.mpr ⟨mem_univ _,?_⟩,rfl⟩
    change (es.get i).lab.1=s ∧ (es.get i).lab.2.1=c ∧ (es.get i).lab.2.2=p
    rw [hh.2]
    exact ⟨rfl,rfl,rfl⟩

theorem stratBank_valid (hInv : Seeded.RunInv H F S Ub pay R0 N es) (j : ℕ) :
    (stratBank S es j).Valid S.basal S.w S.g :=
  occurrence_valid hInv.history.local_history (Function.Embedding.subtype _)

theorem stratBank_total_subset (j : ℕ) : (stratBank S es j).total ⊆ usedEdges es :=
  occurrence_total_subset es (Function.Embedding.subtype _)

theorem stratBank_totals_disjoint (hInv : Seeded.RunInv H F S Ub pay R0 N es)
    {i j : ℕ} (hij : i ≠ j) : Disjoint (stratBank S es i).total (stratBank S es j).total := by
  unfold Bank.total
  rw [disjoint_biUnion_left]
  intro k _
  rw [disjoint_biUnion_right]
  intro l _
  have hne : k.1 ≠ l.1 := by
    intro hkl
    apply hij
    calc i=sidx S es (es.get k.1).round := k.2.symm
      _ = sidx S es (es.get l.1).round := by rw [hkl]
      _ = j := l.2
  change Disjoint (es.get k.1).cell.tot (es.get l.1).cell.tot
  have hpw := List.pairwise_iff_get.mp hInv.history.local_history.disjoint
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · exact hpw _ _ hlt
  · exact (hpw _ _ hgt).symm

theorem stratBank_avoids (hInv : Seeded.RunInv H F S Ub pay R0 N es) (j : ℕ) :
    Avoids (Zstrat S es N j) (stratBank S es j).total := by
  intro f hf v hv hvf
  obtain ⟨i,_,hfi⟩ := mem_biUnion.mp hf
  let e := es.get i.1
  have he : e ∈ es := List.get_mem ..
  have hr := entry_executed hInv.trace he
  have hpre : preStrat S es N j ≤ e.round := ((sidx_eq_iff hr).mp i.2).1
  have hz : v ∈ e.deleted := by
    rw [trace_deleted_prefix hInv.trace e he]
    exact saturatedPrefix_mono S es hpre hv
  exact (hInv.history.local_history.good e he).good.2.2.2.2.1 f hfi v hz hvf

theorem stratBank_supplies (hTrace : Trace S N es) (j : ℕ) (z : Fin S.P → C → ℤ)
    (hact : ∀ p c,z p c ≠ 0 → S.g c ∈ Kstrat S es N j)
    (hz : ∀ p c,(z p c).natAbs ≤ mStrat S es N j) : (stratBank S es j).Supplies z := by
  intro p c
  by_cases h0 : z p c=0
  · rw [h0]; simp
  · rw [stratBank_fiber_card hTrace,if_pos (hact p c h0)]
    exact hz p c

theorem all_strata_total (hInv : Seeded.RunInv H F S Ub pay R0 N es) (hq : 0 < S.q)
    (hL : ChainBound S L) (hcap : 2*S.E*S.Bstar*N ≤ S.q*S.zmax) :
    (range (L+1)).biUnion (fun j => (stratBank S es j).total)=usedEdges es := by
  apply Subset.antisymm
  · exact biUnion_subset.mpr (fun j _ => stratBank_total_subset j)
  · intro f hf
    rw [←toBank_total es] at hf
    obtain ⟨i,_,hfi⟩ := mem_biUnion.mp hf
    let j := sidx S es (es.get i).round
    have hr := entry_executed hInv.trace (List.get_mem es i)
    have hj : j ≤ L := sidx_le hInv hq hL hcap hr
    refine mem_biUnion.mpr ⟨j,mem_range.mpr (by omega),?_⟩
    exact mem_biUnion.mpr ⟨⟨i,rfl⟩,mem_univ _,hfi⟩


theorem Zstrat_mono {i j : ℕ} (hij : i ≤ j) : Zstrat S es N i ⊆ Zstrat S es N j := by
  unfold Zstrat
  apply saturatedPrefix_mono S es
  unfold preStrat
  exact sum_le_sum_of_subset (range_subset_range.mpr hij)

theorem Zstrat_zero (hq : 0 < S.q) : Zstrat S es N 0=∅ := by
  have hp : roundPrefix es 0=[] := by simp [roundPrefix]
  simp only [Zstrat,preStrat,range_zero,sum_empty,saturatedPrefix,hp,usedEdges]
  exact satSet_empty hq

theorem one_le_m0 {J : ℕ} (h : 1 ≤ ∑i ∈ range (J+1),mStrat S es N i) : 1 ≤ mStrat S es N 0 := by
  obtain ⟨i,_,hi⟩ : ∃i ∈ range (J+1),0 < mStrat S es N i := by
    by_contra hc
    push_neg at hc
    have hz : ∑i ∈ range (J+1),mStrat S es N i=0 :=
      sum_eq_zero (fun i hi => Nat.le_zero.mp (hc i hi))
    omega
  have hn := (mStrat_pos_iff_lt_numStrata.mp hi)
  exact mStrat_pos_iff_lt_numStrata.mpr (by omega)

theorem K_numRounds_eq_bot (hTrace : Trace S N es) (h : numRounds S es N < N) :
    S.K (saturatedPrefix S es (numRounds S es N))=⊥ := by
  by_contra hc
  have hh := (active_iff_lt_numRounds hTrace h).mp hc
  exact Nat.lt_irrefl _ hh

theorem preStrat_numStrata (hInv : Seeded.RunInv H F S Ub pay R0 N es) (hq : 0 < S.q)
    (hL : ChainBound S L) (hcap : 2*S.E*S.Bstar*N ≤ S.q*S.zmax) :
    preStrat S es N (numStrata S es N)=numRounds S es N := by
  rw [←sum_mStrat hInv hq hL hcap]
  unfold preStrat
  have hle := numStrata_le hInv hq hL hcap
  refine sum_subset (range_subset_range.mpr hle) (fun j hj hjn => ?_)
  simp only [mem_range,not_lt] at hjn
  by_contra hc
  have hp := mStrat_pos_iff_lt_numStrata.mp (Nat.pos_of_ne_zero hc)
  omega

theorem K_Zstrat_numStrata_bot (hInv : Seeded.RunInv H F S Ub pay R0 N es) (hq : 0 < S.q)
    (hL : ChainBound S L) (hcap : 2*S.E*S.Bstar*N ≤ S.q*S.zmax)
    (hK : S.K (saturatedPrefix S es N)=⊥) :
    S.K (Zstrat S es N (numStrata S es N))=⊥ := by
  unfold Zstrat
  rw [preStrat_numStrata hInv hq hL hcap]
  rcases lt_or_eq_of_le (numRounds_le (S:=S) (es:=es) N) with h | h
  · exact K_numRounds_eq_bot hInv.trace h
  · rw [h]; exact hK

end TypedTriangle.Pasch.RichBank.Actual
#print axioms TypedTriangle.Pasch.RichBank.Actual.stop_dichotomy
#print axioms TypedTriangle.Pasch.RichBank.Actual.countP_stratum
#print axioms TypedTriangle.Pasch.RichBank.Actual.numStrata_le
#print axioms TypedTriangle.Pasch.RichBank.Actual.sum_mStrat
#print axioms TypedTriangle.Pasch.RichBank.Actual.card_Zstrat_le
#print axioms TypedTriangle.Pasch.RichBank.Actual.stratBank_fiber_card
#print axioms TypedTriangle.Pasch.RichBank.Actual.stratBank_valid
#print axioms TypedTriangle.Pasch.RichBank.Actual.stratBank_totals_disjoint
#print axioms TypedTriangle.Pasch.RichBank.Actual.stratBank_avoids
#print axioms TypedTriangle.Pasch.RichBank.Actual.stratBank_supplies
#print axioms TypedTriangle.Pasch.RichBank.Actual.all_strata_total
#print axioms TypedTriangle.Pasch.RichBank.Actual.Zstrat_mono
#print axioms TypedTriangle.Pasch.RichBank.Actual.Zstrat_zero
#print axioms TypedTriangle.Pasch.RichBank.Actual.preStrat_numStrata
#print axioms TypedTriangle.Pasch.RichBank.Actual.K_Zstrat_numStrata_bot
