module
public import RequestProject.TypedTriangle.PaschPackingSamplingExpectation
public import RequestProject.TypedTriangle.ExplicitBasalPackingSampling
set_option maxHeartbeats 4000000 -- build option (original: -DmaxHeartbeats=1600000; raised)
set_option maxRecDepth 16384 -- build option (original: -DmaxRecDepth=8192; raised)
@[expose] public section
open Finset Classical S07V24
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace TypedTriangle.BasalIncidence.PaschSampling
open TypedTriangle.BasalSampling

def thinRate (ρ K δ : ℝ) : ℝ :=
  min (ρ/12) (min (1/2) (δ/(8*(K+1))))

def samplingOrder (q β : ℝ) : ℕ := max 1 (BasalSampling.Explicit.samplingCut (q/2) β)

theorem thinRate_pos {ρ K δ : ℝ} (hρ : 0 < ρ) (hK : 0 ≤ K) (hδ : 0 < δ) :
    0 < thinRate ρ K δ := by
  unfold thinRate
  exact lt_min (by positivity) (lt_min (by norm_num) (by positivity))

theorem thinRate_caps {ρ K δ : ℝ} (hρ : 0 < ρ) (hK : 0 ≤ K) (hδ : 0 < δ) :
    thinRate ρ K δ ≤ ρ/12 ∧ thinRate ρ K δ ≤ 1/2 ∧
      8*(thinRate ρ K δ)^4*K ≤ δ := by
  let q := thinRate ρ K δ
  have hq : 0 < q := thinRate_pos hρ hK hδ
  have hqρ : q ≤ ρ/12 := min_le_left _ _
  have hqHalf : q ≤ 1/2 := (min_le_right _ _).trans (min_le_left _ _)
  have hqδ : q ≤ δ/(8*(K+1)) := (min_le_right _ _).trans (min_le_right _ _)
  have hqOne : q ≤ 1 := hqHalf.trans (by norm_num)
  have hqTwo : q^2 ≤ q := by
    have hh := mul_nonneg hq.le (sub_nonneg.mpr hqOne)
    nlinarith only [hh]
  have hqFour : q^4 ≤ q := by
    have hh := mul_nonneg (sq_nonneg q) (sub_nonneg.mpr (hqTwo.trans hqOne))
    have hh4 : q^4 ≤ q^2 := by nlinarith only [hh]
    exact hh4.trans hqTwo
  have hMul : q*(8*(K+1)) ≤ δ := (le_div_iff₀ (by positivity)).mp hqδ
  have hCost := mul_le_mul_of_nonneg_right hqFour hK
  refine ⟨hqρ,hqHalf,?_⟩
  nlinarith only [hMul,hCost,hq.le]

/-- The old native tails have total probability less than one half. Apply
their existing window at rate q/2, order 2n, and doubled event counts. -/
theorem sampling_window_half {q β : ℝ} (hq : 0 < q) (hβ : 0 < β) :
    ∀ n a b : ℕ, samplingOrder q β ≤ n → a ≤ n → b ≤ n^2 →
      (a : ℝ)*Real.exp (-(q^2*n/4))+
        b*Real.exp (-(β*n*q^4/128)) < 1/2 := by
  intro n a b hn ha hb
  have hnBase : BasalSampling.Explicit.samplingCut (q/2) β ≤ 2*n :=
    ((le_max_right _ _).trans hn).trans (by omega)
  have hb2 : 2*b ≤ (2*n)^2 := by nlinarith only [hb]
  have hBig := BasalSampling.Explicit.sampling_window_explicit (q := q/2)
    (half_pos hq) hβ (2*n) (2*a) (2*b) hnBase (Nat.mul_le_mul_left 2 ha) hb2
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg _
  have e1 : Real.exp (-(q^2*n/4)) ≤ Real.exp (-((q/2)^2*(2*n)/4)) := by
    apply Real.exp_le_exp.mpr
    have hh := mul_nonneg (sq_nonneg q) hn0
    nlinarith only [hh]
  have e2 : Real.exp (-(β*n*q^4/128)) ≤ Real.exp (-(β*(2*n)*(q/2)^4/128)) := by
    apply Real.exp_le_exp.mpr
    have hh : 0 ≤ β*(n : ℝ)*q^4 := by positivity
    nlinarith only [hh]
  have haE := mul_le_mul_of_nonneg_left e1 (Nat.cast_nonneg a : (0 : ℝ) ≤ a)
  have hbE := mul_le_mul_of_nonneg_left e2 (Nat.cast_nonneg b : (0 : ℝ) ≤ b)
  push_cast at hBig
  nlinarith only [hBig,haE,hbE]

private theorem simultaneous_sample_extra {B κ τ ι : Type*}
    [Fintype B] [DecidableEq B] [Fintype κ] [Fintype τ] [DecidableEq ι]
    (q N L : ℝ) (hq : 0 < q) (hq1 : q ≤ 1)
    (S : κ → Finset B) (J : τ → Finset ι) (dep : τ → ι → Finset B)
    (hS : ∀ k, ((S k).card : ℝ) ≤ N) (hJ : ∀ t, L ≤ (J t).card)
    (hsize : ∀ t i, i ∈ J t → (dep t i).card ≤ 2)
    (hload : ∀ t b, (((J t).filter (fun i => b ∈ dep t i)).card : ℝ) ≤ 4)
    (E : Finset B → Prop)
    (hExtra : bprob q univ E ≤ 1/8)
    (hwindow : Fintype.card κ*Real.exp (-(q^2*N/4))+
      Fintype.card τ*Real.exp (-(L*q^4/128)) < 1/2) :
    ∃ W : Finset B,
      (∀ k, (ccount (S k) (fun b => {b}) W : ℝ) < 2*q*N) ∧
      (∀ t, L*q^2/2 ≤ (ccount (J t) (dep t) W : ℝ)) ∧ ¬ E W := by
  let badOld : κ ⊕ τ → Finset B → Prop := fun j W => match j with
    | .inl k => 2*q*N ≤ (ccount (S k) (fun b => {b}) W : ℝ)
    | .inr t => (ccount (J t) (dep t) W : ℝ) < L*q^2/2
  have hOld : ∑ j ∈ (univ : Finset (κ ⊕ τ)), bprob q univ (badOld j) < 1/2 := by
    rw [Fintype.sum_sum_type]
    apply lt_of_le_of_lt _ hwindow
    apply add_le_add
    · calc
        ∑ k : κ, bprob q univ (badOld (.inl k)) ≤
            ∑ _k : κ, Real.exp (-(q^2*N/4)) := by
          apply sum_le_sum
          intro k _
          exact load_tail hq hq1 (S k) (hS k)
        _ = _ := by simp [mul_comm]
    · calc
        ∑ t : τ, bprob q univ (badOld (.inr t)) ≤
            ∑ _t : τ, Real.exp (-(L*q^4/128)) := by
          apply sum_le_sum
          intro t _
          have ht := count_tail (V := B) hq hq1 (J t) (dep t)
            (r := 2) (by norm_num) (hsize t) (Δ := 4) (by norm_num) (hload t) (hJ t)
          norm_num [badOld] at ht ⊢
          exact ht
        _ = _ := by simp [mul_comm]
  let bad : (κ ⊕ τ) ⊕ Unit → Finset B → Prop := fun j W => match j with
    | .inl k => badOld k W
    | .inr _ => E W
  have hTotal : ∑ j ∈ (univ : Finset ((κ ⊕ τ) ⊕ Unit)), bprob q univ (bad j) < 1 := by
    rw [Fintype.sum_sum_type]
    have hLeft : (∑ j : κ ⊕ τ, bprob q univ (bad (.inl j))) ≤
        ∑ j : κ ⊕ τ, bprob q univ (badOld j) := by
      apply sum_le_sum
      intro j _
      exact bprob_mono hq.le hq1 (fun W h => h)
    have hRight : (∑ u : Unit, bprob q univ (bad (.inr u))) ≤ bprob q univ E := by
      calc
        _ ≤ ∑ _u : Unit, bprob q univ E := by
          apply sum_le_sum
          intro u _
          exact bprob_mono hq.le hq1 (fun W h => h)
        _ = _ := by simp
    calc
      _ ≤ (∑ j : κ ⊕ τ, bprob q univ (badOld j))+bprob q univ E :=
        add_le_add hLeft hRight
      _ < (1/2 : ℝ)+1/8 := add_lt_add_of_lt_of_le hOld hExtra
      _ < 1 := by norm_num
  obtain ⟨W,_,hW⟩ := exists_good hq.le hq1 (univ : Finset B) univ bad hTotal
  refine ⟨W,?_,?_,hW (.inr ()) (mem_univ _)⟩
  · intro k
    exact lt_of_not_ge (hW (.inl (.inl k)) (mem_univ _))
  · intro t
    exact le_of_not_gt (hW (.inl (.inr t)) (mem_univ _))

/-- Actual block sampling retains the native degree and completion supply,
and controls Pasches simultaneously by their proved Bernoulli expectation. -/
theorem sample_packing_with_pasch (q β K δ : ℝ)
    (hq : 0 < q) (hq1 : q ≤ 1) (hβ : 0 < β) (hK : 0 ≤ K) (hδ : 0 < δ)
    (hRate : 8*q^4*K ≤ δ) :
    ∀ (V : Type) [Fintype V] (I : Type) (H : Host V I)
      (F : Set (Multiset I)) (P : Finset (Finset V)), IsPacking H F P →
      samplingOrder q β ≤ Fintype.card V →
      (Pasch.count P : ℝ) ≤ K*(Fintype.card V : ℝ)^2 →
      ∀ (τ : Type) [Fintype τ] (u v : τ → V), Fintype.card τ ≤ Fintype.card V^2 →
      (∀ t, β*Fintype.card V ≤ (good H F P (u t) (v t)).card) →
      ∃ D ⊆ P, IsDecomposition H F (cover D) D ∧
        (∀ x, (((cover D).filter (fun e => x ∈ e)).card : ℝ) < 6*q*Fintype.card V) ∧
        (∀ t, β*Fintype.card V*q^2/2 ≤ (good H F D (u t) (v t)).card) ∧
        (Pasch.count D : ℝ) ≤ δ*(Fintype.card V : ℝ)^2 := by
  intro V _ I H F P hP hn hCount τ _ u v hτ hmass
  have hnNat : 1 ≤ Fintype.card V := (le_max_left _ _).trans hn
  have hnPos : 0 < Fintype.card V := by omega
  have hnR : (0 : ℝ) < Fintype.card V := by exact_mod_cast hnPos
  let S : V → Finset P := fun x => univ.filter (fun b => x ∈ b.val)
  let J : τ → Finset V := fun t => good H F P (u t) (v t)
  let d : τ → V → Finset P := fun t => dep H F P (u t) (v t)
  let t : ℝ := δ*(Fintype.card V : ℝ)^2
  have ht : 0 < t := by dsimp only [t]; positivity
  have hExtra : bprob q (univ : Finset P)
      (fun W => t ≤ (Pasch.count (selected W) : ℝ)) ≤ 1/8 := by
    have hh := bprob_upper_le_bexp_div q hq.le hq1 (univ : Finset P)
      (fun W => (Pasch.count (selected W) : ℝ))
      (fun W _ => Nat.cast_nonneg _) t ht
    rw [Pasch.bexp_count_selected] at hh
    apply hh.trans
    apply (div_le_iff₀ ht).mpr
    have hMean := mul_le_mul_of_nonneg_left hCount (pow_nonneg hq.le 4)
    have hScale := mul_le_mul_of_nonneg_right hRate (sq_nonneg (Fintype.card V : ℝ))
    dsimp only [t]
    nlinarith only [hMean,hScale]
  obtain ⟨W,hsmall,hcenters,hStat⟩ := simultaneous_sample_extra
    q (Fintype.card V) (β*Fintype.card V) hq hq1 S J d
    (fun x => by exact_mod_cast root_block_card hP x) hmass
    (fun t w _ => dep_card H F P (u t) (v t) w)
    (fun t b => dep_load_le_four hP (u t) (v t) b)
    (fun W => t ≤ (Pasch.count (selected W) : ℝ))
    (by exact (bprob_mono hq.le hq1 (fun W h => h)).trans hExtra)
    (sampling_window_half hq hβ (Fintype.card V) (Fintype.card V)
      (Fintype.card τ) hn le_rfl hτ)
  refine ⟨selected W,selected_subset W,?_,?_,?_,?_⟩
  · simpa only [cover,stock_eq_selected] using selected_decomposition hP W
  · intro x
    have hNat := stock_degree_le hP W x
    rw [stock_eq_selected] at hNat
    have hBound : (((cover (selected W)).filter (fun e => x ∈ e)).card : ℝ) ≤
        3*((W.filter (fun b => x ∈ b.val)).card : ℝ) := by exact_mod_cast hNat
    have hSmall : ((W.filter (fun b => x ∈ b.val)).card : ℝ) < 2*q*Fintype.card V := by
      simpa only [S,selected_load_eq] using hsmall x
    linarith only [hBound,hSmall]
  · intro j
    have hSub : (J j).filter (fun w => d j w ⊆ W) ⊆ good H F (selected W) (u j) (v j) := by
      intro w hw
      obtain ⟨hwJ,hRet⟩ := mem_filter.mp hw
      have hh := retained_wings hwJ W hRet
      refine mem_filter.mpr ⟨mem_univ _,hh.1,?_,?_⟩
      · simpa only [stock_eq_selected,cover] using hh.2.1
      · simpa only [stock_eq_selected,cover] using hh.2.2
    exact (hcenters j).trans (by exact_mod_cast card_le_card hSub)
  · exact (lt_of_not_ge hStat).le

end TypedTriangle.BasalIncidence.PaschSampling

#print axioms TypedTriangle.BasalIncidence.PaschSampling.thinRate_caps
#print axioms TypedTriangle.BasalIncidence.PaschSampling.sampling_window_half
#print axioms TypedTriangle.BasalIncidence.PaschSampling.sample_packing_with_pasch
