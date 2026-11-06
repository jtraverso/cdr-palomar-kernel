module
public import RequestProject.TypedTriangle.BasalPackingIncidence
set_option maxHeartbeats 4000000 -- build option (original: -DmaxHeartbeats=1600000; raised)
set_option maxRecDepth 16384 -- build option (original: -DmaxRecDepth=8192; raised)
@[expose] public section
open Finset Classical
noncomputable section
namespace TypedTriangle.BasalSampling.Explicit

def samplingCut (q β : ℝ) : ℕ :=
  ⌈96 / (min (q^2/4) (β*q^4/128))^4⌉₊+1

theorem sampling_window_explicit {q β : ℝ} (hq : 0 < q) (hβ : 0 < β) :
    ∀ n a b : ℕ, samplingCut q β ≤ n → a ≤ n → b ≤ n ^ 2 →
      (a : ℝ) * Real.exp (-(q ^ 2 * n / 4)) +
      b * Real.exp (-(β * n * q ^ 4 / 128)) < 1 := by
  let θ : ℝ := min (q ^ 2 / 4) (β * q ^ 4 / 128)
  have hθ : 0 < θ := lt_min (by positivity) (by positivity)
  intro n a b hn ha hb
  change ⌈96/θ^4⌉₊+1 ≤ n at hn
  have hnR : (96 / θ ^ 4 : ℝ) < n := by
    have h1 := Nat.le_ceil (96 / θ ^ 4)
    have h2 : ((⌈96 / θ ^ 4⌉₊ + 1 : ℕ) : ℝ) ≤ n := by exact_mod_cast hn
    push_cast at h2
    linarith
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast (show 1 ≤ n by omega)
  have hn0 : (0 : ℝ) ≤ n := by positivity
  have haR : (a : ℝ) ≤ n := by exact_mod_cast ha
  have hbR : (b : ℝ) ≤ (n : ℝ) ^ 2 := by exact_mod_cast hb
  have e1 : Real.exp (-(q ^ 2 * n / 4)) ≤ Real.exp (-(θ * n)) := by
    apply Real.exp_le_exp.mpr
    have := mul_le_mul_of_nonneg_right (min_le_left (q ^ 2 / 4) (β * q ^ 4 / 128)) hn0
    dsimp only [θ]
    nlinarith
  have e2 : Real.exp (-(β * n * q ^ 4 / 128)) ≤ Real.exp (-(θ * n)) := by
    apply Real.exp_le_exp.mpr
    have := mul_le_mul_of_nonneg_right (min_le_right (q ^ 2 / 4) (β * q ^ 4 / 128)) hn0
    dsimp only [θ]
    nlinarith
  have hpoly : (n : ℝ) + (n : ℝ) ^ 2 ≤ 4 * (n : ℝ) ^ 3 := by
    have h1 := mul_le_mul_of_nonneg_left hn1 hn0
    have h2 := mul_le_mul_of_nonneg_left hn1 (sq_nonneg (n : ℝ))
    nlinarith
  calc
    _ ≤ (n : ℝ) * Real.exp (-(θ * n)) + (n : ℝ) ^ 2 * Real.exp (-(θ * n)) :=
      add_le_add (mul_le_mul haR e1 (Real.exp_pos _).le hn0)
        (mul_le_mul hbR e2 (Real.exp_pos _).le (sq_nonneg _))
    _ = ((n : ℝ) + (n : ℝ) ^ 2) * Real.exp (-(θ * n)) := by ring
    _ ≤ 4 * (n : ℝ) ^ 3 * Real.exp (-(θ * n)) :=
      mul_le_mul_of_nonneg_right hpoly (Real.exp_pos _).le
    _ < 1 := S07V24.four_cube_exp_lt hθ hnR


#print axioms sampling_window_explicit
end TypedTriangle.BasalSampling.Explicit
namespace TypedTriangle.BasalIncidence.Explicit
theorem sample_packing_explicit (q β : ℝ) (hq : 0 < q) (hq1 : q ≤ 1) (hβ : 0 < β) :
    ∀ (V : Type) [Fintype V] (I : Type) (H : Host V I)
      (F : Set (Multiset I)) (P : Finset (Finset V)), IsPacking H F P →
      BasalSampling.Explicit.samplingCut q β ≤ Fintype.card V → ∀ (τ : Type) [Fintype τ] (u v : τ → V),
      Fintype.card τ ≤ Fintype.card V ^ 2 →
      (∀ t, β * Fintype.card V ≤ (good H F P (u t) (v t)).card) →
      ∃ D ⊆ P, IsDecomposition H F (cover D) D ∧
        (∀ x, (((cover D).filter (fun e => x ∈ e)).card : ℝ) < 6 * q * Fintype.card V) ∧
        ∀ t, β * Fintype.card V * q ^ 2 / 2 ≤ (good H F D (u t) (v t)).card := by
  have hn₀ := BasalSampling.Explicit.sampling_window_explicit hq hβ
  intro V _ I H F P hP hn τ _ u v hτ hmass
  let S : V → Finset P := fun x => univ.filter (fun b => x ∈ b.val)
  let J : τ → Finset V := fun t => good H F P (u t) (v t)
  let d : τ → V → Finset P := fun t => dep H F P (u t) (v t)
  obtain ⟨W, hsmall, hcenters⟩ := BasalSampling.simultaneous_sample
    q (Fintype.card V) (β * Fintype.card V) hq hq1 S J d
    (fun x => by exact_mod_cast root_block_card hP x) hmass
    (fun t w _ => dep_card H F P (u t) (v t) w)
    (fun t b => dep_load_le_four hP (u t) (v t) b)
    (hn₀ (Fintype.card V) (Fintype.card V) (Fintype.card τ) hn le_rfl hτ)
  refine ⟨selected W, selected_subset W, ?_, ?_, ?_⟩
  · simpa only [cover, stock_eq_selected] using selected_decomposition hP W
  · intro x
    have hNat := stock_degree_le hP W x
    rw [stock_eq_selected] at hNat
    have hBound : (((cover (selected W)).filter (fun e => x ∈ e)).card : ℝ) ≤
        3 * ((W.filter (fun b => x ∈ b.val)).card : ℝ) := by exact_mod_cast hNat
    have hSmall : ((W.filter (fun b => x ∈ b.val)).card : ℝ) < 2 * q * Fintype.card V := by
      simpa only [S, selected_load_eq] using hsmall x
    linarith
  · intro t
    have hsub : (J t).filter (fun w => d t w ⊆ W) ⊆ good H F (selected W) (u t) (v t) := by
      intro w hw
      obtain ⟨hwJ, hret⟩ := mem_filter.mp hw
      have hh := retained_wings hwJ W hret
      refine mem_filter.mpr ⟨mem_univ _, hh.1, ?_, ?_⟩
      · simpa only [stock_eq_selected, cover] using hh.2.1
      · simpa only [stock_eq_selected, cover] using hh.2.2
    exact (hcenters t).trans (by exact_mod_cast card_le_card hsub)


#print axioms sample_packing_explicit
end TypedTriangle.BasalIncidence.Explicit
