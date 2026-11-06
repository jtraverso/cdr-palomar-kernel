/-
Copyright (c) 2026 Juan Pablo Traverso Gianini.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module
public import RequestProject.TypedTriangle.ExplicitDyadicBounds
public import RequestProject.TypedTriangle.SampleParams
set_option maxHeartbeats 4000000 -- build option (original: -DmaxHeartbeats=1600000; raised)
set_option maxRecDepth 16384 -- build option (original: -DmaxRecDepth=8192; raised)
@[expose] public section
open Finset Classical
noncomputable section
namespace TypedTriangle.ExplicitSample

def sampleLc (c : ℝ) : ℕ := ⌈30/c⌉₊
def sampleA (κ ε : ℝ) (q m0 : ℕ) : ℝ :=
  3/κ*(27/(κ^2*ε)+1+m0)+q
def sampleT (κ ε : ℝ) (q m0 : ℕ) : ℕ := ⌈6*sampleA κ ε q m0/ε⌉₊
def sampleJ (c κ ε : ℝ) (q m0 : ℕ) : ℕ :=
  ⌈max (4/c) (max (12*(sampleLc c+1:ℝ)/ε)
    (6*(sampleLc c+1:ℝ)*(sampleT κ ε q m0+1:ℝ)/ε))⌉₊
def sampleEta (c κ ε : ℝ) (q m0 : ℕ) : ℝ := ((1:ℝ)/2)^sampleJ c κ ε q m0
def sampleL (c κ ε : ℝ) (q m0 : ℕ) : ℕ := ⌈2/(κ*sampleEta c κ ε q m0)⌉₊
def sampleQ (c κ ε : ℝ) (q m0 : ℕ) : ℕ :=
  ⌈9*sampleL c κ ε q m0/(κ*sampleEta c κ ε q m0*ε)⌉₊+m0
def sampleB (c κ ε : ℝ) (q m0 : ℕ) : ℕ := sampleLc c*(sampleJ c κ ε q m0+sampleT κ ε q m0)

private theorem div_succ_le {A B : ℝ} (hA : 0 < A) (j : ℕ)
    (h : B/A ≤ (j:ℝ)) : B/((j:ℝ)+1) ≤ A := by
  apply (div_le_iff₀ (by positivity)).mpr
  have hh := (div_le_iff₀ hA).mp h
  nlinarith

theorem explicit_indices (c κ ε : ℝ) (q m0 : ℕ)
    (hc : 0 < c) (hc1 : c ≤ 1) (hκ : 0 < κ) (hε : 0 < ε) :
    (1-c/2)^(sampleLc c) ≤ (1:ℝ)/16 ∧
    ((1:ℝ)/16)^(sampleT κ ε q m0) ≤ ε/(3*sampleA κ ε q m0) ∧
    sampleEta c κ ε q m0 ≤ c/2 ∧
    (sampleJ c κ ε q m0:ℝ)*sampleEta c κ ε q m0 ≤ ε/(6*(sampleLc c+1:ℝ)) ∧
    sampleEta c κ ε q m0 ≤ ε/(6*(sampleLc c+1:ℝ)*(sampleT κ ε q m0+1:ℝ)) := by
  let Lc := sampleLc c
  let A := sampleA κ ε q m0
  let t := sampleT κ ε q m0
  let j := sampleJ c κ ε q m0
  have hA : 0 < A := by dsimp [A,sampleA]; positivity
  have hLc : 30/c ≤ (Lc:ℝ) := Nat.le_ceil _
  have ht : 6*A/ε ≤ (t:ℝ) := Nat.le_ceil _
  have hj : max (4/c) (max (12*(Lc+1:ℝ)/ε) (6*(Lc+1:ℝ)*(t+1:ℝ)/ε)) ≤ (j:ℝ) :=
    Nat.le_ceil _
  have hjc : 4/c ≤ (j:ℝ) := (le_max_left _ _).trans hj
  have hjw : 12*(Lc+1:ℝ)/ε ≤ (j:ℝ) := (le_max_left _ _).trans ((le_max_right _ _).trans hj)
  have hje : 6*(Lc+1:ℝ)*(t+1:ℝ)/ε ≤ (j:ℝ) := (le_max_right _ _).trans ((le_max_right _ _).trans hj)
  have hLcPay := (div_le_iff₀ hc).mp hLc
  have htPay := (div_le_iff₀ hε).mp ht
  have hFirst : (1-c/2)^Lc ≤ (1:ℝ)/16 := by
    calc (1-c/2)^Lc ≤ 1/(1+(Lc:ℝ)*(c/2)) :=
      one_sub_pow_le_inv (by linarith) (by linarith) Lc
      _ ≤ 1/16 := (div_le_div_iff₀ (by positivity) (by norm_num)).mpr (by nlinarith)
  have hSecond : ((1:ℝ)/16)^t ≤ ε/(3*A) := by
    calc ((1:ℝ)/16)^t = (1-(15:ℝ)/16)^t := by norm_num
      _ ≤ 1/(1+(t:ℝ)*(15/16)) := one_sub_pow_le_inv (by norm_num) (by norm_num) t
      _ ≤ ε/(3*A) := (div_le_div_iff₀ (by positivity) (by positivity)).mpr (by nlinarith)
  have hThird : ((1:ℝ)/2)^j ≤ c/2 := by
    apply (dyadic_le_inv j).trans
    apply div_succ_le (by positivity) j
    calc 1/(c/2) = 2/c := by ring
      _ ≤ 4/c := by gcongr <;> norm_num
      _ ≤ (j:ℝ) := hjc
  have hFourth : (j:ℝ)*((1:ℝ)/2)^j ≤ ε/(6*(Lc+1:ℝ)) := by
    apply (weighted_dyadic_le_inv j).trans
    apply div_succ_le (by positivity) j
    convert hjw using 1 <;> field_simp <;> ring
  have hFifth : ((1:ℝ)/2)^j ≤ ε/(6*(Lc+1:ℝ)*(t+1:ℝ)) := by
    apply (dyadic_le_inv j).trans
    apply div_succ_le (by positivity) j
    convert hje using 1 <;> field_simp <;> ring
  exact ⟨hFirst,hSecond,hThird,hFourth,hFifth⟩

theorem sample_params_explicit {c κ ε : ℝ} (q m0 : ℕ) (hc : 0 < c) (hc1 : c ≤ 1)
    (hκ : 0 < κ) (hκ1 : κ ≤ 1) (hε : 0 < ε) :
    let η := sampleEta c κ ε q m0
    let L := sampleL c κ ε q m0
    let Q := sampleQ c κ ε q m0
    let b := sampleB c κ ε q m0
    0 < η ∧ η ≤ c/2 ∧ 1 < L*(κ*η) ∧ m0 ≤ Q ∧
      L*(1-κ*η)^Q+(L*Q+q)*(1-c+η)^b+b*η ≤ ε := by
  set r : ℝ := 1-c/2
  have hr0 : 0 ≤ r := by dsimp [r]; linarith
  let Lc := sampleLc c
  let A := sampleA κ ε q m0
  let t := sampleT κ ε q m0
  let j := sampleJ c κ ε q m0
  have hA : 0 < A := by dsimp [A,sampleA]; positivity
  obtain ⟨hLc,ht,hj1,hj2,hj3⟩ := explicit_indices c κ ε q m0 hc hc1 hκ hε
  set η : ℝ := ((1 : ℝ) / 2) ^ j
  set u : ℝ := (2 : ℝ) ^ j
  have hηu : η * u = 1 := by simp only [η, u]; rw [← mul_pow]; norm_num
  have hη0 : 0 < η := by positivity
  have hu1 : 1 ≤ u := one_le_pow₀ (by norm_num)
  have hη1 : η ≤ 1 := by nlinarith
  have hκη : 0 < κ * η := by positivity
  have hκη1 : κ * η ≤ 1 := by nlinarith
  set L : ℕ := ⌈2 / (κ * η)⌉₊
  set Q : ℕ := ⌈9 * L / (κ * η * ε)⌉₊ + m0
  set b : ℕ := Lc * (j + t)
  change 0 < η ∧ η ≤ c/2 ∧ 1 < L*(κ*η) ∧ m0 ≤ Q ∧
    L*(1-κ*η)^Q+(L*Q+q)*(1-c+η)^b+b*η ≤ ε
  refine ⟨hη0, hj1, ?_, by simp [Q], ?_⟩
  · have := Nat.le_ceil (2 / (κ * η))
    rw [div_le_iff₀ hκη] at this
    linarith
  -- cotas de `L` y `Q` en términos de `u = 2^j`
  have h1κη : 1 / (κ * η) = u / κ := by
    field_simp
    nlinarith
  have hL2 : (L : ℝ) ≤ 3 * u / κ := by
    have h := (Nat.ceil_lt_add_one (show (0 : ℝ) ≤ 2 / (κ * η) by positivity)).le
    have : 2 / (κ * η) = 2 * (u / κ) := by rw [← h1κη]; ring
    have hu' : 1 ≤ u / κ := by rw [le_div_iff₀ hκ]; linarith
    have e3 : 3 * u / κ = 3 * (u / κ) := by ring
    linarith
  have hQe : (Q : ℝ) = (⌈9 * L / (κ * η * ε)⌉₊ : ℝ) + m0 := by simp only [Q]; push_cast; rfl
  have hQ1 : 9 * L / (κ * η * ε) ≤ Q := by
    have := Nat.le_ceil (9 * L / (κ * η * ε))
    rw [hQe]; linarith [(by positivity : (0 : ℝ) ≤ m0)]
  have hQ2 : (Q : ℝ) ≤ (27 / (κ ^ 2 * ε) + 1 + m0) * u ^ 2 := by
    have h := (Nat.ceil_lt_add_one (show (0 : ℝ) ≤ 9 * L / (κ * η * ε) by positivity)).le
    have e : 9 * (L : ℝ) / (κ * η * ε) ≤ 27 / (κ ^ 2 * ε) * u ^ 2 := by
      have : 9 * (L : ℝ) / (κ * η * ε) = 9 * L * (u / κ) / ε := by
        rw [← h1κη]; field_simp
      rw [this]
      calc 9 * (L : ℝ) * (u / κ) / ε ≤ 9 * (3 * u / κ) * (u / κ) / ε := by gcongr
        _ = 27 / (κ ^ 2 * ε) * u ^ 2 := by field_simp; ring
    have hu2 : 1 ≤ u ^ 2 := one_le_pow₀ hu1
    rw [hQe]
    nlinarith [(by positivity : (0 : ℝ) ≤ m0)]
  -- primer término
  have hT1 := growth_term_le hκη hκη1 hε hQ1
  -- segundo término
  have hLQq : (L : ℝ) * Q + q ≤ A * u ^ 3 := by
    have hq : (q : ℝ) ≤ q * u ^ 3 := by
      have : 1 ≤ u ^ 3 := one_le_pow₀ hu1
      nlinarith [(by positivity : (0 : ℝ) ≤ q)]
    have hLQ : (L : ℝ) * Q ≤ 3 / κ * (27 / (κ ^ 2 * ε) + 1 + m0) * u ^ 3 := by
      calc (L : ℝ) * Q ≤ (3 * u / κ) * ((27 / (κ ^ 2 * ε) + 1 + m0) * u ^ 2) := by gcongr
        _ = _ := by ring
    have hAe : A = 3 / κ * (27 / (κ ^ 2 * ε) + 1 + m0) + q := rfl
    calc (L : ℝ) * Q + q ≤ 3 / κ * (27 / (κ ^ 2 * ε) + 1 + m0) * u ^ 3 + q * u ^ 3 := by linarith
      _ = A * u ^ 3 := by rw [hAe]; ring
  have hbase : 1 - c + η ≤ r := by
    have hj1' : η ≤ c / 2 := hj1
    simp only [r]
    linarith
  have hbase0 : 0 ≤ 1 - c + η := by linarith
  have hpowb : (1 - c + η) ^ b ≤ ((1 : ℝ) / 16) ^ (j + t) := by
    calc (1 - c + η) ^ b ≤ r ^ b := pow_le_pow_left₀ hbase0 hbase b
      _ = (r ^ Lc) ^ (j + t) := by rw [← pow_mul]
      _ ≤ ((1 : ℝ) / 16) ^ (j + t) := pow_le_pow_left₀ (pow_nonneg hr0 _) hLc _
  have hT2 : ((L : ℝ) * Q + q) * (1 - c + η) ^ b ≤ ε / 3 := by
    have hu3 : u ^ 3 * ((1 : ℝ) / 16) ^ j = η := by
      simp only [u, η]; rw [← pow_mul, mul_comm j 3, pow_mul, ← mul_pow]; norm_num
    calc ((L : ℝ) * Q + q) * (1 - c + η) ^ b ≤ (A * u ^ 3) * ((1 : ℝ) / 16) ^ (j + t) := by
          gcongr
      _ = A * η * ((1 : ℝ) / 16) ^ t := by rw [pow_add, ← hu3]; ring
      _ ≤ A * 1 * (ε / (3 * A)) := by gcongr
      _ = ε / 3 := by field_simp
  -- tercer término
  have hT3 : (b : ℝ) * η ≤ ε / 3 := final_term_le hε hj2 hj3
  linarith

universe u
open Sampler in
theorem component_sample_explicit {c κ ε : ℝ} (q m0 : ℕ) (hc : 0 < c) (hc1 : c ≤ 1) (hκ : 0 < κ)
    (hκ1 : κ ≤ 1) (hε : 0 < ε) :
    let L := sampleL c κ ε q m0
    let Q := sampleQ c κ ε q m0
    let b := sampleB c κ ε q m0
    1 ≤ L ∧ m0 ≤ Q ∧ ∀ {Ω : Type u} [Fintype Ω] (J : SimpleGraph Ω) (K : Finset Ω),
      K.Nonempty → NbrClosed J K → MinDegOn J K c → ExpandOn J K c κ →
      ∀ M : (Fin L → Fin Q → Ω) → Finset Ω, (∀ p, (M p).card ≤ q) →
      ((univ.filter (fun x : (Fin L → Fin Q → Ω) × (Fin b → Ω) =>
        ¬ SampleGood J K (M x.1) (pvals x.1) (pvals x.1 ∪ fvals x.2))).card : ℝ) ≤
        ε * Fintype.card ((Fin L → Fin Q → Ω) × (Fin b → Ω)) := by
  let L := sampleL c κ ε q m0
  let Q := sampleQ c κ ε q m0
  let b := sampleB c κ ε q m0
  let η := sampleEta c κ ε q m0
  obtain ⟨hη0,hηc,hL,hQ,hsum⟩ := sample_params_explicit q m0 hc hc1 hκ hκ1 hε
  have hη1 : η ≤ 1 := by linarith
  have hκη : κ * η ≤ c / 2 := by nlinarith
  change 1 < (L : ℝ) * (κ * η) at hL
  have hL1 : 1 ≤ L := by
    rcases Nat.eq_zero_or_pos L with h0 | h0
    · simp only [h0, Nat.cast_zero, zero_mul] at hL
      linarith
    · exact h0
  refine ⟨hL1, hQ, fun J K hne hK hdeg hexp M hMq => ?_⟩
  refine (card_not_sampleGood_le hK hdeg hexp hne hη0 hη1 (by linarith) (by nlinarith) hL M
    hMq).trans ?_
  exact mul_le_mul_of_nonneg_right hsum (by positivity)

#print axioms explicit_indices
#print axioms sample_params_explicit
#print axioms component_sample_explicit
end TypedTriangle.ExplicitSample
