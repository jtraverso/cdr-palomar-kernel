/-
Copyright (c) 2026 Juan Pablo Traverso Gianini.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module
public import RequestProject.TypedTriangle.ExplicitSampleParams
public import RequestProject.TypedTriangle.UniformCompression
set_option maxHeartbeats 4000000 -- build option (original: -DmaxHeartbeats=1600000; raised)
set_option maxRecDepth 16384 -- build option (original: -DmaxRecDepth=8192; raised)
@[expose] public section
open Finset Classical
noncomputable section
namespace TypedTriangle.ExplicitSample
open Incidence Sampler

def compressionSampleSize (α : ℝ) (h : ℕ) : ℕ :=
  let a := min α 1
  let θ := a/(64*(2:ℝ)^Nat.choose h 2)
  let κ := expConst (a/2) (θ/2) (θ/4)
  let m0 : ℕ := ⌈32/(a*θ^2)⌉₊
  let L := sampleL (a/2) κ (a*θ/16) 1 m0
  let Q := sampleQ (a/2) κ (a*θ/16) 1 m0
  let b := sampleB (a/2) κ (a*θ/16) 1 m0
  L*Q+b

def compressionOrder (α : ℝ) (h : ℕ) : ℕ :=
  ⌈4/min α 1⌉₊+⌈4*h*(2:ℝ)^Nat.choose h 2/min α 1⌉₊+1

theorem sampleOut_windows_of_H3H4_explicit (α : ℝ) (h : ℕ) (hα : 0 < α) :
    ∀ {V I : Type} [Fintype V] (H : Host V I) (F : Set (Multiset I)),
      compressionOrder α h ≤ Fintype.card V → CommonNbrCond H F α → HingeCond H F α h →
      ∃ d : ℕ, ∃ smp : SampleOut H F (compressionSampleSize α h) d,
        (smp.Z.card : ℝ) + 2 + 4 * d < min α 1 * Fintype.card V ∧
        ((smp.Z.card : ℝ) + h + 5 * d) * 2 ^ Nat.choose h 2 ≤
          min α 1 / 2 * Fintype.card V ∧
        (smp.Z.card : ℝ) + d ≤ min α 1 * Fintype.card V / 2 := by
  set a := min α 1 with ha_def
  have ha0 : 0 < a := lt_min hα one_pos
  have ha1 : a ≤ 1 := min_le_right _ _
  have haα : a ≤ α := min_le_left _ _
  set P2 : ℝ := (2 : ℝ) ^ Nat.choose h 2
  have hP2 : 1 ≤ P2 := one_le_pow₀ (by norm_num)
  set θ := a / (64 * P2)
  have hθ : 0 < θ := by positivity
  have hθP : θ * 64 * P2 = a := by
    simp only [θ]; field_simp
  have hθa : θ ≤ a := by nlinarith
  set κ := expConst (a / 2) (θ / 2) (θ / 4)
  have hκ0 : 0 < κ := expConst_pos (by positivity) (by positivity) (by positivity)
  have hκ1 : κ ≤ 1 := expConst_le_one (by linarith)
  let m0 : ℕ := ⌈32/(a*θ^2)⌉₊
  have hm0 : (1-a)^m0 ≤ θ^2/16 := by
    have hh := Nat.le_ceil (32/(a*θ^2))
    have hp := (div_le_iff₀ (by positivity : 0 < a*θ^2)).mp hh
    calc (1-a)^m0 ≤ 1/(1+(m0:ℝ)*a) := one_sub_pow_le_inv ha0.le ha1 m0
      _ ≤ θ^2/16 := (div_le_div_iff₀ (by positivity) (by norm_num)).mpr (by nlinarith [sq_nonneg θ])
  let L := sampleL (a/2) κ (a*θ/16) 1 m0
  let Q := sampleQ (a/2) κ (a*θ/16) 1 m0
  let b := sampleB (a/2) κ (a*θ/16) 1 m0
  obtain ⟨hL,hQ,hcs⟩ := component_sample_explicit.{0} (c:=a/2) (κ:=κ)
    (ε:=a*θ/16) 1 m0 (by positivity) (by linarith) hκ0 hκ1 (by positivity)
  intro V I _ H F hn hH3 hH4
  have hH3' := commonNbrCond_mono hH3 haα
  have hH4' := hingeCond_mono hH4 haα
  set n : ℝ := (Fintype.card V : ℝ)
  change ⌈4/a⌉₊+⌈4*h*P2/a⌉₊+1 ≤ Fintype.card V at hn
  have hnN : 0 < Fintype.card V := by omega
  have hnpos : 0 < n := Nat.cast_pos.2 hnN
  have hn1 : 4 ≤ a * n := by
    have h1 : (⌈4 / a⌉₊ : ℝ) ≤ n := by
      show (⌈4 / a⌉₊ : ℝ) ≤ (Fintype.card V : ℝ)
      exact_mod_cast (by omega : ⌈4 / a⌉₊ ≤ Fintype.card V)
    have h2 := (Nat.le_ceil (4 / a)).trans h1
    rw [div_le_iff₀ ha0] at h2; linarith
  have hn2 : 4 * h * P2 ≤ a * n := by
    have h1 : (⌈4 * h * P2 / a⌉₊ : ℝ) ≤ n := by
      show (⌈4 * h * P2 / a⌉₊ : ℝ) ≤ (Fintype.card V : ℝ)
      exact_mod_cast (by omega : ⌈4 * h * P2 / a⌉₊ ≤ Fintype.card V)
    have h2 := (Nat.le_ceil (4 * h * P2 / a)).trans h1
    rw [div_le_iff₀ ha0] at h2; linarith
  have hθn : 0 ≤ θ * n := by positivity
  obtain ⟨hw1, hw2, -⟩ := windows_of (z := θ * n) (d := θ * n) (hh := h) hθ.le hP2 hθP.le
    hnpos.le hn1 hn2 hθn le_rfl le_rfl
  have hQ' : (1 - a) ^ Q ≤ θ ^ 2 / 16 :=
    (pow_le_pow_of_le_one (by linarith) (by linarith) hQ).trans hm0
  obtain ⟨y, hy⟩ := exists_sample ha0 hH3' hH4' ha1 hθ hθa rfl hnN hw1 hw2 hL hQ' hcs
  set W := baseW y.1
  set D := ⌊θ * n⌋₊
  set bad := univ.filter (fun v => BadRoot H F v y)
  set high := univ.filter (fun x => D < degIn (noThird H F W) x)
  set Z := (bad ∪ high) \ W
  have hZ : (Z.card : ℝ) ≤ θ * n / 4 := by
    have h1 : Z.card ≤ bad.card + high.card :=
      (Finset.card_le_card Finset.sdiff_subset).trans (Finset.card_union_le _ _)
    have h2 : ((Z.card : ℕ) : ℝ) ≤ bad.card + high.card := by exact_mod_cast h1
    exact h2.trans hy
  have hD : (D : ℝ) ≤ θ * n := Nat.floor_le hθn
  obtain ⟨w1, w2, w3⟩ := windows_of (z := Z.card) (d := D) (hh := h) hθ.le hP2 hθP.le
    hnpos.le hn1 hn2 (by positivity) (by linarith) hD
  have hdeg : ∀ x, degIn (badEdges H F W Z) x ≤ D := by
    intro x
    by_cases hx : x ∈ W ∨ x ∈ Z
    · have : degIn (badEdges H F W Z) x = 0 := by
        unfold degIn
        rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
        intro e he hxe
        obtain ⟨-, -, hall, -⟩ := Finset.mem_filter.1 he
        rcases hx with hx | hx
        · exact (hall x hxe).1 hx
        · exact (hall x hxe).2 hx
      omega
    · push_neg at hx
      have hxh : x ∉ high := fun hxh => hx.2
        (Finset.mem_sdiff.2 ⟨Finset.mem_union_right _ hxh, hx.1⟩)
      have : ¬ D < degIn (noThird H F W) x := fun hlt =>
        hxh (Finset.mem_filter.2 ⟨Finset.mem_univ _, hlt⟩)
      exact (degIn_mono (badEdges_subset_noThird W Z) x).trans (by omega)
  refine ⟨D, sampleOut_of_goodRoots H F W Z (card_baseW_le _) Finset.disjoint_sdiff
    (fun v hvW hvZ => goodRoot_of_not_badRoot H F v y fun hb => hvZ
      (Finset.mem_sdiff.2 ⟨Finset.mem_union_left _ (Finset.mem_filter.2 ⟨Finset.mem_univ _, hb⟩),
        hvW⟩)) hdeg, w1, w2, w3⟩


theorem compression_of_H3H4_explicit (α : ℝ) (h : ℕ) (hα : 0 < α)
    {V I : Type} [Fintype V] (H : Host V I) (F : Set (Multiset I))
    (hn : compressionOrder α h ≤ Fintype.card V)
    (hH3 : CommonNbrCond H F α) (hH4 : HingeCond H F α h) :
    Nonempty (Compression H F (compressionSampleSize α h)
      (compH0 (min α 1) (compressionSampleSize α h))
      (compD0 (min α 1) (compressionSampleSize α h))) := by
  obtain ⟨d,smp,hw1,hw2,hw3⟩ := sampleOut_windows_of_H3H4_explicit α h hα H F hn hH3 hH4
  exact compression_of_sample (lt_min hα one_pos)
    (commonNbrCond_mono hH3 (min_le_left α 1))
    (hingeCond_mono hH4 (min_le_left α 1)) smp hw1 hw2 hw3

#print axioms sampleOut_windows_of_H3H4_explicit
#print axioms compression_of_H3H4_explicit
end TypedTriangle.ExplicitSample
