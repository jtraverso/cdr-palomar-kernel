/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import RequestProject.S10K.SourceOutcome
set_option maxHeartbeats 4000000 -- build option (original: -DmaxHeartbeats=1600000; raised)
set_option maxRecDepth 16384 -- build option (original: -DmaxRecDepth=8192; raised)

@[expose] public section

/-!
# V23: every positive-probability outcome of a source process is valid

`reach_valid`: under the ORIGINAL H3 (`CommonNbrCond`) and H4 (`HingeCond`), `h ≥ 6`,
`α > 0` and `n ≥ n₀ = 2(12h+3)2^(h choose 2)/α`, every outcome of positive weight of the
process of a permitted source `T = {u,v,a}` decodes into choices satisfying `SrcValid`, so
the recursion `srcCert_spec` applies to it.
-/

open Finset

noncomputable section
open Classical

namespace S10V23.Proc

open TypedTriangle.SparseEdge S10V22 S10V23

variable {V I : Type*} [Fintype V] {G : SimpleGraph V} {lab : V → I} {F : Set (Multiset I)}
  {al : ℝ} {hh : ℕ}

omit [Fintype V] in
lemma HSk_mono [Fintype V] (u v a : V) (ω : Fin 12 → Opt V) {k k' : ℕ} (h : k ≤ k') :
    HSk u v a ω k ⊆ HSk u v a ω k' := by
  unfold HSk
  refine Finset.union_subset_union (subset_refl _) (Finset.biUnion_subset_biUnion_of_subset_left _ ?_)
  intro j hj; simp at hj ⊢; omega

lemma mem_HSk_inl (u v a : V) {ω : Fin 12 → Opt V} {j k : ℕ} {y : V}
    (he : G12 ω j = Sum.inl y) (hjk : j < k) : y ∈ HSk u v a ω k :=
  vsO_subset_HSk u v a ω hjk (by rw [he]; simp [vsO])

lemma support_subset_HSk (u v a : V) {ω : Fin 12 → Opt V} {j k : ℕ} {J : Finset (Sym2 V)}
    (he : G12 ω j = Sum.inr J) (hjk : j < k) : support J ⊆ HSk u v a ω k := by
  intro x hx
  exact vsO_subset_HSk u v a ω hjk (by rw [he]; simpa [vsO] using hx)

lemma T_mem_HSk (u v a : V) (ω : Fin 12 → Opt V) (k : ℕ) :
    u ∈ HSk u v a ω k ∧ v ∈ HSk u v a ω k ∧ a ∈ HSk u v a ω k :=
  ⟨T_subset_HSk u v a ω k (by simp), T_subset_HSk u v a ω k (by simp),
    T_subset_HSk u v a ω k (by simp)⟩

/-- The third vertex `x1` of `Q1` is exposed once `J1` is. -/
lemma x1_mem_HSk {u v a c : V} {ω : Fin 12 → Opt V} {J1 : Finset (Sym2 V)}
    (huv : u ≠ v) (hua : u ≠ a) (hva : v ≠ a) (hJ1 : IsHinge G lab F u v a c J1)
    (he : G12 ω 4 = Sum.inr J1) {k : ℕ} (hk : 4 < k) :
    x1 G lab F u v a J1 ∈ HSk u v a ω k ∧ x2 G lab F u v a J1 ∈ HSk u v a ω k := by
  obtain ⟨⟨hQ1, -, -, -, -, hQ1eq⟩, ⟨hQ2, -, -, -, -, hQ2eq⟩⟩ :=
    Q_facts huv hua hva hJ1 (G := G) (lab := lab) (F := F)
  have key : ∀ Q ∈ dA G lab F u v a J1, Q ⊆ HSk u v a ω k := by
    intro Q hQ
    rw [dA_eq] at hQ
    refine (subset_support_of_mem_decOf hQ).trans ((support_union_wedge J1 u v a).trans ?_)
    refine Finset.union_subset (support_subset_HSk u v a he hk) ?_
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    obtain ⟨h1, h2, h3⟩ := T_mem_HSk u v a ω k
    rcases hx with rfl | rfl | rfl <;> assumption
  refine ⟨key _ hQ1 ?_, key _ hQ2 ?_⟩
  · rw [hQ1eq]; simp
  · rw [hQ2eq]; simp

/-- **Validity of every positive-probability outcome** (from H3, H4 and `n ≥ n₀`). -/
theorem reach_valid {u v a : V} (hT : IsAllowed G lab F {u, v, a})
    (H3 : CommonNbrCond G lab F al) (H4 : HingeCond G lab F al hh) (hal : 0 < al)
    (hh6 : 6 ≤ hh) (hn0 : nZero al hh ≤ (Fintype.card V : ℝ)) {ω : Fin 12 → Opt V}
    (hw : Expo.wt (opts G lab F al hh u v a) 12 [] ω ≠ 0) :
    SrcValid G lab F u v a (ob1 u ω) (ob2 u ω) (ob3 u ω) (oc u ω) (oc1 u ω) (oc2 u ω)
      (oJ1 ω) (oJ2 ω) (oJ3 ω) (oJ4 ω) (oJ5 ω) (oJ6 ω) := by
  obtain ⟨huv, hua, hva⟩ := distinct_of_card_three hT.1
  set n := (Fintype.card V : ℝ) with hn_def
  have hn : 0 < n := lt_of_lt_of_le (by unfold nZero; positivity) hn0
  have h2R : 2 * ((12 * hh + 3 : ℕ) : ℝ) ≤ al * n := by
    have h1 : (1 : ℝ) ≤ 2 ^ (hh.choose 2) := one_le_pow₀ (by norm_num)
    have := hn0; unfold nZero at this
    rw [div_le_iff₀ hal] at this
    push_cast
    nlinarith
  have hsmall : ∀ j < 12, (vsO (G12 ω j)).card ≤ hh := fun j hj =>
    vsO_card_le (by omega) u v a j _ _ (step_mem hw j hj)
  have hcard : ∀ k ≤ 12, ((HSk u v a ω k).card : ℝ) ≤ 12 * hh + 3 := HSk_card hsmall
  have hex : ∀ k ≤ 12, 2 * ((HSk u v a ω k).card : ℝ) ≤ al * n := by
    intro k hk; have := hcard k hk; push_cast at h2R; linarith
  have hTa : IsAllowed G lab F {u, a, v} := by rw [triple_comm1]; exact hT
  have hTb : IsAllowed G lab F {v, a, u} := by rw [triple_comm2]; exact hT
  have hex1 : 2 * (({a} : Finset V).card : ℝ) ≤ al * n := by
    simp only [Finset.card_singleton, Nat.cast_one]; push_cast at h2R; linarith
  have hex1' : ∀ x : V, 2 * (({x} : Finset V).card : ℝ) ≤ al * n := by
    intro x; simp only [Finset.card_singleton, Nat.cast_one]; push_cast at h2R; linarith
  have Tu : ∀ k, u ∈ HSk u v a ω k := fun k => (T_mem_HSk u v a ω k).1
  have Tv : ∀ k, v ∈ HSk u v a ω k := fun k => (T_mem_HSk u v a ω k).2.1
  have Ta : ∀ k, a ∈ HSk u v a ω k := fun k => (T_mem_HSk u v a ω k).2.2
  -- pivots
  have s0 := step_mem hw 0 (by norm_num)
  simp only [stepOpts] at s0
  obtain ⟨b1, e0, hb1, hb1a⟩ := apex_mem H3 hal hn hT (hex1' a) s0
  have s1 := step_mem hw 1 (by norm_num)
  simp only [stepOpts] at s1
  obtain ⟨b2, e1, hb2, hb2v⟩ := apex_mem H3 hal hn hTa (hex1' v) s1
  have s2 := step_mem hw 2 (by norm_num)
  simp only [stepOpts] at s2
  obtain ⟨b3, e2, hb3, hb3u⟩ := apex_mem H3 hal hn hTb (hex1' u) s2
  simp only [Finset.mem_singleton] at hb1a hb2v hb3u
  obtain ⟨-, hub1, hvb1⟩ := distinct_of_card_three hb1.1
  obtain ⟨-, hub2, hab2⟩ := distinct_of_card_three hb2.1
  obtain ⟨-, hvb3, hab3⟩ := distinct_of_card_three hb3.1
  have eb1 : ob1 u ω = b1 := by simp [ob1, e0, gv]
  have eb2 : ob2 u ω = b2 := by simp [ob2, e1, gv]
  have eb3 : ob3 u ω = b3 := by simp [ob3, e2, gv]
  -- bridge
  have s3 := step_mem hw 3 (by norm_num)
  simp only [stepOpts] at s3
  obtain ⟨c, e3, hc, hcH⟩ := apex_mem H3 hal hn hT (hex 3 (by norm_num)) s3
  have ec : oc u ω = c := by simp [oc, e3, gv]
  have hcu : u ≠ c := fun h => hcH (h ▸ Tu 3)
  have hcv : v ≠ c := fun h => hcH (h ▸ Tv 3)
  have hca : a ≠ c := fun h => hcH (h ▸ Ta 3)
  have hcb1 : c ≠ b1 := fun h => hcH (h ▸ mem_HSk_inl u v a e0 (by norm_num))
  -- J1
  have s4 := step_mem hw 4 (by norm_num)
  simp only [stepOpts, restr, Nat.reduceLT, ite_true] at s4
  rw [show gv u (G12 ω 3) = c by rw [e3]; rfl] at s4
  have r4 : ({u, v, a, c} : Finset V) ⊆ HSk u v a ω 4 := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl | rfl | rfl
    exacts [Tu 4, Tv 4, Ta 4, mem_HSk_inl u v a e3 (by norm_num)]
  obtain ⟨J1, e4, hJ1, -, -⟩ := hinge_mem H4 hal hn0 huv hua hva hcu hcv hca hT hc r4
    (hcard 4 (by norm_num)) s4
  have eJ1 : oJ1 ω = J1 := by simp [oJ1, e4, gJ]
  -- J2
  have s5 := step_mem hw 5 (by norm_num)
  simp only [stepOpts, restr, Nat.reduceLT, ite_true] at s5
  rw [show gv u (G12 ω 3) = c by rw [e3]; rfl, show gv u (G12 ω 0) = b1 by rw [e0]; rfl] at s5
  have r5 : ({u, v, c, b1} : Finset V) ⊆ HSk u v a ω 5 := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl | rfl | rfl
    exacts [Tu 5, Tv 5, mem_HSk_inl u v a e3 (by norm_num), mem_HSk_inl u v a e0 (by norm_num)]
  obtain ⟨J2, e5, hJ2, hJ2f, -⟩ := hinge_mem H4 hal hn0 huv hcu hcv hub1 hvb1 hcb1 hc hb1 r5
    (hcard 5 (by norm_num)) s5
  have eJ2 : oJ2 ω = J2 := by simp [oJ2, e5, gJ]
  have haJ2 : a ∉ support J2 := by
    intro ha
    refine Finset.disjoint_left.1 hJ2f ha (Finset.mem_sdiff.2 ⟨Ta 5, ?_⟩)
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
    exact ⟨Ne.symm hua, Ne.symm hva, hca, Ne.symm hb1a⟩
  obtain ⟨hx1H, hx2H⟩ := x1_mem_HSk huv hua hva hJ1 e4 (k := 6) (by norm_num)
  obtain ⟨hx2H9, -⟩ := (⟨(x1_mem_HSk huv hua hva hJ1 e4 (k := 9) (by norm_num)).2, trivial⟩ :
    x2 G lab F u v a J1 ∈ HSk u v a ω 9 ∧ True)
  obtain ⟨⟨-, -, -, hQ1a, hx1T, hQ1eq⟩, ⟨-, -, -, hQ2a, hx2T, hQ2eq⟩⟩ :=
    Q_facts huv hua hva hJ1 (G := G) (lab := lab) (F := F)
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hx1T hx2T
  have hx1a : IsAllowed G lab F {u, a, x1 G lab F u v a J1} := hQ1eq ▸ hQ1a
  have hx2a : IsAllowed G lab F {v, a, x2 G lab F u v a J1} := hQ2eq ▸ hQ2a
  refine ⟨hT, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [eb1]; exact hb1
  · rw [eb1]; exact hb1a
  · rw [eb2]; exact hb2
  · rw [eb2]; exact hb2v
  · rw [eb3]; exact hb3
  · rw [eb3]; exact hb3u
  · rw [ec]; simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
    exact ⟨Ne.symm hcu, Ne.symm hcv, Ne.symm hca⟩
  · rw [ec, eJ1]; exact hJ1
  · rw [ec, eb1, eJ2]; exact hJ2
  · rw [eJ2]; exact haJ2
  · -- first transport
    rw [eJ1, eb2]
    intro hs
    have s6 := step_mem hw 6 (by norm_num)
    simp only [stepOpts, restr, Nat.reduceLT, ite_true] at s6
    rw [show gJ (G12 ω 4) = J1 by rw [e4]; rfl, show gv u (G12 ω 1) = b2 by rw [e1]; rfl,
      if_neg hs] at s6
    obtain ⟨c1, e6, hc1, hc1H⟩ := apex_mem H3 hal hn hTa (hex 6 (by norm_num)) s6
    have ec1 : oc1 u ω = c1 := by simp [oc1, e6, gv]
    have hc1u : u ≠ c1 := fun h => hc1H (h ▸ Tu 6)
    have hc1v : v ≠ c1 := fun h => hc1H (h ▸ Tv 6)
    have hc1a : a ≠ c1 := fun h => hc1H (h ▸ Ta 6)
    have hx1c1 : x1 G lab F u v a J1 ≠ c1 := fun h => hc1H (h ▸ hx1H)
    have hc1b2 : c1 ≠ b2 := fun h => hc1H (h ▸ mem_HSk_inl u v a e1 (by norm_num))
    -- J3
    have s7 := step_mem hw 7 (by norm_num)
    simp only [stepOpts, restr, Nat.reduceLT, ite_true] at s7
    rw [show gJ (G12 ω 4) = J1 by rw [e4]; rfl, show gv u (G12 ω 1) = b2 by rw [e1]; rfl,
      if_neg hs, show gv u (G12 ω 6) = c1 by rw [e6]; rfl] at s7
    have r7 : ({u, a, x1 G lab F u v a J1, c1} : Finset V) ⊆ HSk u v a ω 7 := by
      intro x hx
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl | rfl | rfl
      exacts [Tu 7, Ta 7, HSk_mono u v a ω (by norm_num) hx1H,
        mem_HSk_inl u v a e6 (by norm_num)]
    obtain ⟨J3, e7, hJ3, hJ3f, -⟩ := hinge_mem H4 hal hn0 hua (Ne.symm hx1T.1)
      (Ne.symm hx1T.2.2) hc1u hc1a hx1c1 hx1a hc1 r7 (hcard 7 (by norm_num)) s7
    -- J4
    have s8 := step_mem hw 8 (by norm_num)
    simp only [stepOpts, restr, Nat.reduceLT, ite_true] at s8
    rw [show gJ (G12 ω 4) = J1 by rw [e4]; rfl, show gv u (G12 ω 1) = b2 by rw [e1]; rfl,
      if_neg hs, show gv u (G12 ω 6) = c1 by rw [e6]; rfl] at s8
    have r8 : ({u, a, c1, b2} : Finset V) ⊆ HSk u v a ω 8 := by
      intro x hx
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl | rfl | rfl
      exacts [Tu 8, Ta 8, mem_HSk_inl u v a e6 (by norm_num), mem_HSk_inl u v a e1 (by norm_num)]
    obtain ⟨J4, e8, hJ4, hJ4f, -⟩ := hinge_mem H4 hal hn0 hua hc1u hc1a hub2 hab2 hc1b2
      hc1 hb2 r8 (hcard 8 (by norm_num)) s8
    have eJ3 : oJ3 ω = J3 := by simp [oJ3, e7, gJ]
    have eJ4 : oJ4 ω = J4 := by simp [oJ4, e8, gJ]
    rw [ec1, eJ3, eJ4]
    refine ⟨?_, hJ3, ?_, hJ4, ?_⟩
    · simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
      exact ⟨Ne.symm hc1u, Ne.symm hc1v, Ne.symm hc1a⟩
    · intro hv
      refine Finset.disjoint_left.1 hJ3f hv (Finset.mem_sdiff.2 ⟨Tv 7, ?_⟩)
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
      exact ⟨Ne.symm huv, hva, fun h => hx1T.2.1 h.symm, hc1v⟩
    · intro hv
      refine Finset.disjoint_left.1 hJ4f hv (Finset.mem_sdiff.2 ⟨Tv 8, ?_⟩)
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
      exact ⟨Ne.symm huv, hva, hc1v, fun h => hb2v h.symm⟩
  · -- second transport
    rw [eJ1, eb3]
    intro hs
    have s9 := step_mem hw 9 (by norm_num)
    simp only [stepOpts, restr, Nat.reduceLT, ite_true] at s9
    rw [show gJ (G12 ω 4) = J1 by rw [e4]; rfl, show gv u (G12 ω 2) = b3 by rw [e2]; rfl,
      if_neg hs] at s9
    obtain ⟨c2, e9, hc2, hc2H⟩ := apex_mem H3 hal hn hTb (hex 9 (by norm_num)) s9
    have ec2 : oc2 u ω = c2 := by simp [oc2, e9, gv]
    have hc2u : u ≠ c2 := fun h => hc2H (h ▸ Tu 9)
    have hc2v : v ≠ c2 := fun h => hc2H (h ▸ Tv 9)
    have hc2a : a ≠ c2 := fun h => hc2H (h ▸ Ta 9)
    have hx2c2 : x2 G lab F u v a J1 ≠ c2 := fun h => hc2H (h ▸ hx2H9)
    have hc2b3 : c2 ≠ b3 := fun h => hc2H (h ▸ mem_HSk_inl u v a e2 (by norm_num))
    -- J5
    have s10 := step_mem hw 10 (by norm_num)
    simp only [stepOpts, restr, Nat.reduceLT, ite_true] at s10
    rw [show gJ (G12 ω 4) = J1 by rw [e4]; rfl, show gv u (G12 ω 2) = b3 by rw [e2]; rfl,
      if_neg hs, show gv u (G12 ω 9) = c2 by rw [e9]; rfl] at s10
    have r10 : ({v, a, x2 G lab F u v a J1, c2} : Finset V) ⊆ HSk u v a ω 10 := by
      intro x hx
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl | rfl | rfl
      exacts [Tv 10, Ta 10, HSk_mono u v a ω (by norm_num) hx2H9,
        mem_HSk_inl u v a e9 (by norm_num)]
    obtain ⟨J5, e10, hJ5, hJ5f, -⟩ := hinge_mem H4 hal hn0 hva (Ne.symm hx2T.2.1)
      (Ne.symm hx2T.2.2) hc2v hc2a hx2c2 hx2a hc2 r10 (hcard 10 (by norm_num)) s10
    -- J6
    have s11 := step_mem hw 11 (by norm_num)
    simp only [stepOpts, restr, Nat.reduceLT, ite_true] at s11
    rw [show gJ (G12 ω 4) = J1 by rw [e4]; rfl, show gv u (G12 ω 2) = b3 by rw [e2]; rfl,
      if_neg hs, show gv u (G12 ω 9) = c2 by rw [e9]; rfl] at s11
    have r11 : ({v, a, c2, b3} : Finset V) ⊆ HSk u v a ω 11 := by
      intro x hx
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl | rfl | rfl
      exacts [Tv 11, Ta 11, mem_HSk_inl u v a e9 (by norm_num), mem_HSk_inl u v a e2 (by norm_num)]
    obtain ⟨J6, e11, hJ6, hJ6f, -⟩ := hinge_mem H4 hal hn0 hva hc2v hc2a hvb3 hab3 hc2b3
      hc2 hb3 r11 (hcard 11 (by norm_num)) s11
    have eJ5 : oJ5 ω = J5 := by simp [oJ5, e10, gJ]
    have eJ6 : oJ6 ω = J6 := by simp [oJ6, e11, gJ]
    rw [ec2, eJ5, eJ6]
    refine ⟨?_, hJ5, ?_, hJ6, ?_⟩
    · simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
      exact ⟨Ne.symm hc2u, Ne.symm hc2v, Ne.symm hc2a⟩
    · intro hu
      refine Finset.disjoint_left.1 hJ5f hu (Finset.mem_sdiff.2 ⟨Tu 10, ?_⟩)
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
      exact ⟨huv, hua, fun h => hx2T.1 h.symm, hc2u⟩
    · intro hu
      refine Finset.disjoint_left.1 hJ6f hu (Finset.mem_sdiff.2 ⟨Tu 11, ?_⟩)
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
      exact ⟨huv, hua, hc2u, fun h => hb3u h.symm⟩

end S10V23.Proc
