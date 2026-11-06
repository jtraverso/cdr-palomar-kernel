/-
Copyright (c) 2026 Juan Pablo Traverso Gianini.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module
public import RequestProject.TypedTriangle.NativeSeedNibble
set_option maxHeartbeats 4000000 -- build option (original: -DmaxHeartbeats=1600000; raised)
set_option maxRecDepth 16384 -- build option (original: -DmaxRecDepth=8192; raised)
@[expose] public section
open Finset Classical
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace PartitionedTriangleAbsorption.Nibble

/-- The first actual round absorbs a small INITIAL load error. All subsequent
rounds use the already checked `IterInv.step`, with its unchanged schedule. -/
theorem IterInv.first_near {V : Type} [Fintype V] [DecidableEq V] {m : ℕ}
    (S : TriSystem V m) (B : Finset (Sym2 V)) (w : Fin m → ℝ)
    (γ θ c a β δ ε : ℝ) (ω : Fin m → Bool)
    (hB : ∀ i, triEdges (S.tri i) ⊆ B) (hγ : 0 ≤ γ) (hγ8 : γ ≤ 8)
    (hgood : RoundGood S B w β δ γ θ ε ω)
    (hload : (1+5*γ)*δ+5*γ*β+ε ≤ c*a) :
    IterInv S B w γ θ c a 1
      (univ.filter (fun i => triEdges (S.tri i) ⊆ S.untouched B ω))
      (S.untouched B ω) (S.waste ω) (S.packing ω) := by
  have hPE : edgesOf S (S.packing ω) = S.packEdges ω := rfl
  have hT : S.touched ω ⊆ B := biUnion_subset.mpr fun i _ => hB i
  have hP : S.packEdges ω ⊆ B := (S.packEdges_subset_touched ω).trans hT
  have hU : S.untouched B ω ⊆ B := sdiff_subset
  have hUP : Disjoint (S.untouched B ω) (S.packEdges ω) :=
    disjoint_of_subset_right (S.packEdges_subset_touched ω) sdiff_disjoint
  refine ⟨?_,?_,?_,?_,?_,?_,?_⟩
  · intro i hi; exact (mem_filter.mp hi).2
  · intro i hi j hj hne; exact S.packing_edge_disjoint ω hi hj hne
  · rw [hPE]; exact hUP.symm
  · rw [hPE,(S.residual_identity B hB ω).1]
  · intro v; simpa using hgood.2.1 v
  · intro v
    have hs : (star (S.untouched B ω) v).card + (star (S.packEdges ω) v).card ≤
        (star B v).card := by
      rw [←card_union_of_disjoint (show Disjoint
        (star (S.untouched B ω) v) (star (S.packEdges ω) v)
        from hUP.mono (filter_subset _ _) (filter_subset _ _))]
      exact card_le_card (union_subset (star_mono hU v) (star_mono hP v))
    have hsR : ((star (S.untouched B ω) v).card:ℝ) + (star (S.packEdges ω) v).card ≤
        (star B v).card := by exact_mod_cast hs
    by_cases ht : θ*(Fintype.card V:ℝ) ≤ (star B v).card
    · right
      have hp := hgood.1 v ht
      have hd : ((star B v).card:ℝ) ≤ Fintype.card V := by exact_mod_cast card_star_le B v
      have hc : 0 ≤ 1-γ/8 := by linarith
      have hh := mul_le_mul_of_nonneg_left hd hc
      simp only [pow_one]
      nlinarith
    · left
      push Not at ht
      have hz : (0:ℝ) ≤ (star (S.packEdges ω) v).card := by positivity
      linarith
  · intro e he
    have heq : aliveLoad S
        (univ.filter (fun i => triEdges (S.tri i) ⊆ S.untouched B ω))
        (fun i => Real.exp (2*γ*(1:ℕ)) * w i) e = Real.exp (2*γ)*availLoad S B w e ω := by
      simp only [aliveLoad,availLoad,TriSystem.edgeTris,filter_filter,Nat.cast_one,mul_one,mul_sum]
      rw [filter_congr (q := fun i => e ∈ triEdges (S.tri i) ∧
        triEdges (S.tri i) ⊆ S.untouched B ω) (fun _ _ => and_comm)]
    rw [heq]
    simpa only [Nat.cast_one,mul_one,pow_one] using (hgood.2.2 e he).trans hload

end PartitionedTriangleAbsorption.Nibble

namespace PartitionedTriangleAbsorption.Nibble

/-- A small approximate unit load suffices for an arbitrarily small local
leftover. The permitted initial error is fixed BEFORE the host. No integrality
or exact fractional decomposition of that host is required. -/
theorem nibble_packing_near (b η : ℝ) (hb : 0 < b) (hη0 : 0 < η) (hη1 : η ≤ 1) :
    ∃ ε : ℝ, 0 < ε ∧ ∃ N : ℕ,
      ∀ (V : Type) [Fintype V] [DecidableEq V], N ≤ Fintype.card V →
      ∀ (m : ℕ) (S : TriSystem V m) (B : Finset (Sym2 V)) (w : Fin m → ℝ),
        (∀ i, triEdges (S.tri i) ⊆ B) → (∀ i, 0 ≤ w i) →
        (∀ i, w i ≤ b / Fintype.card V) → (∀ e ∈ B, |S.load w e - 1| ≤ ε) →
        ∃ P : Finset (Fin m), IsPacking S P ∧
          ∀ v, ((star (B \ edgesOf S P) v).card : ℝ) ≤ η * Fintype.card V := by
  obtain ⟨γ, r, hγ0, hγ1, hr1, hdeg, hwaste⟩ := schedule_params η hη0 hη1
  set a : ℝ := 1 + 5 * γ with ha
  have ha1 : 1 ≤ a := by rw [ha]; linarith
  have hr0 : (0 : ℝ) < r := by exact_mod_cast hr1
  set c : ℝ := 1 / (8 * r * a ^ r) with hc
  have hapos : 0 < a ^ r := by positivity
  have hc0 : 0 < c := by positivity
  have hcr : c * r * a ^ r = 1 / 8 := by rw [hc]; field_simp
  set bmax : ℝ := b * Real.exp (2 * γ * r) with hbmax
  have hbmax0 : 0 < bmax := by positivity
  obtain ⟨N0, hN0⟩ := near_load_round bmax γ (η / 2) (c / 2) hbmax0 hγ0 hγ1 (by positivity)
    (by positivity)
  obtain ⟨N1, hN1⟩ := near_load_round bmax γ (η / 2) (c / 4) hbmax0 hγ0 hγ1
    (by positivity) (by positivity)
  have hcsmall : c ≤ 1 / 8 := by
    have hpow : 1 ≤ a^r := one_le_pow₀ ha1
    have hrR : (1:ℝ) ≤ r := by exact_mod_cast hr1
    rw [hc,div_le_iff₀ (by positivity)]
    nlinarith
  refine ⟨c/8,by positivity,max (max (max N0 N1) 1) ⌈20 * γ * bmax / c⌉₊, ?_⟩
  intro V _ _ hN m S B w hB hw0 hwb hload
  have hN0' : N0 ≤ Fintype.card V := le_trans (le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) (le_max_left _ _)) hN
  have hn1 : 1 ≤ Fintype.card V := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hN
  have hnR : (1 : ℝ) ≤ Fintype.card V := by exact_mod_cast hn1
  have hnpos : (0 : ℝ) < Fintype.card V := by linarith
  have hnbig : 20 * γ * bmax / c ≤ Fintype.card V :=
    (Nat.le_ceil _).trans (by exact_mod_cast le_trans (le_max_right _ _) hN)
  rw [div_le_iff₀ hc0] at hnbig
  have key : ∀ j, 1 ≤ j → j ≤ r → ∃ (s : Finset (Fin m)) (Bj W : Finset (Sym2 V)) (P : Finset (Fin m)),
      IterInv S B w γ (η / 2) c a j s Bj W P := by
    intro j hj1
    induction j, hj1 using Nat.le_induction with
    | base =>
      intro _
      have hn1' : N1 ≤ Fintype.card V :=
        (le_trans (le_trans (le_trans (le_max_right _ _) (le_max_left _ _))
          (le_max_left _ _)) hN)
      have he1 : c/8 ≤ 1/4 := by linarith
      obtain ⟨_,ω,_,hgood,_⟩ := hN1 V hn1' m S B w b (c/8) hb
        (by rw [hbmax]; exact le_mul_of_one_le_right hb.le (Real.one_le_exp (by positivity)))
        (by positivity) he1 hB hw0 hwb
        (fun e he => ⟨by linarith [(abs_le.mp (hload e he)).1],
          by linarith [(abs_le.mp (hload e he)).2]⟩)
      have hβ : 5*γ*(b/Fintype.card V) ≤ c/4 := by
        rw [mul_div_assoc',div_le_iff₀ hnpos]
        have hbb : b ≤ bmax := by
          rw [hbmax]; exact le_mul_of_one_le_right hb.le (Real.one_le_exp (by positivity))
        nlinarith [mul_le_mul_of_nonneg_left hbb hγ0.le]
      have hl : (1+5*γ)*(c/8)+5*γ*(b/Fintype.card V)+c/4 ≤ c*a := by
        have hcγ : γ*c ≤ c/128 := by nlinarith [hc0.le]
        have hca : c ≤ c*a := le_mul_of_one_le_right hc0.le ha1
        nlinarith
      exact ⟨_,_,_,_,IterInv.first_near S B w γ (η/2) c a _ _ _ ω hB hγ0.le
        (by linarith) hgood hl⟩
    | succ j hj1 ih =>
      intro hj
      obtain ⟨s, Bj, W, P, hI⟩ := ih (by omega)
      have hjr : (j : ℝ) ≤ r := by exact_mod_cast (by omega : j ≤ r)
      set bj : ℝ := b * Real.exp (2 * γ * j) with hbj
      have hbj0 : 0 < bj := by positivity
      have hbjmax : bj ≤ bmax :=
        mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by nlinarith)) hb.le
      have hδ0 : 0 ≤ c * j * a ^ j := by positivity
      have hδ1 : c * j * a ^ j ≤ 1 / 4 := by
        have h1 : a ^ j ≤ a ^ r := pow_le_pow_right₀ ha1 (by omega)
        have h2 : c * j ≤ c * r := mul_le_mul_of_nonneg_left hjr hc0.le
        have h3 : c * j * a ^ j ≤ c * r * a ^ r :=
          mul_le_mul h2 h1 (by positivity) (by positivity)
        linarith
      have hβ : 5 * γ * (bj / Fintype.card V) ≤ c / 2 := by
        rw [mul_div_assoc', div_le_iff₀ hnpos]
        have : γ * bj ≤ γ * bmax := mul_le_mul_of_nonneg_left hbjmax hγ0.le
        nlinarith
      obtain ⟨-, ω, -, hgood, -⟩ := hN0 V hN0' s.card (S.reindex s) Bj
        (fun k => Real.exp (2 * γ * j) * w (reidx s k)) bj (c * j * a ^ j) hbj0 hbjmax hδ0 hδ1
        (fun k => hI.alive_sub _ (reidx_mem s k))
        (fun k => mul_nonneg (Real.exp_pos _).le (hw0 _))
        (fun k => by
          calc Real.exp (2 * γ * j) * w (reidx s k)
              ≤ Real.exp (2 * γ * j) * (b / Fintype.card V) :=
                mul_le_mul_of_nonneg_left (hwb _) (Real.exp_pos _).le
            _ = bj / Fintype.card V := by rw [hbj]; ring)
        (fun e he => by
          have h := hI.load e he
          rw [reindex_load S s (fun i => Real.exp (2 * γ * j) * w i) e]
          change |aliveLoad S s (fun i => Real.exp (2 * γ * j) * w i) e - 1| ≤ _ at h
          unfold aliveLoad at h
          exact ⟨by linarith [(abs_le.mp h).1], by linarith [(abs_le.mp h).2]⟩)
      exact ⟨_, _, _, _, hI.step hγ0.le (by linarith) (by rw [ha]) hc0.le ω _ hβ hgood⟩
  obtain ⟨s, Bj, W, P, hI⟩ := key r hr1 le_rfl
  refine ⟨P, hI.pack, fun v => ?_⟩
  have h1 : (star (B \ edgesOf S P) v).card ≤ (star Bj v).card + (star W v).card :=
    (card_le_card (star_mono hI.cover v)).trans (card_star_union_le _ _ v)
  have h1R : ((star (B \ edgesOf S P) v).card : ℝ) ≤ (star Bj v).card + (star W v).card := by
    exact_mod_cast h1
  have h2 : ((star Bj v).card : ℝ) ≤ η / 2 * Fintype.card V := by
    rcases hI.deg v with h | h
    · exact h.le
    · exact h.trans (mul_le_mul_of_nonneg_right hdeg hnpos.le)
  have h3 : ((star W v).card : ℝ) ≤ η / 4 * Fintype.card V := by
    refine (hI.waste v).trans ?_
    have := mul_le_mul_of_nonneg_right hwaste hnpos.le
    linarith
  nlinarith


end PartitionedTriangleAbsorption.Nibble
