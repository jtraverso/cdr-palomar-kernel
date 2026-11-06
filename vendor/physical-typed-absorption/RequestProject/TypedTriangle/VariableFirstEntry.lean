/-
Copyright (c) 2026 Juan Pablo Traverso Gianini.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import RequestProject.TypedTriangle.VertexFirstEntry
set_option maxHeartbeats 4000000 -- build option (original: -DmaxHeartbeats=1600000; raised)
set_option maxRecDepth 16384 -- build option (original: -DmaxRecDepth=8192; raised)

@[expose] public section

open Finset Classical
noncomputable section

namespace TypedTriangle

variable {V I : Type*} [Fintype V]

/-- The amount spent strictly before stage `r` of variable-radius first entry. -/
def priorBudget (b : ℕ → ℕ) (r : ℕ) : ℕ :=
  ∑ j ∈ Finset.range r, b j

/-- First entry with a separate deletion radius at each stage. The successful
stage `r` pays only earlier radii, not its own radius. -/
theorem first_entry_variable_radius (H : Host V I) (F : Set (Multiset I))
    (L : ℕ) (b : ℕ → ℕ)
    (hcount : ∀ (Z : ℕ → Finset V) (hz : ∀ k, Z k ⊆ Z (k+1)),
      (∀ k ≤ L+1, (Z k).card ≤ priorBudget b (L+1)) →
      ((Finset.range (L+1)).filter (fun k => ¬ Function.Injective
        (quotMap (F := F) (vertexDeleted_antitone H (hz k)) rfl))).card ≤ L) :
    ∃ r ≤ L, ∃ A : Finset V,
      A.card ≤ priorBudget b r ∧
      ∀ B : Finset V, B.card ≤ b r →
        Function.Injective (nestedVertexQuotMap H F A B) := by
  by_contra hnone
  have hbad : ∀ r ≤ L, ∀ A : Finset V, A.card ≤ priorBudget b r →
      ∃ B : Finset V, B.card ≤ b r ∧
        ¬ Function.Injective (nestedVertexQuotMap H F A B) := by
    intro r hr A hA
    by_contra hnoB
    push_neg at hnoB
    exact hnone ⟨r,hr,A,hA,hnoB⟩
  let pick : ℕ → Finset V → Finset V := fun r A =>
    if hr : r ≤ L ∧ A.card ≤ priorBudget b r then
      Classical.choose (hbad r hr.1 A hr.2)
    else ∅
  have hpick (r : ℕ) (hr : r ≤ L) (A : Finset V)
      (hA : A.card ≤ priorBudget b r) :
      (pick r A).card ≤ b r ∧
        ¬ Function.Injective (nestedVertexQuotMap H F A (pick r A)) := by
    have heq : pick r A = Classical.choose (hbad r hr A hA) := by
      dsimp only [pick]
      rw [dif_pos ⟨hr,hA⟩]
    rw [heq]
    exact Classical.choose_spec (hbad r hr A hA)
  have hpick_card (r : ℕ) (A : Finset V) : (pick r A).card ≤ b r := by
    by_cases hr : r ≤ L ∧ A.card ≤ priorBudget b r
    · exact (hpick r hr.1 A hr.2).1
    · simp only [pick,dif_neg hr,Finset.card_empty]
      exact Nat.zero_le _
  let Z : ℕ → Finset V := Nat.rec ∅ (fun r A => A ∪ pick r A)
  have hstep (r : ℕ) : Z (r+1) = Z r ∪ pick r (Z r) := rfl
  have hz (r : ℕ) : Z r ⊆ Z (r+1) := by
    rw [hstep]
    exact Finset.subset_union_left
  have hc (r : ℕ) : (Z r).card ≤ priorBudget b r := by
    induction r with
    | zero => simp [Z,priorBudget]
    | succ r ih =>
      rw [hstep]
      calc
        (Z r ∪ pick r (Z r)).card ≤ (Z r).card + (pick r (Z r)).card :=
          Finset.card_union_le _ _
        _ ≤ priorBudget b r + b r := Nat.add_le_add ih (hpick_card r _)
        _ = priorBudget b (r+1) := by simp [priorBudget, Finset.sum_range_succ]
  have hstrict (r : ℕ) (hr : r < L+1) :
      ¬ Function.Injective
        (quotMap (F := F) (vertexDeleted_antitone H (hz r)) rfl) := by
    have hrL : r ≤ L := by omega
    have hb := (hpick r hrL (Z r) (hc r)).2
    change ¬ Function.Injective (nestedVertexQuotMap H F (Z r) (pick r (Z r))) at hb
    exact hb
  have hZ (r : ℕ) (hr : r ≤ L+1) : (Z r).card ≤ priorBudget b (L+1) :=
    (hc r).trans (Finset.sum_le_sum_of_subset_of_nonneg
      (Finset.range_mono hr) (by simp))
  have hb := hcount Z hz hZ
  have hfull : (Finset.range (L+1)).filter (fun r => ¬ Function.Injective
      (quotMap (F := F) (vertexDeleted_antitone H (hz r)) rfl)) =
      Finset.range (L+1) := by
    apply Finset.filter_eq_self.2
    intro r hr
    exact hstrict r (Finset.mem_range.1 hr)
  rw [hfull,Finset.card_range] at hb
  omega

/-- Original H3--H4 produce a stable physical quotient at one of the
prescribed radii. The number of vertices removed before the successful
stage is bounded by the sum of strictly earlier radii. -/
theorem physical_vertex_first_entry_variable (α : ℝ) (h : ℕ) (hα : 0 < α) :
    ∃ ε : ℝ, 0 < ε ∧ ∃ d T n₀ : ℕ, 1 ≤ T ∧
      ∀ {V I : Type} [Fintype V] (H : Host V I) (F : Set (Multiset I)),
        n₀ ≤ Fintype.card V → CommonNbrCond H F α → HingeCond H F α h →
        ∀ b : ℕ → ℕ,
          (priorBudget b (d+(d+1)*Nat.log 2 T+1) : ℝ) ≤ ε*Fintype.card V →
          ∃ r ≤ d+(d+1)*Nat.log 2 T, ∃ A : Finset V,
            A.card ≤ priorBudget b r ∧
            ∀ B : Finset V, B.card ≤ b r →
              Function.Bijective (nestedVertexQuotMap H F A B) := by
  obtain ⟨ε,hε,d,T,n₀,hT,hcontrol⟩ := physical_vertex_chain_control α h hα
  refine ⟨ε,hε,d,T,n₀,hT,fun {V I} _ H F hn hH3 hH4 b hbudget => ?_⟩
  obtain ⟨hs,hchain⟩ := hcontrol H F hn hH3 hH4
  let L : ℕ := d+(d+1)*Nat.log 2 T
  have hbudget' : (priorBudget b (L+1) : ℝ) ≤ ε*Fintype.card V := hbudget
  have hc : ∀ (Z : ℕ → Finset V) (hz : ∀ k, Z k ⊆ Z (k+1)),
      (∀ k ≤ L+1, (Z k).card ≤ priorBudget b (L+1)) →
      ((Finset.range (L+1)).filter (fun k => ¬ Function.Injective
        (quotMap (F := F) (vertexDeleted_antitone H (hz k)) rfl))).card ≤ L := by
    intro Z hz hZ
    apply hchain Z hz (L+1)
    intro k hk
    have hck : ((Z k).card : ℝ) ≤ priorBudget b (L+1) := by
      exact_mod_cast hZ k hk
    exact hck.trans hbudget'
  obtain ⟨r,hr,A,hA,hstable⟩ := first_entry_variable_radius H F L b hc
  have hAR : (A.card : ℝ) ≤ ε*Fintype.card V := by
    have hpr : priorBudget b r ≤ priorBudget b (L+1) :=
      Finset.sum_le_sum_of_subset_of_nonneg
        (Finset.range_mono (by omega : r ≤ L+1)) (by simp)
    exact (show (A.card : ℝ) ≤ priorBudget b (L+1) by
      exact_mod_cast hA.trans hpr).trans hbudget'
  refine ⟨r,hr,A,hA,fun B hB => ⟨hstable B hB,?_⟩⟩
  have hb_le : b r ≤ priorBudget b (L+1) := by
    have hrR : r ∈ Finset.range (L+1) := Finset.mem_range.2 (by omega)
    exact Finset.single_le_sum (fun _ _ => Nat.zero_le _) hrR
  have hBR : (B.card : ℝ) ≤ ε*Fintype.card V := by
    exact (show (B.card : ℝ) ≤ priorBudget b (L+1) by
      exact_mod_cast hB.trans hb_le).trans hbudget'
  exact hs A B hAR hBR

/-- The stable variable-radius quotient gives integer lattice persistence for
demands supported away from the later deletion. -/
theorem physical_vertex_first_entry_lattice_variable (α : ℝ) (h : ℕ) (hα : 0 < α) :
    ∃ ε : ℝ, 0 < ε ∧ ∃ d T n₀ : ℕ, 1 ≤ T ∧
      ∀ {V I : Type} [Fintype V] (H : Host V I) (F : Set (Multiset I)),
        n₀ ≤ Fintype.card V → CommonNbrCond H F α → HingeCond H F α h →
        ∀ b : ℕ → ℕ,
          (priorBudget b (d+(d+1)*Nat.log 2 T+1) : ℝ) ≤ ε*Fintype.card V →
          ∃ r ≤ d+(d+1)*Nat.log 2 T, ∃ A : Finset V,
            A.card ≤ priorBudget b r ∧
            ∀ B : Finset V, B.card ≤ b r →
              ∀ x ∈ lattice (vertexDeleted H A) F,
                (∀ e, TouchZ B e → x e = 0) →
                  x ∈ lattice (vertexDeleted H (A ∪ B)) F := by
  obtain ⟨ε₀,hε₀,d,T,N₀,hT,hentry⟩ := physical_vertex_first_entry_variable α h hα
  obtain ⟨ε₁,hε₁,N₁,hwin⟩ := uniform_nested_vertex_windows α h hα
  let ε := min ε₀ ε₁
  have hε : 0 < ε := lt_min hε₀ hε₁
  refine ⟨ε,hε,d,T,max N₀ N₁,hT,fun {V I} _ H F hn h3 h4 b hbudget => ?_⟩
  have hbudget₀ : (priorBudget b (d+(d+1)*Nat.log 2 T+1) : ℝ) ≤
      ε₀*Fintype.card V :=
    hbudget.trans (mul_le_mul_of_nonneg_right (min_le_left _ _) (by positivity))
  obtain ⟨r,hr,A,hA,hstable⟩ :=
    hentry H F ((le_max_left _ _).trans hn) h3 h4 b hbudget₀
  refine ⟨r,hr,A,hA,fun B hB x hx hz => ?_⟩
  have htotal : (priorBudget b (d+(d+1)*Nat.log 2 T+1) : ℝ) ≤
      ε₁*Fintype.card V :=
    hbudget.trans (mul_le_mul_of_nonneg_right (min_le_right _ _) (by positivity))
  have hAr : A.card ≤ priorBudget b (d+(d+1)*Nat.log 2 T+1) :=
    hA.trans (Finset.sum_le_sum_of_subset_of_nonneg
      (Finset.range_mono (by omega : r ≤ d+(d+1)*Nat.log 2 T+1)) (by simp))
  have hBr : B.card ≤ priorBudget b (d+(d+1)*Nat.log 2 T+1) := by
    have hrR : r ∈ Finset.range (d+(d+1)*Nat.log 2 T+1) :=
      Finset.mem_range.2 (by omega)
    exact hB.trans (Finset.single_le_sum (fun _ _ => Nat.zero_le _) hrR)
  have hAε : (A.card : ℝ) ≤ ε₁*Fintype.card V :=
    (show (A.card : ℝ) ≤ priorBudget b (d+(d+1)*Nat.log 2 T+1) by
      exact_mod_cast hAr).trans htotal
  have hBε : (B.card : ℝ) ≤ ε₁*Fintype.card V :=
    (show (B.card : ℝ) ≤ priorBudget b (d+(d+1)*Nat.log 2 T+1) by
      exact_mod_cast hBr).trans htotal
  obtain ⟨hA3,hA4,hB1,hB2⟩ :=
    hwin A B ((le_max_right _ _).trans hn) hAε hBε
  have hxM : x ∈ localGroup (vertexDeleted H (A ∪ B)) F :=
    localGroup_nested_of_vanish hα h3 h4 A B
      hA3 hA4 hB1 hB2
      (lattice_le_localGroup (vertexDeleted H A) F hx) hz
  exact (nestedVertexQuotMap_injective_iff H F A B).1
    (hstable B hB).1 x hxM hx

#print axioms first_entry_variable_radius
#print axioms physical_vertex_first_entry_variable
#print axioms physical_vertex_first_entry_lattice_variable

end TypedTriangle
