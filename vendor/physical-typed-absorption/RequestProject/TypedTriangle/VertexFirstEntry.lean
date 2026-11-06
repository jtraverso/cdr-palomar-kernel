/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import RequestProject.TypedTriangle.UniformVertexChains

@[expose] public section

/-! Adversarial first entry into quotient stability. Local candidate; NOT kernel-checked. -/

open Finset
noncomputable section
open Classical

namespace TypedTriangle
variable {V I : Type*} [Fintype V]

/-- An abstract counting helper, instantiated with concrete physical chains below. -/
lemma first_entry_of_physical_chain_bound (H : Host V I) (F : Set (Multiset I)) (L b : ℕ)
    (hcount : ∀ (Z : ℕ → Finset V) (hz : ∀ k, Z k ⊆ Z (k+1)),
      (∀ k ≤ L+1, (Z k).card ≤ (L+1)*b) →
      ((Finset.range (L+1)).filter (fun k => ¬ Function.Injective
        (quotMap (F := F) (vertexDeleted_antitone H (hz k)) rfl))).card ≤ L) :
    ∃ A : Finset V, A.card ≤ L*b ∧ ∀ B : Finset V, B.card ≤ b →
      Function.Injective (nestedVertexQuotMap H F A B) := by
  by_contra hnone
  have hbad : ∀ A : Finset V, A.card ≤ L*b →
      ∃ B : Finset V, B.card ≤ b ∧ ¬ Function.Injective (nestedVertexQuotMap H F A B) := by
    intro A hA
    by_contra hnoB
    push_neg at hnoB
    exact hnone ⟨A,hA,hnoB⟩
  let pick : Finset V → Finset V := fun A =>
    if hA : A.card ≤ L*b then Classical.choose (hbad A hA) else ∅
  have hpick (A : Finset V) (hA : A.card ≤ L*b) :
      (pick A).card ≤ b ∧ ¬ Function.Injective (nestedVertexQuotMap H F A (pick A)) := by
    have heq : pick A = Classical.choose (hbad A hA) := by
      dsimp only [pick]
      rw [dif_pos hA]
    rw [heq]
    exact Classical.choose_spec (hbad A hA)
  have hpick_card (A : Finset V) : (pick A).card ≤ b := by
    by_cases hA : A.card ≤ L*b
    · exact (hpick A hA).1
    · simp only [pick,dif_neg hA,Finset.card_empty]; exact Nat.zero_le _
  let Z : ℕ → Finset V := Nat.rec ∅ (fun _ A => A ∪ pick A)
  have hstep (k : ℕ) : Z (k+1)=Z k ∪ pick (Z k) := rfl
  have hz (k : ℕ) : Z k ⊆ Z (k+1) := by rw [hstep]; exact Finset.subset_union_left
  have hc (k : ℕ) : (Z k).card ≤ k*b := by
    induction k with
    | zero => change (∅ : Finset V).card ≤ 0*b; simp
    | succ k ih =>
      rw [hstep]
      calc (Z k ∪ pick (Z k)).card ≤ (Z k).card+(pick (Z k)).card := Finset.card_union_le _ _
        _ ≤ k*b+b := Nat.add_le_add ih (hpick_card _)
        _ = (k+1)*b := by ring
  have hstrict (k : ℕ) (hk : k<L+1) : ¬ Function.Injective
      (quotMap (F := F) (vertexDeleted_antitone H (hz k)) rfl) := by
    have hkL : k ≤ L := by omega
    have hck : (Z k).card ≤ L*b := (hc k).trans (Nat.mul_le_mul_right b hkL)
    have hb := (hpick (Z k) hck).2
    change ¬ Function.Injective (nestedVertexQuotMap H F (Z k) (pick (Z k)))
    exact hb
  have hb := hcount Z hz (fun k hk => (hc k).trans (Nat.mul_le_mul_right b hk))
  have hfull : (Finset.range (L+1)).filter (fun k => ¬ Function.Injective
      (quotMap (F := F) (vertexDeleted_antitone H (hz k)) rfl)) = Finset.range (L+1) := by
    apply Finset.filter_eq_self.2
    intro k hk
    exact hstrict k (Finset.mem_range.1 hk)
  rw [hfull,Finset.card_range] at hb
  omega

/-- A core stable under EVERY deletion of at most b vertices, not just one stable step. -/
theorem physical_vertex_first_entry (α : ℝ) (h : ℕ) (hα : 0 < α) :
    ∃ ε : ℝ, 0 < ε ∧ ∃ d T n₀ : ℕ, 1 ≤ T ∧
      ∀ {V I : Type} [Fintype V] (H : Host V I) (F : Set (Multiset I)),
        n₀ ≤ Fintype.card V → CommonNbrCond H F α → HingeCond H F α h →
        ∀ b : ℕ, (((d+(d+1)*Nat.log 2 T+1)*b : ℕ) : ℝ) ≤ ε*Fintype.card V →
          ∃ A : Finset V, A.card ≤ (d+(d+1)*Nat.log 2 T)*b ∧
            ∀ B : Finset V, B.card ≤ b → Function.Bijective (nestedVertexQuotMap H F A B) := by
  obtain ⟨ε,hε,d,T,n₀,hT,hcontrol⟩ := physical_vertex_chain_control α h hα
  refine ⟨ε,hε,d,T,n₀,hT,fun {V I} _ H F hn hH3 hH4 b hbudget => ?_⟩
  obtain ⟨hs,hchain⟩ := hcontrol H F hn hH3 hH4
  let L : ℕ := d+(d+1)*Nat.log 2 T
  have hbudget' : (((L+1)*b : ℕ) : ℝ) ≤ ε*Fintype.card V := hbudget
  have hc : ∀ (Z : ℕ → Finset V) (hz : ∀ k, Z k ⊆ Z (k+1)),
      (∀ k ≤ L+1, (Z k).card ≤ (L+1)*b) →
      ((Finset.range (L+1)).filter (fun k => ¬ Function.Injective
        (quotMap (F := F) (vertexDeleted_antitone H (hz k)) rfl))).card ≤ L := by
    intro Z hz hZ
    apply hchain Z hz (L+1)
    intro k hk
    have hck : ((Z k).card : ℝ) ≤ (((L+1)*b : ℕ) : ℝ) := by exact_mod_cast hZ k hk
    exact hck.trans hbudget'
  obtain ⟨A,hA,hstable⟩ := first_entry_of_physical_chain_bound H F L b hc
  have hAR : (A.card : ℝ) ≤ ε*Fintype.card V := by
    have hle : A.card ≤ (L+1)*b := hA.trans (Nat.mul_le_mul_right b (Nat.le_succ L))
    exact (show (A.card : ℝ) ≤ (((L+1)*b : ℕ) : ℝ) by exact_mod_cast hle).trans hbudget'
  refine ⟨A,hA,fun B hB => ⟨hstable B hB,?_⟩⟩
  have hble : b ≤ (L+1)*b := by nlinarith
  have hBR : (B.card : ℝ) ≤ ε*Fintype.card V := by
    have hle : B.card ≤ (L+1)*b := hB.trans hble
    exact (show (B.card : ℝ) ≤ (((L+1)*b : ℕ) : ℝ) by exact_mod_cast hle).trans hbudget'
  exact hs A B hAR hBR

/-- Exact lattice persistence for local vectors is the injectivity already constructed. -/
lemma nestedVertexQuotMap_injective_iff (H : Host V I) (F : Set (Multiset I)) (A B : Finset V) :
    Function.Injective (nestedVertexQuotMap H F A B) ↔
      ∀ x ∈ localGroup (vertexDeleted H (A ∪ B)) F,
        x ∈ lattice (vertexDeleted H A) F → x ∈ lattice (vertexDeleted H (A ∪ B)) F :=
  quotMap_injective_iff (vertexDeleted_antitone H Finset.subset_union_left) rfl

/-- First entry gives physical integer persistence, without assuming the demand is local afterwards. -/
theorem physical_vertex_first_entry_lattice (α : ℝ) (h : ℕ) (hα : 0 < α) :
    ∃ ε : ℝ, 0 < ε ∧ ∃ d T n₀ : ℕ, 1 ≤ T ∧
      ∀ {V I : Type} [Fintype V] (H : Host V I) (F : Set (Multiset I)),
        n₀ ≤ Fintype.card V → CommonNbrCond H F α → HingeCond H F α h →
        ∀ b : ℕ, (((d+(d+1)*Nat.log 2 T+1)*b : ℕ) : ℝ) ≤ ε*Fintype.card V →
          ∃ A : Finset V, A.card ≤ (d+(d+1)*Nat.log 2 T)*b ∧
            ∀ B : Finset V, B.card ≤ b → ∀ x ∈ lattice (vertexDeleted H A) F,
              (∀ e, TouchZ B e → x e=0) → x ∈ lattice (vertexDeleted H (A ∪ B)) F := by
  obtain ⟨ε₀,hε₀,d,T,N₀,hT,hentry⟩ := physical_vertex_first_entry α h hα
  obtain ⟨ε₁,hε₁,N₁,hwin⟩ := uniform_nested_vertex_windows α h hα
  let ε : ℝ := min ε₀ ε₁
  have hε : 0 < ε := lt_min hε₀ hε₁
  refine ⟨ε,hε,d,T,max N₀ N₁,hT,fun {V I} _ H F hn hH3 hH4 b hbudget => ?_⟩
  let L : ℕ := d+(d+1)*Nat.log 2 T
  have hbudget₀ : (((L+1)*b : ℕ) : ℝ) ≤ ε₀*Fintype.card V :=
    hbudget.trans (mul_le_mul_of_nonneg_right (min_le_left _ _) (by positivity))
  obtain ⟨A,hA,hbij⟩ := hentry H F ((le_max_left _ _).trans hn) hH3 hH4 b hbudget₀
  have hsmall : ∀ C : Finset V, C.card ≤ (L+1)*b → (C.card : ℝ) ≤ ε₁*Fintype.card V := by
    intro C hC
    have hc : (C.card : ℝ) ≤ (((L+1)*b : ℕ) : ℝ) := by exact_mod_cast hC
    exact (hc.trans hbudget).trans (mul_le_mul_of_nonneg_right (min_le_right _ _) (by positivity))
  refine ⟨A,hA,fun B hB x hx hz => ?_⟩
  have hAc : A.card ≤ (L+1)*b := hA.trans (Nat.mul_le_mul_right b (Nat.le_succ L))
  have hBc : B.card ≤ (L+1)*b := hB.trans (by nlinarith)
  obtain ⟨hA3,hA4,hB1,hB2⟩ := hwin A B ((le_max_right _ _).trans hn) (hsmall A hAc) (hsmall B hBc)
  have hxM : x ∈ localGroup (vertexDeleted H (A ∪ B)) F :=
    localGroup_nested_of_vanish hα hH3 hH4 A B hA3 hA4 hB1 hB2
      (lattice_le_localGroup (vertexDeleted H A) F hx) hz
  exact (nestedVertexQuotMap_injective_iff H F A B).1 (hbij B hB).1 x hxM hx

end TypedTriangle
