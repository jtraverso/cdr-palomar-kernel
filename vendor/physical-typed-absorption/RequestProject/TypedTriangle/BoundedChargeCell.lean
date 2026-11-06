/-
Copyright (c) 2026 Juan Pablo Traverso Gianini.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module
public import RequestProject.TypedTriangle.IntegerChargeRealization
public import RequestProject.TypedTriangle.NativeCompressionData
set_option maxHeartbeats 4000000 -- build option (original: -DmaxHeartbeats=1600000; raised)
set_option maxRecDepth 16384 -- build option (original: -DmaxRecDepth=8192; raised)
@[expose] public section
open Finset Classical
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace TypedTriangle.ChargePolar
variable {V I : Type*} [Fintype V]

/-- The roots required to realize a bounded integer charge are themselves
bounded; no root-set hypothesis needs to be supplied by a bank construction. -/
theorem bounded_profile_roots (x : Sym2 V → ℤ) (k : ℕ)
    (hx : (∑ e, |x e|) ≤ (k:ℤ)) :
    ∃ U : Finset V, U.card ≤ 2*k ∧ ∀ e, x e ≠ 0 → ∀ v ∈ e, v ∈ U := by
  let S := univ.filter fun e => x e ≠ 0
  have hS : S.card ≤ k := by
    have hsum : (S.card:ℤ) ≤ ∑ e ∈ S, |x e| := by
      calc (S.card:ℤ) = ∑ _e ∈ S, (1:ℤ) := by simp
        _ ≤ ∑ e ∈ S, |x e| := sum_le_sum fun e he => by
          have hz := abs_pos.mpr (mem_filter.mp he).2
          omega
    have hall : (∑ e ∈ S, |x e|) = ∑ e, |x e| := by
      change (∑ e ∈ univ.filter (fun e => x e ≠ 0), |x e|) = _
      rw [sum_filter]
      apply sum_congr rfl
      intro e _
      by_cases he : x e = 0 <;> simp [he]
    rw [hall] at hsum
    exact_mod_cast hsum.trans hx
  refine ⟨S.biUnion Sym2.toFinset,?_,?_⟩
  · calc (S.biUnion Sym2.toFinset).card ≤ ∑ e ∈ S, e.toFinset.card := card_biUnion_le
      _ ≤ ∑ _e ∈ S, 2 := sum_le_sum fun e _ => by rw [Sym2.card_toFinset]; split_ifs <;> omega
      _ = 2*S.card := by simp [mul_comm]
      _ ≤ 2*k := Nat.mul_le_mul_left 2 hS
  · intro e he v hv
    exact mem_biUnion.mpr ⟨e,mem_filter.mpr ⟨mem_univ _,he⟩,Sym2.mem_toFinset.mpr hv⟩

/-- Every nonzero coordinate of an actual local profile has an allowed
triangle. This uses the integer local module itself, not its saturation. -/
lemma local_profile_hasTri (H : Host V I) (F : Set (Multiset I))
    (x : Sym2 V → ℤ) (hx : x ∈ Composition.localProfile H.G H.lab F)
    (e : Sym2 V) (he : x e ≠ 0) : HasTri H F e := by
  by_contra h
  exact he (localGroup_zero_of_not_hasTri hx h)

/-- Uniform physical cell from an actual bounded relative charge. All root and
size windows are discharged before the host; the only forbidden-edge budget
is a fixed positive fraction of the host order. -/
theorem bounded_local_charge_cell (α β : ℝ) (h k : ℕ) (hα : 0 < α) (hβ : 0 < β) :
    ∃ ε : ℝ, 0 < ε ∧ ∃ E n₀ : ℕ,
      ∀ {V I : Type} [Fintype V] (H : Host V I) (F : Set (Multiset I))
        (J : SimpleGraph V), n₀ ≤ Fintype.card V → J ≤ H.G →
      CommonNbrCond H F α → HingeCond H F α h →
      CommonNbrCond (⟨J,H.lab⟩ : Host V I) F β →
      ∀ (x : Sym2 V → ℤ), x ∈ Composition.localProfile J H.lab F →
      x ∈ lattice H F → (∑ e, |x e|) ≤ (k:ℤ) →
      ∀ (B : Finset (Sym2 V)) (b : ℕ), (∀ v, SelSimul.edeg B v ≤ b) →
      (b:ℝ) ≤ ε*Fintype.card V →
      ∃ A Y : Finset (Sym2 V), Y.card ≤ 4*k ∧ Y ⊆ edges (⟨J,H.lab⟩ : Host V I) ∧
        Disjoint Y B ∧ Disjoint A B ∧ Disjoint A Y ∧
        Basal H F (A∪Y) ∧ Basal H F A ∧ (A∪Y).card ≤ E ∧
        ind Y-x ∈ lattice (⟨J,H.lab⟩ : Host V I) F := by
  obtain ⟨K,nA,hCell⟩ := integer_charge_cell α h hα
  let Ub := 5*k+3*(K*(4*k))+K*(4*k)*(2*h-2)+3*(K*(4*k))*(2*h-3)
  let a₀ : ℕ := 5*k+2
  let b₀ : ℕ := Ub+h+3
  let P : ℝ := 2^(Nat.choose h 2)
  have hP : 1 ≤ P := by dsimp [P]; exact one_le_pow₀ (by norm_num)
  have hPpos : 0 < P := by linarith
  let ε := min (β/8) (α/(40*P))
  have hε : 0 < ε := lt_min (by positivity) (by positivity)
  refine ⟨ε,hε,K*(4*k)*(4*(2*h-2).choose 2+6)+4*k,
    nA+⌈4*(a₀:ℝ)/β⌉₊+⌈8*(b₀:ℝ)*P/α⌉₊+1,?_⟩
  intro V I _ H F J hn hJG h3 h4 hJ3 x hx hxG hnorm B b hB hb
  have hnpos : (0:ℝ) < Fintype.card V := by exact_mod_cast (by omega : 0 < Fintype.card V)
  have hna : nA ≤ Fintype.card V := by omega
  have ha₀ : (a₀:ℝ) ≤ β/4*Fintype.card V := by
    have hh : 4*(a₀:ℝ)/β ≤ Fintype.card V := (Nat.le_ceil _).trans (by exact_mod_cast (by omega : ⌈4*(a₀:ℝ)/β⌉₊ ≤ Fintype.card V))
    rw [div_le_iff₀ hβ] at hh
    linarith
  have hb₀ : (b₀:ℝ)*P ≤ α/8*Fintype.card V := by
    have hh : 8*(b₀:ℝ)*P/α ≤ Fintype.card V := (Nat.le_ceil _).trans (by exact_mod_cast (by omega : ⌈8*(b₀:ℝ)*P/α⌉₊ ≤ Fintype.card V))
    rw [div_le_iff₀ hα] at hh
    linarith
  have hbβ : (b:ℝ) ≤ β/8*Fintype.card V :=
    hb.trans (mul_le_mul_of_nonneg_right (min_le_left _ _) hnpos.le)
  have hbP : (b:ℝ)*P ≤ α/40*Fintype.card V := by
    have hh := hb.trans (mul_le_mul_of_nonneg_right (min_le_right _ _) hnpos.le)
    have hh' := mul_le_mul_of_nonneg_right hh hPpos.le
    have he : α/(40*P)*Fintype.card V*P = α/40*Fintype.card V := by field_simp <;> ring
    rwa [he] at hh'
  have hb' : (b:ℝ) ≤ α/40*Fintype.card V :=
    (le_mul_of_one_le_right (by positivity) hP).trans hbP
  have hb₀' : (b₀:ℝ) ≤ α/8*Fintype.card V :=
    (le_mul_of_one_le_right (by positivity) hP).trans hb₀
  obtain ⟨U,hU,hroots⟩ := bounded_profile_roots x k hnorm
  have hwin : ((U.card+3*k+2*b+2:ℕ):ℝ) < β*Fintype.card V := by
    have hu : ((U.card+3*k+2:ℕ):ℝ) ≤ a₀ := by exact_mod_cast (by dsimp [a₀]; omega : U.card+3*k+2 ≤ a₀)
    push_cast
    push_cast at hu
    nlinarith
  have hbudget : U.card+3*k+3*(K*(4*k))+K*(4*k)*(2*h-2)+3*(K*(4*k))*(2*h-3) ≤ Ub := by
    dsimp [Ub]
    omega
  have hw1 : (Ub:ℝ)+3+4*b < α*Fintype.card V := by
    have he : (Ub:ℝ)+3 ≤ b₀ := by exact_mod_cast (by dsimp [b₀]; omega : Ub+3 ≤ b₀)
    nlinarith
  have hw2 : ((Ub:ℝ)+1+h+5*b)*2^(Nat.choose h 2) ≤ α/2*Fintype.card V := by
    change ((Ub:ℝ)+1+h+5*b)*P ≤ _
    have he : (Ub:ℝ)+1+h ≤ b₀ := by dsimp [b₀]; push_cast; linarith
    have hh := mul_le_mul_of_nonneg_right he hPpos.le
    nlinarith
  exact hCell H J F β hna h3 h4 hJG hJ3 x U k hnorm
    (local_profile_hasTri ⟨J,H.lab⟩ F x hx) hroots hxG B b Ub hB hwin hbudget hw1 hw2
end TypedTriangle.ChargePolar
