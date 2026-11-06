/-
Copyright (c) 2026 Juan Pablo Traverso Gianini.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module
public import RequestProject.TypedTriangle.ExplicitKernelLinearBound
public import RequestProject.TypedTriangle.GroupingAtomKernelLift
public import RequestProject.TypedTriangle.IntLift
set_option maxHeartbeats 4000000 -- build option (original: -DmaxHeartbeats=1600000; raised)
set_option maxRecDepth 16384 -- build option (original: -DmaxRecDepth=8192; raised)
@[expose] public section

open Finset Submodule Classical
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 800000

namespace TypedTriangle.IntLiftExplicit
open GroupingExplicit QuotientBox IntLift

private abbrev LiftIndex {d : ℕ} (κ : Type) (S : Finset (Fin d → ℤ)) := κ ⊕ (S ⊕ S)

private def columns {κ : Type} {d : ℕ} (Z : κ → Fin d → ℤ)
    (S : Finset (Fin d → ℤ)) : LiftIndex κ S → Fin d → ℤ :=
  Sum.elim Z (Sum.elim (fun s => -s.val) Subtype.val)

private theorem certificate_exists {κ : Type} [Fintype κ] {d : ℕ}
    (Z : κ → Fin d → ℤ) (m : κ → ℕ) (S : Finset (Fin d → ℤ))
    (hm : (∑ i,(m i : ℤ) • Z i) ∈ span ℤ (S : Set (Fin d → ℤ))) :
    ∃ u : LiftIndex κ S → ℕ, (∀ i,u (Sum.inl i) = m i) ∧
      (∑ i,(u i : ℤ) • columns Z S i) = 0 := by
  obtain ⟨c,hc⟩ := Submodule.mem_span_finset'.mp hm
  let p : S → ℕ := fun s => (c s).toNat
  let q : S → ℕ := fun s => (-c s).toNat
  have hParts : (∑ s : S,(p s : ℤ) • s.val) -
      (∑ s : S,(q s : ℤ) • s.val) = ∑ i,(m i : ℤ) • Z i := by
    rw [← sum_sub_distrib]
    calc
      (∑ s : S,((p s : ℤ) • s.val - (q s : ℤ) • s.val)) =
          ∑ s : S,c s • s.val := by
        apply sum_congr rfl
        intro s _
        rw [← sub_smul]
        have h : (p s : ℤ) - (q s : ℤ) = c s := by dsimp [p,q]; omega
        rw [h]
      _ = _ := hc
  refine ⟨Sum.elim m (Sum.elim p q),fun _ => rfl,?_⟩
  simp only [Fintype.sum_sum_type,columns,Sum.elim_inl,Sum.elim_inr,
    smul_neg,sum_neg_distrib]
  rw [← hParts]
  abel

/-- A minimum certificate for fixed demand has bounded total multiplicity.
Only cycles with zero demand are excluded; the demand need not be atomic. -/
theorem bounded_lattice_certificate {κ : Type} [Fintype κ] {d B R : ℕ}
    (Z : κ → Fin d → ℤ) (m : κ → ℕ) (S : Finset (Fin d → ℤ))
    (hZ : ∀ i k,|Z i k| ≤ (B : ℤ)) (hS : S ⊆ box d R)
    (hm : (∑ i,(m i : ℤ) • Z i) ∈ span ℤ (S : Set (Fin d → ℤ))) :
    ∃ c : S → ℤ, (∑ s : S,c s • s.val) = ∑ i,(m i : ℤ) • Z i ∧
      (∑ s : S,|c s|) ≤ (kernelBound d (max B R) : ℤ) * (∑ i,m i : ℕ) := by
  let P : ℕ → Prop := fun n => ∃ u : LiftIndex κ S → ℕ,
    (∀ i,u (Sum.inl i) = m i) ∧
      (∑ i,(u i : ℤ) • columns Z S i) = 0 ∧ ∑ i,u i = n
  have hP : ∃ n,P n := by
    obtain ⟨u,hproj,hzero⟩ := certificate_exists Z m S hm
    exact ⟨∑ i,u i,u,hproj,hzero,rfl⟩
  obtain ⟨u,hproj,hzero,hnorm⟩ := Nat.find_spec hP
  have hMin : ∀ w : LiftIndex κ S → ℕ,
      (∀ i,w (Sum.inl i) = m i) →
      (∑ i,(w i : ℤ) • columns Z S i) = 0 → Nat.find hP ≤ ∑ i,w i := by
    intro w hp hz
    exact Nat.find_min' hP ⟨w,hp,hz,rfl⟩
  let demand : Finset (LiftIndex κ S) := univ.image Sum.inl
  have hDemandSum : ∀ w : LiftIndex κ S → ℕ,
      (∑ i ∈ demand,w i) = ∑ i : κ,w (Sum.inl i) := by
    intro w
    dsimp [demand]
    rw [Finset.sum_image]
    intro i _ j _ h
    exact Sum.inl.inj h
  have hDemand : ∀ v : LiftIndex κ S → ℕ, v ≤ u → v ≠ 0 →
      (∑ i,(v i : ℤ) • columns Z S i) = 0 → 0 < ∑ i ∈ demand,v i := by
    intro v hv hv0 hzv
    rw [hDemandSum]
    by_contra h
    have hsum0 : (∑ i : κ,v (Sum.inl i)) = 0 := Nat.eq_zero_of_not_pos h
    have hFirst : ∀ i : κ,v (Sum.inl i) = 0 := by
      intro i
      have hi := single_le_sum (fun j _ => Nat.zero_le (v (Sum.inl j))) (mem_univ i)
      omega
    let w : LiftIndex κ S → ℕ := fun i => u i-v i
    have hwproj : ∀ i,w (Sum.inl i) = m i := by
      intro i
      simpa only [w,hFirst i,Nat.sub_zero] using hproj i
    have hwzero : (∑ i,(w i : ℤ) • columns Z S i) = 0 := by
      have heq : (∑ i,(w i : ℤ) • columns Z S i) =
          (∑ i,(u i : ℤ) • columns Z S i) - ∑ i,(v i : ℤ) • columns Z S i := by
        rw [← sum_sub_distrib]
        apply sum_congr rfl
        intro i _
        rw [show w i = u i-v i from rfl,Nat.cast_sub (hv i),sub_smul]
      rw [heq,hzero,hzv,sub_self]
    have hWsplit : (∑ i,w i) + (∑ i,v i) = ∑ i,u i := by
      rw [← sum_add_distrib]
      exact sum_congr rfl (fun i _ => Nat.sub_add_cancel (hv i))
    have hvpos : 0 < ∑ i,v i := by
      obtain ⟨i,hi⟩ := Function.ne_iff.mp hv0
      have hi' : 0 < v i := Nat.pos_of_ne_zero (by simpa only [Pi.zero_apply] using hi)
      exact hi'.trans_le (single_le_sum (fun j _ => Nat.zero_le (v j)) (mem_univ i))
    have hwb := hMin w hwproj hwzero
    omega
  have hColumns : ∀ i k,|columns Z S i k| ≤ (max B R : ℕ) := by
    intro i k
    cases i with
    | inl i => exact (hZ i k).trans (by exact_mod_cast Nat.le_max_left B R)
    | inr s =>
      cases s with
      | inl s =>
        simpa only [columns,Sum.elim_inr,Sum.elim_inl,Pi.neg_apply,abs_neg]
          using (mem_box.mp (hS s.property) k).trans (by exact_mod_cast Nat.le_max_right B R)
      | inr s => exact (mem_box.mp (hS s.property) k).trans (by exact_mod_cast Nat.le_max_right B R)
  have hBound := kernel_flag_bound d (max B R) (columns Z S) u demand hColumns hzero hDemand
  rw [hDemandSum] at hBound
  have hProjSum : (∑ i : κ,u (Sum.inl i)) = ∑ i,m i := sum_congr rfl (fun i _ => hproj i)
  rw [hProjSum] at hBound
  let c : S → ℤ := fun s => (u (Sum.inr (Sum.inl s)) : ℤ) - u (Sum.inr (Sum.inr s))
  have hSplit : (∑ i,(m i : ℤ) • Z i) -
      (∑ s : S,(u (Sum.inr (Sum.inl s)) : ℤ) • s.val) +
      (∑ s : S,(u (Sum.inr (Sum.inr s)) : ℤ) • s.val) = 0 := by
    simpa only [Fintype.sum_sum_type,columns,Sum.elim_inl,Sum.elim_inr,
      smul_neg,sum_neg_distrib,hproj,sub_eq_add_neg,add_assoc] using hzero
  refine ⟨c,?_,?_⟩
  · have hc : (∑ s : S,c s • s.val) =
        (∑ s : S,(u (Sum.inr (Sum.inl s)) : ℤ) • s.val) -
        (∑ s : S,(u (Sum.inr (Sum.inr s)) : ℤ) • s.val) := by
      simp only [c,sub_smul,sum_sub_distrib]
    rw [hc]
    apply sub_eq_zero.mp
    convert congrArg Neg.neg hSplit using 1 <;> abel
  · have hcost : (∑ s : S,|c s|) ≤ (∑ i,u i : ℕ) := by
      have hs : (∑ s : S,|c s|) ≤
          (∑ s : S,(u (Sum.inr (Sum.inl s)) : ℤ)) +
          ∑ s : S,(u (Sum.inr (Sum.inr s)) : ℤ) := by
        rw [← sum_add_distrib]
        apply sum_le_sum
        intro s _
        dsimp only [c]
        calc
          |(u (Sum.inr (Sum.inl s)) : ℤ) - u (Sum.inr (Sum.inr s))| ≤
              |(u (Sum.inr (Sum.inl s)) : ℤ)| + |(u (Sum.inr (Sum.inr s)) : ℤ)| := by
            simpa only [sub_eq_add_neg,abs_neg] using
              abs_add_le (u (Sum.inr (Sum.inl s)) : ℤ) (-(u (Sum.inr (Sum.inr s)) : ℤ))
          _ = _ := by simp
      push_cast
      simp only [Fintype.sum_sum_type] at *
      have hp : 0 ≤ ∑ i : κ,(u (Sum.inl i) : ℤ) := sum_nonneg (fun _ _ => Nat.cast_nonneg _)
      linarith
    exact hcost.trans (by exact_mod_cast hBound)

/-- Integer lifting with a computable constant and no rank or saturation premise. -/
theorem int_lift_finset_explicit {d R : ℕ} (S : Finset (Fin d → ℤ))
    (hS : S ⊆ box d R) (v : Fin d → ℤ)
    (hv : v ∈ span ℤ (S : Set (Fin d → ℤ))) :
    ∃ c : S → ℤ, (∑ s : S,c s • s.val) = v ∧
      (∑ s : S,|c s|) ≤ (kernelBound d (max 1 R) : ℤ) * IntLift.l1 v := by
  let Z : Fin d ⊕ Fin d → Fin d → ℤ :=
    Sum.elim (fun j => Pi.single j 1) (fun j => -Pi.single j 1)
  let m : Fin d ⊕ Fin d → ℕ := Sum.elim (fun j => (v j).toNat) (fun j => (-v j).toNat)
  have hZ : ∀ i k,|Z i k| ≤ (1 : ℤ) := by
    intro i k
    cases i with
    | inl j => simp only [Z,Sum.elim_inl,Pi.single_apply]; split_ifs <;> norm_num
    | inr j => simp only [Z,Sum.elim_inr,Pi.neg_apply,abs_neg,Pi.single_apply]; split_ifs <;> norm_num
  have hCharge : (∑ i,(m i : ℤ) • Z i) = v := by
    ext j
    simp only [Fintype.sum_sum_type,m,Z,Sum.elim_inl,Sum.elim_inr,
      Finset.sum_apply,Pi.add_apply,Pi.smul_apply,Pi.neg_apply,smul_eq_mul,Pi.single_apply]
    simp only [mul_ite,mul_one,mul_zero,sum_ite_eq',sum_ite_eq,mem_univ,ite_true,mul_neg,sum_neg_distrib]
    omega
  have hCost : ((∑ i,m i : ℕ) : ℤ) = IntLift.l1 v := by
    simp only [Fintype.sum_sum_type,m,Sum.elim_inl,Sum.elim_inr,
      Nat.cast_add,Nat.cast_sum,IntLift.l1]
    rw [← sum_add_distrib]
    apply sum_congr rfl
    intro j _
    by_cases hj : 0 ≤ v j
    · rw [abs_of_nonneg hj]
      omega
    · rw [abs_of_nonpos (le_of_not_ge hj)]
      omega
  obtain ⟨c,hc,hcb⟩ := bounded_lattice_certificate (B := 1) (R := R) Z m S hZ hS (hCharge.symm ▸ hv)
  exact ⟨c,hc.trans hCharge,by simpa only [hCost] using hcb⟩

theorem int_lift_uniform_explicit (d R : ℕ) :
    ∀ {ι : Type*} [Fintype ι] (A : ι → Fin d → ℤ), (∀ i j,|A i j| ≤ R) →
      ∀ v ∈ span ℤ (Set.range A), ∃ a : ι → ℤ,
        (∑ i,a i • A i) = v ∧
        (∑ i,|a i|) ≤ (kernelBound d (max 1 R) : ℤ) * IntLift.l1 v := by
  intro ι _ A hA v hv
  let S := univ.image A
  have hS : S ⊆ box d R := by
    intro s hs
    obtain ⟨i,_,rfl⟩ := mem_image.mp hs
    exact mem_box.mpr (hA i)
  have hspan : (S : Set (Fin d → ℤ)) = Set.range A := by simp [S]
  rw [← hspan] at hv
  obtain ⟨c,hc,hcb⟩ := int_lift_finset_explicit S hS v hv
  let aS : (Fin d → ℤ) → ℤ := fun s => if hs : s ∈ S then c ⟨s,hs⟩ else 0
  have hsum : (∑ s ∈ S,aS s • s) = ∑ s : S,c s • s.val := by
    rw [← Finset.sum_coe_sort S (fun s => aS s • s)]
    apply sum_congr rfl
    intro s _
    simp only [aS,dif_pos s.property]
  have hcost : (∑ s ∈ S,|aS s|) = ∑ s : S,|c s| := by
    rw [← Finset.sum_coe_sort S (fun s => |aS s|)]
    apply sum_congr rfl
    intro s _
    simp only [aS,dif_pos s.property]
  obtain ⟨a,ha,hac⟩ := IntLift.transfer_indexed A aS
  refine ⟨a,ha.trans (hsum.trans hc),?_⟩
  rw [hac]
  exact hcost.trans_le hcb

/-- The original recovery splice with its formerly existential lifting constant replaced by the proved recursive majorant. -/
theorem recovery_splice_explicit (d R : ℕ) :
    ∀ {𝒯 E ι : Type*} [Fintype 𝒯] [Fintype E] [Fintype ι]
      (bd : (𝒯 → ℤ) →ₗ[ℤ] (E → ℤ)) (emb : (Fin d → ℤ) →ₗ[ℤ] (E → ℤ))
      (B₀ : ι → Fin d → ℤ) (q : ι → 𝒯 → ℤ) (H D J : ℕ),
      (∀ r j, |B₀ r j| ≤ R) → (∀ r, bd (q r) = emb (B₀ r)) → (∀ r, ∑ t, |q r t| ≤ J) →
      ∀ (x : E → ℤ) (c₀ : 𝒯 → ℤ) (y : Fin d → ℤ),
        x - emb y = bd c₀ → ∑ t, |c₀ t| ≤ H * ∑ e, |x e| → l1 y ≤ D * ∑ e, |x e| →
        y ∈ span ℤ (Set.range B₀) →
        ∃ c : 𝒯 → ℤ, bd c = x ∧ ∑ t, |c t| ≤ (H + J * kernelBound d (max 1 R) * D) * ∑ e, |x e| := by
  classical
  let K := kernelBound d (max 1 R)
  intro 𝒯 E ι _ _ _ bd emb B₀ q H D J hB hq hJ x c₀ y hx hc₀ hy hspan
  obtain ⟨a, ha, hac⟩ := int_lift_uniform_explicit d R B₀ hB y hspan
  refine ⟨c₀ + ∑ r, a r • q r, ?_, ?_⟩
  · have hy' : ∑ r, a r • emb (B₀ r) = emb y := by
      rw [← ha, map_sum]; simp only [map_zsmul]
    rw [map_add, map_sum, ← hx]
    simp only [map_zsmul, hq]
    rw [hy']; abel
  · have hx0 : 0 ≤ ∑ e, |x e| := sum_nonneg fun _ _ => abs_nonneg _
    have h1 : ∑ t, |(c₀ + ∑ r, a r • q r) t| ≤ ∑ t, |c₀ t| + ∑ r, |a r| * J := by
      calc ∑ t, |(c₀ + ∑ r, a r • q r) t|
          ≤ ∑ t, (|c₀ t| + ∑ r, |a r| * |q r t|) := by
            refine sum_le_sum fun t _ => ?_
            simp only [Pi.add_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
            refine (abs_add_le _ _).trans (add_le_add_right ?_ _)
            refine (abs_sum_le_sum_abs _ _).trans (le_of_eq ?_)
            simp [abs_mul]
        _ = ∑ t, |c₀ t| + ∑ r, |a r| * ∑ t, |q r t| := by
            rw [sum_add_distrib, sum_comm]; simp [mul_sum]
        _ ≤ ∑ t, |c₀ t| + ∑ r, |a r| * J := by
            gcongr with r; exact hJ r
    have h2 : ∑ r, |a r| * (J : ℤ) ≤ J * K * D * ∑ e, |x e| := by
      rw [← sum_mul]
      have hK0 : (0 : ℤ) ≤ K := by positivity
      have hJ0 : (0 : ℤ) ≤ J := by positivity
      calc (∑ r, |a r|) * (J : ℤ) ≤ (K * l1 y) * J := mul_le_mul_of_nonneg_right hac hJ0
        _ ≤ (K * (D * ∑ e, |x e|)) * J := by gcongr
        _ = J * K * D * ∑ e, |x e| := by ring
    linarith


#print axioms recovery_splice_explicit
#print axioms bounded_lattice_certificate
#print axioms int_lift_finset_explicit
#print axioms int_lift_uniform_explicit
end TypedTriangle.IntLiftExplicit
