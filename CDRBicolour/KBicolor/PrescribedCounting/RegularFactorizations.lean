/-
Copyright (c) 2026 Juan Pablo Traverso Gianini.
Released under Apache 2.0 license.
Authors: Juan Pablo Traverso Gianini
-/
module
public import CountingCone.VanDerWaerden.Full

/-! # Counting ordered factorizations of any regular bipartite graph

The permanent input is the proved van der Waerden theorem. This extends
the existing Latin-rectangle argument from the complete bipartite graph
to an arbitrary regular support.
-/
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace CDRBicolour.KBicolor.PrescribedCounting
open Finset Classical
variable {n d j : ℕ}

def rowSet (E : Finset (Fin n × Fin n)) (v : Fin n) : Finset (Fin n) :=
  univ.filter (fun w => (v,w) ∈ E)

def colSet (E : Finset (Fin n × Fin n)) (w : Fin n) : Finset (Fin n) :=
  univ.filter (fun v => (v,w) ∈ E)

def Regular (E : Finset (Fin n × Fin n)) (d : ℕ) : Prop :=
  (∀ v, (rowSet E v).card=d) ∧ (∀ w, (colSet E w).card=d)

def matchings (E : Finset (Fin n × Fin n)) : Finset (Equiv.Perm (Fin n)) :=
  univ.filter (fun p => ∀ v, (v,p v) ∈ E)

theorem matching_count_lower {E : Finset (Fin n × Fin n)} (hE : Regular E d) (hd : 0<d) :
    (d:ℝ)^n * ((n.factorial:ℝ)/(n:ℝ)^n) ≤ (matchings E).card := by
  let M : Matrix (Fin n) (Fin n) ℝ := fun s c => if (c,s) ∈ E then 1 else 0
  have hdR : (0:ℝ)<d := by exact_mod_cast hd
  have hper : M.permanent = ((matchings E).card:ℝ) := by
    rw [Matrix.permanent]
    simp only [M,prod_boole,mem_univ,true_implies,sum_boole]
    rfl
  have hds : ((d:ℝ)⁻¹ • M) ∈ doublyStochastic ℝ (Fin n) := by
    rw [mem_doublyStochastic_iff_sum]
    refine ⟨fun s c => ?_,fun s => ?_,fun c => ?_⟩
    · change 0 ≤ (d:ℝ)⁻¹*(if (c,s)∈E then 1 else 0)
      split_ifs <;> positivity
    · change (∑ c, (d:ℝ)⁻¹*(if (c,s)∈E then 1 else 0))=1
      rw [← mul_sum,sum_boole]
      change (d:ℝ)⁻¹ * (colSet E s).card=1
      rw [hE.2,inv_mul_cancel₀ hdR.ne']
    · change (∑ s, (d:ℝ)⁻¹*(if (c,s)∈E then 1 else 0))=1
      rw [← mul_sum,sum_boole]
      change (d:ℝ)⁻¹ * (rowSet E c).card=1
      rw [hE.1,inv_mul_cancel₀ hdR.ne']
  have hh := _root_.STS.van_der_waerden n _ hds
  rw [Matrix.permanent_smul,Fintype.card_fin,hper] at hh
  calc
    _ ≤ (d:ℝ)^n * ((d:ℝ)⁻¹^n * (matchings E).card) :=
      mul_le_mul_of_nonneg_left hh (by positivity)
    _ = _ := by rw [← mul_assoc,← mul_pow,mul_inv_cancel₀ hdR.ne',one_pow,one_mul]

abbrev PartialFactorization (E : Finset (Fin n × Fin n)) (j : ℕ) :=
  {r : _root_.STS.LR n j // ∀ i v, (v,r.1 i v) ∈ E}

def remaining (E : Finset (Fin n × Fin n)) (r : PartialFactorization E j) :
    Finset (Fin n × Fin n) := E.filter (fun p => ∀ i, r.1.1 i p.1 ≠ p.2)

theorem remaining_regular {E : Finset (Fin n × Fin n)} (hE : Regular E d)
    (r : PartialFactorization E j) : Regular (remaining E r) (d-j) := by
  constructor
  · intro v
    have himg : #((univ:Finset (Fin j)).image (fun i => r.1.1 i v))=j := by
      rw [card_image_of_injective _ (fun i l he => by
        by_contra hil; exact r.1.2 i l hil v he),card_univ,Fintype.card_fin]
    have hsub : (univ:Finset (Fin j)).image (fun i => r.1.1 i v) ⊆ rowSet E v := by
      intro w hw
      obtain ⟨i,_,rfl⟩ := mem_image.mp hw
      simpa only [rowSet,mem_filter,mem_univ,true_and] using r.2 i v
    have heq : rowSet (remaining E r) v = rowSet E v \ univ.image (fun i => r.1.1 i v) := by
      ext w
      simp only [rowSet,remaining,mem_filter,mem_univ,true_and,mem_sdiff,mem_image,not_exists,not_and]
    rw [heq,card_sdiff_of_subset hsub,hE.1,himg]
  · intro w
    have hinj : Function.Injective (fun i : Fin j => (r.1.1 i).symm w) := by
      intro i l he
      by_contra hil
      apply r.1.2 i l hil ((r.1.1 i).symm w)
      change (r.1.1 i).symm w = (r.1.1 l).symm w at he
      calc
        (r.1.1 i) ((r.1.1 i).symm w)=w := (r.1.1 i).apply_symm_apply w
        _=(r.1.1 l) ((r.1.1 i).symm w) := by rw [he]; simp
    have himg : #((univ:Finset (Fin j)).image (fun i => (r.1.1 i).symm w))=j := by
      rw [card_image_of_injective _ hinj,card_univ,Fintype.card_fin]
    have hsub : (univ:Finset (Fin j)).image (fun i => (r.1.1 i).symm w) ⊆ colSet E w := by
      intro v hv
      obtain ⟨i,_,rfl⟩ := mem_image.mp hv
      have hh := r.2 i ((r.1.1 i).symm w)
      simpa [colSet] using hh
    have heq : colSet (remaining E r) w = colSet E w \ univ.image (fun i => (r.1.1 i).symm w) := by
      ext v
      simp only [colSet,remaining,mem_filter,mem_univ,true_and,mem_sdiff,mem_image,not_exists,not_and]
      constructor
      · rintro ⟨hv,hh⟩
        exact ⟨hv,fun i he => hh i (by rw [← he]; simp)⟩
      · rintro ⟨hv,hh⟩
        exact ⟨hv,fun i he => hh i (by rw [← he]; simp)⟩
    rw [heq,card_sdiff_of_subset hsub,hE.2,himg]

theorem partial_factorization_succ {E : Finset (Fin n × Fin n)} :
    ∑ r : PartialFactorization E j, (matchings (remaining E r)).card ≤
      Fintype.card (PartialFactorization E (j+1)) := by
  let f : (Σ r : PartialFactorization E j, ↥(matchings (remaining E r))) →
      PartialFactorization E (j+1) := fun p =>
    ⟨⟨Fin.snoc p.1.1.1 p.2.1,by
      intro i l hil v
      have hp := (mem_filter.mp p.2.2).2 v
      simp only [remaining,mem_filter] at hp
      revert hil
      refine Fin.lastCases ?_ (fun i' => ?_) i <;> refine Fin.lastCases ?_ (fun l' => ?_) l <;> intro hil
      · exact absurd rfl hil
      · simp only [Fin.snoc_last,Fin.snoc_castSucc]; exact (hp.2 l').symm
      · simp only [Fin.snoc_last,Fin.snoc_castSucc]; exact hp.2 i'
      · simp only [Fin.snoc_castSucc]
        exact p.1.1.2 i' l' (fun he => hil (by rw [he])) v⟩,by
      intro i v
      refine Fin.lastCases ?_ (fun i' => ?_) i
      · simpa only [Fin.snoc_last] using (mem_filter.mp ((mem_filter.mp p.2.2).2 v)).1
      · simpa only [Fin.snoc_castSucc] using p.1.2 i' v⟩
  have hinj : Function.Injective f := by
    rintro ⟨r,p⟩ ⟨r',p'⟩ he
    have hh := congrArg (fun a => a.1.1) he
    have hr : r=r' := Subtype.ext (Subtype.ext (by
      funext i
      have hhi := congrFun hh (Fin.castSucc i)
      simpa only [f,Fin.snoc_castSucc] using hhi))
    subst r'
    have hp : p=p' := Subtype.ext (by
      have hhi := congrFun hh (Fin.last j)
      simpa only [f,Fin.snoc_last] using hhi)
    subst p'
    rfl
  have hh := Fintype.card_le_of_injective f hinj
  rw [Fintype.card_sigma] at hh
  simpa using hh

theorem partial_factorization_count {E : Finset (Fin n × Fin n)} (hE : Regular E d) :
    ∀ j, j≤d →
      ∏ i ∈ range j, (((d-i:ℕ):ℝ)^n * ((n.factorial:ℝ)/(n:ℝ)^n)) ≤
        Fintype.card (PartialFactorization E j) := by
  intro j
  induction j with
  | zero =>
    intro _
    simp only [range_zero,prod_empty,Nat.one_le_cast]
    rw [Nat.one_le_iff_ne_zero,← Nat.pos_iff_ne_zero,Fintype.card_pos_iff]
    exact ⟨⟨⟨Fin.elim0,fun i => i.elim0⟩,fun i => i.elim0⟩⟩
  | succ j ih =>
    intro hj
    rw [prod_range_succ]
    calc
      _ ≤ (Fintype.card (PartialFactorization E j):ℝ) *
          (((d-j:ℕ):ℝ)^n * ((n.factorial:ℝ)/(n:ℝ)^n)) :=
        mul_le_mul_of_nonneg_right (ih (by omega)) (by positivity)
      _ = ∑ _r : PartialFactorization E j,
          (((d-j:ℕ):ℝ)^n * ((n.factorial:ℝ)/(n:ℝ)^n)) := by simp
      _ ≤ ∑ r : PartialFactorization E j, ((matchings (remaining E r)).card:ℝ) :=
        sum_le_sum (fun r _ => matching_count_lower (remaining_regular hE r) (by omega))
      _ ≤ _ := by exact_mod_cast (partial_factorization_succ (E:=E) (j:=j))

end CDRBicolour.KBicolor.PrescribedCounting
