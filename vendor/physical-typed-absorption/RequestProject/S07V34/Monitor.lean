/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module
public import RequestProject.S07V32.CosetPayment
set_option maxHeartbeats 4000000 -- build option (original: -DmaxHeartbeats=1600000; raised)
set_option maxRecDepth 16384 -- build option (original: -DmaxRecDepth=8192; raised)
@[expose] public section

/-!
# Integer monitors with finite kernel and their restriction (V34, parts 1–2)

* `exists_int_monitor`: every finitely generated abelian group `G` admits an additive map
  `ψ : G →+ ℤ^k` with finite kernel. Proof from the integral structure theorem
  `AddCommGroup.equiv_free_prod_directSum_zmod` (`G ≃+ ℤ^(n) × ⨁ ZMod (pᵢ^eᵢ)`): `ψ` is the
  free coordinate projection, its kernel embeds into the finite torsion part.
* `l1_map_sum_le`: if `‖ψ(g b)‖₁ ≤ M` for every generator, then
  `‖ψ(∑ n_b • g b)‖₁ ≤ M * ∑ |n_b|` (the same monitor evaluates words of other strata).
* `restricted_payment`: a monitor `ψ` on `G ⧸ H` (the *whole* quotient, not only `K ⧸ H`)
  with finite kernel pays every `x` in `K = closure (range g)` by an integer word in `g`
  modulo `H`, with `ℓ¹` cost `≤ A * (1 + ‖ψ(x+H)‖₁)`. This is the V32 lemma applied to the image
  of `K` in `G ⧸ H` with the restricted monitor. No relation between `H` and `K` is needed.
-/

namespace S07V34

open Finset S07V32

/-- **Integer monitor with finite kernel** for any finitely generated abelian group, obtained
from the integral structure theorem (free part × finite direct sum of `ZMod (p^e)`). -/
theorem exists_int_monitor (G : Type*) [AddCommGroup G] [AddGroup.FG G] :
    ∃ (k : ℕ) (psi : G →+ (Fin k → ℤ)), (psi.ker : Set G).Finite := by
  obtain ⟨n, ι, hι, p, hp, e, ⟨f⟩⟩ := AddCommGroup.equiv_free_prod_directSum_zmod G
  let psi : G →+ (Fin n → ℤ) :=
    (Finsupp.linearEquivFunOnFinite ℤ ℤ (Fin n)).toAddMonoidHom.comp
      ((AddMonoidHom.fst _ _).comp f.toAddMonoidHom)
  refine ⟨n, psi, ?_⟩
  haveI : ∀ i, NeZero (p i ^ e i) := fun i => ⟨pow_ne_zero _ (hp i).ne_zero⟩
  let t : G → ((i : ι) → ZMod (p i ^ e i)) := fun x => DirectSum.addEquivProd _ (f x).2
  have hinj : Set.InjOn t (psi.ker : Set G) := by
    intro x hx y hy hxy
    apply f.injective
    have h1 : (f x).1 = (f y).1 := by
      have hx' : psi x = 0 := hx
      have hy' : psi y = 0 := hy
      have : psi x = psi y := by rw [hx', hy']
      exact (Finsupp.linearEquivFunOnFinite ℤ ℤ (Fin n)).injective this
    have h2 : (f x).2 = (f y).2 := (DirectSum.addEquivProd _).injective hxy
    exact Prod.ext h1 h2
  exact Set.Finite.of_finite_image (Set.toFinite _) hinj

/-- `ℓ¹` of an image of an integer word is controlled by the generator bound `M`. -/
theorem l1_map_sum_le {G : Type*} [AddCommGroup G] {k : ℕ} (psi : G →+ (Fin k → ℤ))
    {β : Type*} (T : Finset β) (g : β → G) (n : β → ℤ) (M : ℕ)
    (hM : ∀ b ∈ T, l1 (psi (g b)) ≤ M) :
    l1 (psi (∑ b ∈ T, n b • g b)) ≤ M * ∑ b ∈ T, |n b| := by
  classical
  induction T using Finset.induction_on with
  | empty => simp [l1]
  | insert a T ha ih =>
    rw [sum_insert ha, sum_insert ha, map_add]
    have h1 := l1_add_le (psi (n a • g a)) (psi (∑ b ∈ T, n b • g b))
    have h2 : l1 (psi (n a • g a)) ≤ M * |n a| := by
      rw [map_zsmul]
      have : l1 (n a • psi (g a)) = |n a| * l1 (psi (g a)) := by
        simp [l1, abs_mul, mul_sum]
      rw [this, mul_comm]
      exact mul_le_mul_of_nonneg_right (hM a (mem_insert_self a T)) (abs_nonneg _)
    have h3 := ih (fun b hb => hM b (mem_insert_of_mem hb))
    linarith [mul_add (M : ℤ) |n a| (∑ b ∈ T, |n b|)]

/-- **Restriction of a monitor on `G ⧸ H` to the stratum `K = closure (range g)`.** -/
theorem restricted_payment {G : Type*} [AddCommGroup G] (H : AddSubgroup G)
    {ι : Type*} [Fintype ι] (g : ι → G) {k : ℕ} (psi : G ⧸ H →+ (Fin k → ℤ))
    (hker : (psi.ker : Set (G ⧸ H)).Finite) :
    ∃ A : ℕ, ∀ x ∈ AddSubgroup.closure (Set.range g), ∃ z : ι → ℤ,
      x + ∑ i, z i • g i ∈ H ∧ ∑ i, |z i| ≤ (A : ℤ) * (1 + l1 (psi (x : G ⧸ H))) := by
  classical
  set m := Fintype.card ι
  let eq := Fintype.equivFin ι
  let K' : AddSubgroup (G ⧸ H) := (AddSubgroup.closure (Set.range g)).map (QuotientAddGroup.mk' H)
  have hmem : ∀ i, ((g i : G) : G ⧸ H) ∈ K' := fun i =>
    AddSubgroup.mem_map_of_mem _ (AddSubgroup.subset_closure (Set.mem_range_self i))
  let gb : Fin m → K' := fun j => ⟨((g (eq.symm j) : G) : G ⧸ H), hmem _⟩
  have hgen : ∀ q : K', ∃ z : Fin m → ℤ, ∑ j, z j • gb j = q := by
    rintro ⟨q, hq⟩
    obtain ⟨y, hy, rfl⟩ := AddSubgroup.mem_map.mp hq
    obtain ⟨a, rfl⟩ := (AddSubgroup.mem_closure_range_iff_of_fintype).mp hy
    refine ⟨fun j => a (eq.symm j), ?_⟩
    apply Subtype.ext
    simp only [gb, AddSubgroup.val_finset_sum, AddSubgroup.coe_zsmul, QuotientAddGroup.mk'_apply,
      QuotientAddGroup.mk_sum, QuotientAddGroup.mk_zsmul]
    exact Equiv.sum_comp eq.symm (fun i => a i • ((g i : G) : G ⧸ H))
  let psi' : K' →+ (Fin k → ℤ) := psi.comp K'.subtype
  have hker' : (psi'.ker : Set K').Finite := by
    refine Set.Finite.of_finite_image (f := K'.subtype) (hker.subset ?_) Subtype.val_injective.injOn
    rintro _ ⟨y, hy, rfl⟩
    exact hy
  obtain ⟨A, hA⟩ := coset_payment_abstract gb hgen psi' hker'
  refine ⟨A, fun x hx => ?_⟩
  have hxK : -((x : G ⧸ H)) ∈ K' := K'.neg_mem (AddSubgroup.mem_map_of_mem _ hx)
  obtain ⟨z, hz, hb⟩ := hA ⟨_, hxK⟩
  refine ⟨fun i => z (eq i), ?_, ?_⟩
  · rw [← QuotientAddGroup.eq_zero_iff]
    have hz' := congrArg Subtype.val hz
    simp only [gb, AddSubgroup.val_finset_sum, AddSubgroup.coe_zsmul] at hz'
    have hs : ∑ i, z (eq i) • ((g i : G) : G ⧸ H) = ∑ j, z j • ((g (eq.symm j) : G) : G ⧸ H) := by
      rw [← Equiv.sum_comp eq.symm]; simp only [Equiv.apply_symm_apply]; rfl
    simp only [QuotientAddGroup.mk_add, QuotientAddGroup.mk_sum, QuotientAddGroup.mk_zsmul]
    rw [hs, hz', add_neg_cancel]
  · have hs : ∑ i, |z (eq i)| = ∑ j, |z j| := Equiv.sum_comp eq (fun j => |z j|)
    have hpsi : (∑ j, |psi' ⟨_, hxK⟩ j|) = l1 (psi (x : G ⧸ H)) := by
      simp [psi', l1, map_neg]
    rw [hs, ← hpsi]
    exact hb

end S07V34
