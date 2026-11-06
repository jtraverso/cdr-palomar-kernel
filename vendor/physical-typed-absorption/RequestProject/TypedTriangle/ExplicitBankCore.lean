module
public import RequestProject.S07V37.RelativeKernel
public import RequestProject.S07V42.Catalog
public import RequestProject.S07V42.Generation
public import RequestProject.S07V42.Reroute
public import RequestProject.S07V43.ChildSetting
public import RequestProject.TypedTriangle.BasalStockEntry
public import RequestProject.TypedTriangle.ExplicitBasalPackingSampling
public import RequestProject.TypedTriangle.ExplicitBoundedPieceAbsorber
public import RequestProject.TypedTriangle.ExplicitDenseReference
public import RequestProject.TypedTriangle.ExplicitFinitePresentation
public import RequestProject.TypedTriangle.ExplicitIntLift
public import RequestProject.TypedTriangle.ExplicitNativeApproxPacking
public import RequestProject.TypedTriangle.ExplicitNativeCatalogCompression
public import RequestProject.TypedTriangle.ExplicitSeedPersistence
public import RequestProject.TypedTriangle.ExplicitVertexWindows
public import RequestProject.TypedTriangle.NativeBasalStock
public import RequestProject.TypedTriangle.NativeCatalogCell
public import RequestProject.TypedTriangle.NativeProtectedChildBank
public import RequestProject.TypedTriangle.NativeProtectedGeometricBankEarlyProtection
public import RequestProject.TypedTriangle.PhysicalResidual
public import RequestProject.TypedTriangle.QuadraticBankBudget
set_option maxHeartbeats 4000000 -- build option (original: -DmaxHeartbeats=1600000; raised)
set_option maxRecDepth 16384 -- build option (original: -DmaxRecDepth=8192; raised)
@[expose] public section
noncomputable section

section BankPart01
open Submodule Finset Classical
namespace S07V37.Explicit
open TypedTriangle.QuotientBox

def relKBound (d d' cJ cG R E : ℕ) : ℕ :=
  presLBound d' (max (cG*R) E)*R

def relNBound (d d' cJ cG R E : ℕ) : ℕ :=
  presKBound (Fintype.card {v // v ∈ box d (cJ*R)}) d' (max (cG*R) E)

universe u

theorem relative_kernel_generators_explicit (d d' cJ cG R E : ℕ)
    {N : Type u} [AddCommGroup N] (ℓ : N → ℤ) (hℓ : L1Like ℓ)
    (M₀ M₁ L₀ L₁ : Submodule ℤ N) (hM : M₀ ≤ M₁) (hL : L₀ ≤ L₁)
    (qJ : M₀ →ₗ[ℤ] (Fin d → ℤ)) (qG : M₁ →ₗ[ℤ] (Fin d' → ℤ))
    (hkerJ : ∀ x : M₀, qJ x = 0 → (x : N) ∈ L₀)
    (hkerG : ∀ x : M₁, qG x = 0 → (x : N) ∈ L₁)
    (hqJ : ∀ x : M₀, ∀ i, |qJ x i| ≤ cJ * ℓ x)
    (hqG : ∀ x : M₁, ∀ i, |qG x i| ≤ cG * ℓ x)
    (S : Finset (Fin d' → ℤ)) (hS : ∀ s ∈ S, ∀ i, |s i| ≤ E)
    (himg : (L₁.comap M₁.subtype).map qG = span ℤ (S : Set (Fin d' → ℤ)))
    (atoms : Set N) (hat : atoms ⊆ M₀) (hspan : M₀ ≤ span ℤ atoms)
    (hR : ∀ b ∈ atoms, ℓ b ≤ R) :
    ∃ Y : Finset N, Y.card ≤ relNBound d d' cJ cG R E ∧
      (∀ y ∈ Y, y ∈ M₀ ∧ y ∈ L₁ ∧ ℓ y ≤ relKBound d d' cJ cG R E) ∧
      ∀ x ∈ M₀, x ∈ L₁ → ∃ f : N → ℤ, x - ∑ y ∈ Y, f y • y ∈ L₀ := by
  set D := cJ * R with hD
  set E' := max (cG * R) E with hE'
  let ι := {v // v ∈ box d D}
  -- the box bound for atoms
  have hbox : ∀ b (hb : b ∈ atoms), qJ ⟨b, hat hb⟩ ∈ box d D := fun b hb =>
    mem_box.2 fun i => by
      have h1 := hqJ ⟨b, hat hb⟩ i
      have h2 : (cJ : ℤ) * ℓ b ≤ cJ * R := mul_le_mul_of_nonneg_left (hR b hb) (by positivity)
      push_cast [hD]; exact h1.trans h2
  -- chosen representatives
  let P : ι → Prop := fun a => ∃ b, ∃ hb : b ∈ atoms, qJ ⟨b, hat hb⟩ = a.1
  let rep : ι → N := fun a => if h : P a then h.choose else 0
  have rep_mem : ∀ a, rep a ∈ M₀ := by
    intro a; simp only [rep]; split_ifs with h
    · exact hat h.choose_spec.choose
    · exact zero_mem _
  have rep_ℓ : ∀ a, ℓ (rep a) ≤ R := by
    intro a; simp only [rep]; split_ifs with h
    · exact hR _ h.choose_spec.choose
    · rw [hℓ.zero]; positivity
  let repM : ι → M₀ := fun a => ⟨rep a, rep_mem a⟩
  have rep_spec : ∀ b (hb : b ∈ atoms), qJ (repM ⟨_, hbox b hb⟩) = qJ ⟨b, hat hb⟩ := by
    intro b hb
    have hP : P ⟨_, hbox b hb⟩ := ⟨b, hb, rfl⟩
    have : rep ⟨_, hbox b hb⟩ = hP.choose := dif_pos hP
    have e : repM ⟨_, hbox b hb⟩ = ⟨hP.choose, hat hP.choose_spec.choose⟩ := Subtype.ext this
    rw [e]; exact hP.choose_spec.choose_spec
  -- the combination map
  let comb : (ι → ℤ) →ₗ[ℤ] M₀ :=
    { toFun := fun t => ∑ a, t a • repM a
      map_add' := fun t s => by simp [add_smul, Finset.sum_add_distrib]
      map_smul' := fun r t => by simp [Finset.smul_sum, mul_smul] }
  have comb_coe : ∀ t, ((comb t : M₀) : N) = ∑ a, t a • rep a := by
    intro t; show ((∑ a, t a • repM a : M₀) : N) = _
    rw [Submodule.coe_sum]; rfl
  -- Step 2: representatives generate `M₀` modulo `L₀`.
  have step2 : ∀ x ∈ span ℤ atoms, ∃ t : ι → ℤ, x - (comb t : N) ∈ L₀ := by
    intro x hx
    induction hx using Submodule.span_induction with
    | mem b hb =>
      refine ⟨Pi.single ⟨_, hbox b hb⟩ 1, ?_⟩
      have hc : comb (Pi.single ⟨_, hbox b hb⟩ 1) = repM ⟨_, hbox b hb⟩ := by
        show ∑ a, (Pi.single (⟨_, hbox b hb⟩ : ι) (1 : ℤ) : ι → ℤ) a • repM a = _
        rw [Finset.sum_eq_single (⟨_, hbox b hb⟩ : ι)]
        · simp
        · intro a _ ha; simp [ha]
        · simp
      have h0 : qJ (⟨b, hat hb⟩ - repM ⟨_, hbox b hb⟩) = 0 := by
        rw [map_sub, rep_spec b hb, sub_self]
      have := hkerJ _ h0
      rw [hc]; simpa using this
    | zero => exact ⟨0, by simp⟩
    | add x y _ _ hx hy =>
      obtain ⟨t, ht⟩ := hx; obtain ⟨s, hs⟩ := hy
      refine ⟨t + s, ?_⟩
      have : x + y - (comb (t + s) : N) = (x - comb t) + (y - comb s) := by
        rw [map_add, Submodule.coe_add]; abel
      rw [this]; exact add_mem ht hs
    | smul r x _ hx =>
      obtain ⟨t, ht⟩ := hx
      refine ⟨r • t, ?_⟩
      have : r • x - (comb (r • t) : N) = r • (x - comb t) := by
        rw [map_smul, Submodule.coe_smul, smul_sub]
      rw [this]; exact smul_mem _ _ ht
  -- Step 3: columns and the membership criterion.
  let c : ι → Fin d' → ℤ := fun a => qG (Submodule.inclusion hM (repM a))
  have hc_box : ∀ a i, |c a i| ≤ E' := by
    intro a i
    have h1 := hqG (Submodule.inclusion hM (repM a)) i
    have h2 : (cG : ℤ) * ℓ (rep a) ≤ cG * R :=
      mul_le_mul_of_nonneg_left (rep_ℓ a) (by positivity)
    have h3 : ((cG * R : ℕ) : ℤ) ≤ E' := by exact_mod_cast le_max_left _ _
    push_cast at h3
    exact h1.trans (h2.trans h3)
  have hS' : ∀ s ∈ S, ∀ i, |s i| ≤ E' := fun s hs i =>
    (hS s hs i).trans (by exact_mod_cast le_max_right _ _)
  have hcol : ∀ t, colMap c t = qG (Submodule.inclusion hM (comb t)) := by
    intro t
    show ∑ a, t a • c a = qG (Submodule.inclusion hM (∑ a, t a • repM a))
    simp [map_sum, c]
  have crit : ∀ t, ((comb t : M₀) : N) ∈ L₁ ↔ t ∈ presMod c (S : Set (Fin d' → ℤ)) := by
    intro t
    rw [presMod, Submodule.mem_comap, hcol, ← himg]
    constructor
    · intro h; exact ⟨Submodule.inclusion hM (comb t), h, rfl⟩
    · rintro ⟨l, hl, hlq⟩
      have h0 : qG (Submodule.inclusion hM (comb t) - l) = 0 := by rw [map_sub, hlq, sub_self]
      have h1 := hkerG _ h0
      have h2 : (l : N) ∈ L₁ := hl
      have : ((comb t : M₀) : N) = ((Submodule.inclusion hM (comb t) - l : M₁) : N) + l := by
        simp
      rw [this]; exact add_mem h1 h2
  -- Step 4: uniform finite presentation.
  obtain ⟨Z, hZcard, hZl1, hZspan⟩ := presentation_uniform_explicit E' c hc_box S hS'
  -- Step 5: lift.
  let φ : (ι → ℤ) →ₗ[ℤ] N := M₀.subtype ∘ₗ comb
  have hφ : ∀ t, φ t = ∑ a, t a • rep a := comb_coe
  refine ⟨Z.image φ, Finset.card_image_le.trans hZcard, ?_, ?_⟩
  · intro y hy
    obtain ⟨z, hz, rfl⟩ := Finset.mem_image.1 hy
    have hzP : z ∈ presMod c (S : Set (Fin d' → ℤ)) := hZspan ▸ subset_span hz
    refine ⟨(comb z).2, (crit z).2 hzP, ?_⟩
    rw [hφ]
    calc ℓ (∑ a, z a • rep a) ≤ ∑ a, |z a| * ℓ (rep a) := hℓ.sum_le _ _ _
      _ ≤ ∑ a, |z a| * R := Finset.sum_le_sum fun a _ =>
          mul_le_mul_of_nonneg_left (rep_ℓ a) (abs_nonneg _)
      _ = l1c z * R := by rw [l1c, Finset.sum_mul]
      _ ≤ (presLBound d' E' : ℤ) * R :=
          mul_le_mul_of_nonneg_right (hZl1 z hz) (by positivity)
      _ = (relKBound d d' cJ cG R E : ℤ) := by rw [relKBound]; push_cast; rfl
  · intro x hx0 hx1
    obtain ⟨t, ht⟩ := step2 x (hspan hx0)
    have htL : ((comb t : M₀) : N) ∈ L₁ := by
      have : ((comb t : M₀) : N) = x - (x - comb t) := by abel
      rw [this]; exact sub_mem hx1 (hL ht)
    have htP : t ∈ span ℤ (Z : Set (ι → ℤ)) := hZspan ▸ (crit t).1 htL
    have hmem : φ t ∈ span ℤ ((Z.image φ : Finset N) : Set N) := by
      rw [Finset.coe_image, ← Submodule.map_span]
      exact Submodule.mem_map_of_mem htP
    obtain ⟨f, -, hf⟩ := Submodule.mem_span_finset.1 hmem
    refine ⟨f, ?_⟩
    rw [hf]; exact ht


#print axioms relative_kernel_generators_explicit
end S07V37.Explicit
end BankPart01

section BankPart02
open Finset Classical Submodule
namespace S07V42.Explicit
open TypedTriangle.SparseEdge TypedTriangle.ComponentRows TypedTriangle.Composition
open TypedTriangle.Dispersal
variable {V I : Type*} [Fintype V] {H : SimpleGraph V} {lab : V → I} {F : Set (Multiset I)} {W : Finset V}

def genKBound (β : ℝ) (d c d' c' E' : ℕ) : ℕ :=
  S07V37.Explicit.relKBound (d+d') d' (max c c') c' (atomR β) E'

theorem bounded_generators_explicit {β : ℝ} {h : ℕ} (hβ : 0 < β) {d c E d' c' E' : ℕ}
    (hH3 : CommonNbrCond (H.comap (Subtype.val : {x // x ∈ W} → V)) (lab ∘ Subtype.val) F β)
    (hH4 : HingeCond (H.comap (Subtype.val : {x // x ∈ W} → V)) (lab ∘ Subtype.val) F β h)
    (hW : coreN0 β h ≤ W.card) (C0 : CoreCompression H lab F W d c E)
    {Z : Finset V} (hZ : (Z.card : ℝ) ≤ coreDelta β h * W.card)
    (CZ : DelCompression H lab F Z d' c' E') :
    ∃ Y : Finset (Sym2 V → ℤ),
      (∀ y ∈ Y, y ∈ MZ H lab F W Z ∧ y ∈ LamDel H lab F Z ∧ l1E y ≤ genKBound β d c d' c' E') ∧
      ∀ x ∈ MZ H lab F W Z, x ∈ LamDel H lab F Z →
        ∃ f : (Sym2 V → ℤ) → ℤ, x - ∑ y ∈ Y, f y • y ∈ LamCore H lab F W ⊓ LamDel H lab F Z := by
  obtain ⟨hat, hspan⟩ := bounded_atoms H lab F W hβ hH3 hH4 hW hZ
  have h₁ := MZ_le_MCore H lab F W Z
  have h₂ := MZ_le_MDel H lab F W Z
  set qJ := pairMap h₁ h₂ C0.q CZ.q with hqJ
  have hkerJ : ∀ x : MZ H lab F W Z, qJ x = 0 →
      (x : Sym2 V → ℤ) ∈ LamCore H lab F W ⊓ LamDel H lab F Z := by
    intro x hx
    refine ⟨?_, ?_⟩
    · have : C0.q (Submodule.inclusion h₁ x) = 0 := by
        funext j
        have := congrFun hx (Fin.castAdd d' j)
        rw [hqJ, pairMap_left] at this
        simpa using this
      exact C0.ker_le _ this
    · have : CZ.q (Submodule.inclusion h₂ x) = 0 := by
        funext j
        have := congrFun hx (Fin.natAdd d j)
        rw [hqJ, pairMap_right] at this
        simpa using this
      exact CZ.ker_le _ this
  have hqJb : ∀ (x : MZ H lab F W Z) i, |qJ x i| ≤ (max c c' : ℕ) * l1E (x : Sym2 V → ℤ) := by
    intro x i
    have hl : 0 ≤ l1E (x : Sym2 V → ℤ) := S07V37.l1E_L1Like.nonneg _
    induction i using Fin.addCases with
    | left j =>
      rw [hqJ, pairMap_left]
      refine (C0.bound _ j).trans (mul_le_mul_of_nonneg_right ?_ hl)
      exact_mod_cast le_max_left c c'
    | right j =>
      rw [hqJ, pairMap_right]
      refine (CZ.bound _ j).trans (mul_le_mul_of_nonneg_right ?_ hl)
      exact_mod_cast le_max_right c c'
  obtain ⟨Y, -, hY, hgen⟩ := S07V37.Explicit.relative_kernel_generators_explicit (d + d') d' (max c c') c'
    (atomR β) E' l1E S07V37.l1E_L1Like (MZ H lab F W Z) (localProfile (S07V39.delG H Z) lab F)
    (LamCore H lab F W ⊓ LamDel H lab F Z) (LamDel H lab F Z) h₂ inf_le_right qJ CZ.q hkerJ
    CZ.ker_le hqJb CZ.bound CZ.S CZ.S_bound CZ.img (atomsZ H lab F W β Z) hat hspan
    (fun b hb => by exact_mod_cast hb.2)
  exact ⟨Y, hY, hgen⟩

/-- **`K_Z` is spanned by the classes of bounded actual vectors.** -/
theorem KZ_eq_span_explicit {β : ℝ} {h : ℕ} (hβ : 0 < β) {d c E d' c' E' : ℕ}
    (hH3 : CommonNbrCond (H.comap (Subtype.val : {x // x ∈ W} → V)) (lab ∘ Subtype.val) F β)
    (hH4 : HingeCond (H.comap (Subtype.val : {x // x ∈ W} → V)) (lab ∘ Subtype.val) F β h)
    (hW : coreN0 β h ≤ W.card) (C0 : CoreCompression H lab F W d c E)
    {Z : Finset V} (hZ : (Z.card : ℝ) ≤ coreDelta β h * W.card)
    (CZ : DelCompression H lab F Z d' c' E') :
    ∃ Y : Finset (Sym2 V → ℤ),
      (∀ y ∈ Y, y ∈ MZ H lab F W Z ∧ y ∈ LamDel H lab F Z ∧ l1E y ≤ genKBound β d c d' c' E') ∧
      KZ H lab F W Z = span ℤ (clsQ H lab F W '' (Y : Set (Sym2 V → ℤ))) := by
  obtain ⟨Y, hY, hgen⟩ := bounded_generators_explicit hβ hH3 hH4 hW C0 hZ CZ
  refine ⟨Y, hY, le_antisymm ?_ ?_⟩
  · intro k hk
    obtain ⟨x, hx1, hx2, rfl⟩ := (mem_KZ H lab F W).1 hk
    obtain ⟨f, hf⟩ := hgen x hx1 hx2
    have hcl : clsQ H lab F W x = ∑ y ∈ Y, f y • clsQ H lab F W y := by
      have : clsQ H lab F W (x - ∑ y ∈ Y, f y • y) = 0 :=
        (Submodule.Quotient.mk_eq_zero _).2 hf.1
      unfold clsQ at this ⊢
      rw [Submodule.Quotient.mk_sub, sub_eq_zero] at this
      rw [this, ← Submodule.mkQ_apply, map_sum]
      exact Finset.sum_congr rfl fun y _ => LinearMap.map_smul _ _ _
    rw [hcl]
    exact Submodule.sum_mem _ fun y hy =>
      Submodule.smul_mem _ _ (subset_span ⟨y, hy, rfl⟩)
  · rw [span_le]
    rintro _ ⟨y, hy, rfl⟩
    exact (mem_KZ H lab F W).2 ⟨y, (hY y hy).1, (hY y hy).2.1, rfl⟩


#print axioms bounded_generators_explicit
#print axioms KZ_eq_span_explicit
end S07V42.Explicit
end BankPart02

section BankPart03
open Finset Classical Submodule
set_option maxHeartbeats 800000
namespace S07V42.Explicit
open S07V34

def representativeBound (d R k : ℕ) : ℕ :=
  TypedTriangle.GroupingExplicit.kernelBound d (max 1 R)*d*R*k

universe u

/-- Actual bounded representatives from the explicit integer lifting theorem.
The relation columns are included in the lift and then vanish in the quotient. -/
theorem bounded_representative_explicit (d R k : ℕ) :
    ∀ {N : Type u} [AddCommGroup N] (ℓ : N → ℤ), S07V37.L1Like ℓ →
      ∀ (P : AddSubgroup N) (q : N →+ (Fin d → ℤ)) (S : Finset (Fin d → ℤ)),
      (∀ s ∈ S, ∀ i, |s i| ≤ R) → ∀ Y : Finset N,
      (∀ y ∈ Y, y ∈ P ∧ ℓ y ≤ k ∧ ∀ i, |q y i| ≤ R) →
      ∀ b : Fin d → ℤ, (∀ i, |b i| ≤ R) → qmk S b ∈ Kgrp S (Y.image q) →
      ∃ x ∈ P, ℓ x ≤ representativeBound d R k ∧ qmk S (q x) = qmk S b := by
  intro N _ ℓ hℓ P q S hS Y hY b hb hbK
  let C := Y.image q
  let M : AddSubgroup (Fin d → ℤ) := AddSubgroup.closure ((S∪C : Finset (Fin d → ℤ)) : Set (Fin d → ℤ))
  let π : (Fin d → ℤ) →+ Qt S := QuotientAddGroup.mk' _
  have hK : Kgrp S C ≤ M.map π := by
    change AddSubgroup.closure (qmk S '' (C : Set (Fin d → ℤ))) ≤ M.map π
    rw [AddSubgroup.closure_le]
    rintro x ⟨c,hc,rfl⟩
    exact ⟨c,AddSubgroup.subset_closure (mem_union_right S hc),rfl⟩
  obtain ⟨x,hx,hxb⟩ := hK hbK
  have hrel : x-b ∈ AddSubgroup.closure (S : Set (Fin d → ℤ)) := by
    have hz : π (x-b) = 0 := by
      rw [map_sub,hxb]
      change qmk S b-qmk S b=0
      exact sub_self _
    exact (QuotientAddGroup.eq_zero_iff _).mp hz
  have hrelM : x-b ∈ M :=
    AddSubgroup.closure_mono (show (S : Set (Fin d → ℤ)) ⊆ (S∪C : Finset (Fin d → ℤ)) from
      fun _ hs => mem_union_left C hs) hrel
  have hbM : b ∈ M := by
    have hh := M.sub_mem hx hrelM
    simpa only [sub_sub_cancel] using hh
  have hbspan : b ∈ span ℤ ((S∪C : Finset (Fin d → ℤ)) : Set (Fin d → ℤ)) := by
    rw [← Submodule.mem_toAddSubgroup, Submodule.span_int_eq_addSubgroupClosure]
    exact hbM
  let A : S ⊕ Y → Fin d → ℤ := Sum.elim Subtype.val (fun y => q y.val)
  have hA : ∀ i j, |A i j| ≤ R := by
    intro i j
    cases i with
    | inl s => exact hS s.val s.property j
    | inr y => exact (hY y.val y.property).2.2 j
  have hrange : ((S∪C : Finset (Fin d → ℤ)) : Set (Fin d → ℤ)) ⊆ Set.range A := by
    intro c hc
    rcases mem_union.mp hc with hc | hc
    · exact ⟨Sum.inl ⟨c,hc⟩,rfl⟩
    · obtain ⟨y,hy,rfl⟩ := mem_image.mp hc
      exact ⟨Sum.inr ⟨y,hy⟩,rfl⟩
  obtain ⟨a,ha,hac⟩ := TypedTriangle.IntLiftExplicit.int_lift_uniform_explicit d R A hA b
    ((Submodule.span_mono hrange) hbspan)
  let out : N := ∑ y : Y, a (Sum.inr y) • y.val
  have hout : out ∈ P := P.sum_mem fun y _ => P.zsmul_mem (hY y.val y.property).1 _
  have hnorm : (∑ y : Y, |a (Sum.inr y)|) ≤ ∑ i, |a i| := by
    rw [Fintype.sum_sum_type]
    exact le_add_of_nonneg_left (sum_nonneg fun _ _ => abs_nonneg _)
  have hbL : TypedTriangle.IntLift.l1 b ≤ (d*R : ℕ) := by
    calc TypedTriangle.IntLift.l1 b ≤ ∑ _ : Fin d, (R : ℤ) := sum_le_sum fun i _ => hb i
      _ = (d*R : ℕ) := by simp
  have houtL : ℓ out ≤ representativeBound d R k := by
    have hs := hℓ.sum_le (univ : Finset Y) (fun y => a (Sum.inr y)) Subtype.val
    have hsum : (∑ y : Y, |a (Sum.inr y)| *ℓ y.val) ≤ (∑ y : Y, |a (Sum.inr y)|)*k := by
      rw [sum_mul]
      exact sum_le_sum fun y _ => mul_le_mul_of_nonneg_left (hY y.val y.property).2.1 (abs_nonneg _)
    have hm := mul_le_mul_of_nonneg_right (hnorm.trans hac) (show (0 : ℤ) ≤ k by positivity)
    have hm' := mul_le_mul_of_nonneg_left hbL
      (show (0 : ℤ) ≤ TypedTriangle.GroupingExplicit.kernelBound d (max 1 R) by positivity)
    have hm'' := mul_le_mul_of_nonneg_right hm' (show (0 : ℤ) ≤ k by positivity)
    dsimp [representativeBound]
    push_cast
    convert hs.trans (hsum.trans (hm.trans hm'')) using 1 <;> push_cast <;> ring
  refine ⟨out,hout,houtL,?_⟩
  have hπS : ∀ s : S, π s.val = 0 := fun s =>
    (QuotientAddGroup.eq_zero_iff _).mpr (AddSubgroup.subset_closure s.property)
  have he := congrArg π ha
  simp only [Fintype.sum_sum_type,A,Sum.elim_inl,Sum.elim_inr,map_add,map_sum,map_zsmul,
    hπS,zsmul_zero,sum_const_zero,zero_add] at he
  simpa only [π,out,qmk_hom,map_sum,map_zsmul] using he

#print axioms bounded_representative_explicit
end S07V42.Explicit
end BankPart03

section BankPart04
open Finset Classical Submodule
namespace S07V42.Explicit
open TypedTriangle.SparseEdge TypedTriangle.ComponentRows TypedTriangle.Composition
open TypedTriangle.Dispersal S07V34

def catRadius (β : ℝ) (d c E d' c' E' : ℕ) : ℕ := max E (c*genKBound β d c d' c' E')
def rerouteSize (β : ℝ) (d c E d' c' E' : ℕ) : ℕ :=
  representativeBound d (catRadius β d c E d' c' E') (genKBound β d c d' c' E')

variable {V I : Type*} [Fintype V] {H : SimpleGraph V} {lab : V → I} {F : Set (Multiset I)} {W : Finset V}

theorem catalog_generates_explicit {β : ℝ} {h : ℕ} (hβ : 0 < β) {d c E d' c' E' : ℕ}
    (hH3 : CommonNbrCond (H.comap (Subtype.val : {x // x ∈ W} → V)) (lab ∘ Subtype.val) F β)
    (hH4 : HingeCond (H.comap (Subtype.val : {x // x ∈ W} → V)) (lab ∘ Subtype.val) F β h)
    (hW : coreN0 β h ≤ W.card) (C0 : CoreCompression H lab F W d c E)
    {Z : Finset V} (hZ : (Z.card : ℝ) ≤ coreDelta β h * W.card)
    (CZ : DelCompression H lab F Z d' c' E') :
    AddSubgroup.closure {k | ∃ v, gCat C0 (catRadius β d c E d' c' E') v = k ∧
        gCat C0 (catRadius β d c E d' c' E') v ∈ KZ H lab F W Z} =
      (KZ H lab F W Z).toAddSubgroup := by
  obtain ⟨Y, hY, hspan⟩ := KZ_eq_span_explicit hβ hH3 hH4 hW C0 hZ CZ
  apply le_antisymm
  · rw [AddSubgroup.closure_le]
    rintro _ ⟨v, rfl, hv⟩
    exact hv
  · intro k hk
    have hk' : k ∈ KZ H lab F W Z := hk
    rw [hspan, ← Submodule.mem_toAddSubgroup, Submodule.span_int_eq_addSubgroupClosure] at hk'
    have hsub : clsQ H lab F W '' (Y : Set (Sym2 V → ℤ)) ⊆
        {k | ∃ v, gCat C0 (catRadius β d c E d' c' E') v = k ∧
          gCat C0 (catRadius β d c E d' c' E') v ∈ KZ H lab F W Z} := by
      rintro _ ⟨y, hy, rfl⟩
      obtain ⟨hy1, hy2, hy3⟩ := hY y hy
      have hyC : y ∈ MCore H lab F W := MZ_le_MCore H lab F W Z hy1
      have hb := q_mem_box (R := catRadius β d c E d' c' E') C0 (le_max_right E _) ⟨y, hyC⟩ hy3
      have hg := gCat_spec C0 ⟨_, hb⟩ ⟨y, hyC⟩ rfl
      refine ⟨⟨_, hb⟩, hg, ?_⟩
      rw [hg]
      exact (mem_KZ H lab F W).2 ⟨y, hy1, hy2, rfl⟩
    exact AddSubgroup.closure_mono hsub hk'


universe u v
theorem native_reroute_explicit {β : ℝ} (h : ℕ) (hβ : 0 < β) (d c E d' c' E' : ℕ) :
    ∀ {V : Type u} [Fintype V] {I : Type v} {H : SimpleGraph V} {lab : V → I}
      {F : Set (Multiset I)} {W : Finset V},
      CommonNbrCond (H.comap (Subtype.val : {x // x ∈ W} → V)) (lab ∘ Subtype.val) F β →
      HingeCond (H.comap (Subtype.val : {x // x ∈ W} → V)) (lab ∘ Subtype.val) F β h →
      coreN0 β h ≤ W.card → ∀ C0 : CoreCompression H lab F W d c E,
      ∀ {Z : Finset V}, (Z.card : ℝ) ≤ coreDelta β h * W.card →
      DelCompression H lab F Z d' c' E' →
      ∀ v : Cat d (catRadius β d c E d' c' E'),
        gCat C0 (catRadius β d c E d' c' E') v ∈ KZ H lab F W Z →
        ∃ x, x ∈ MZ H lab F W Z ∧ x ∈ LamDel H lab F Z ∧ l1E x ≤ rerouteSize β d c E d' c' E' ∧
          clsQ H lab F W x = gCat C0 (catRadius β d c E d' c' E') v := by
  set R := catRadius β d c E d' c' E' with hR
  set k := genKBound β d c d' c' E' with hk
  let U := representativeBound d R k
  intro V _ I H lab F W hH3 hH4 hW C0 Z hZ CZ v hv
  by_cases hc : ∃ x : MCore H lab F W, C0.q x = v.1
  swap
  · refine ⟨0, zero_mem _, zero_mem _, ?_, ?_⟩
    · simp [l1E]
    · rw [gCat_of_not C0 v hc]; simp [clsQ]
  obtain ⟨x0, hx0⟩ := hc
  rw [gCat_spec C0 v x0 hx0] at hv ⊢
  obtain ⟨Y, hY, hgen⟩ := bounded_generators_explicit hβ hH3 hH4 hW C0 hZ CZ
  obtain ⟨x1, hx1M, hx1L, hx1⟩ := (mem_KZ H lab F W).1 hv
  obtain ⟨f, hf⟩ := hgen x1 hx1M hx1L
  -- move to the core module
  have hYC : ∀ y ∈ Y, y ∈ MCore H lab F W := fun y hy => MZ_le_MCore H lab F W Z (hY y hy).1
  let Y' : Finset (MCore H lab F W) := Y.subtype (· ∈ MCore H lab F W)
  have hsumY : ∀ g : (Sym2 V → ℤ) → (Sym2 V → ℤ),
      ∑ y ∈ Y', g (y : Sym2 V → ℤ) = ∑ y ∈ Y, g y := by
    intro g
    rw [Finset.sum_subtype_eq_sum_filter, Finset.filter_true_of_mem hYC]
  let P : AddSubgroup (MCore H lab F W) :=
    ((MZ H lab F W Z ⊓ LamDel H lab F Z).comap (MCore H lab F W).subtype).toAddSubgroup
  have hℓ : S07V37.L1Like (fun x : MCore H lab F W => l1E (x : Sym2 V → ℤ)) :=
    ⟨fun x => S07V37.l1E_L1Like.nonneg _, fun x y => S07V37.l1E_L1Like.add_le _ _,
      fun z x => S07V37.l1E_L1Like.smul_le z _⟩
  have hS : ∀ s ∈ C0.S, ∀ i, |s i| ≤ R := fun s hs i =>
    (C0.S_bound s hs i).trans (by exact_mod_cast le_max_left _ _)
  have hY' : ∀ y ∈ Y', y ∈ P ∧ l1E (y : Sym2 V → ℤ) ≤ k ∧
      ∀ i, |C0.q.toAddMonoidHom y i| ≤ R := by
    intro y hy
    rw [Finset.mem_subtype] at hy
    obtain ⟨h1, h2, h3⟩ := hY _ hy
    exact ⟨⟨h1, h2⟩, h3, fun i => S07V34.mem_box.1 (q_mem_box C0 (le_max_right _ _) y h3) i⟩
  have hb : ∀ i, |v.1 i| ≤ R := S07V34.mem_box.1 v.2
  -- the physical word
  set w : MCore H lab F W := x0 - ∑ y ∈ Y', f (y : Sym2 V → ℤ) • y with hw
  have hwL : (w : Sym2 V → ℤ) ∈ LamCore H lab F W := by
    have h01 : (x0 : Sym2 V → ℤ) - x1 ∈ LamCore H lab F W := by
      have := hx1.symm
      unfold clsQ at this
      exact (Submodule.Quotient.eq _).1 this
    have hcoe : (w : Sym2 V → ℤ) = ((x0 : Sym2 V → ℤ) - x1) + (x1 - ∑ y ∈ Y, f y • y) := by
      rw [hw, Submodule.coe_sub, Submodule.coe_sum]
      simp only [Submodule.coe_smul]
      rw [hsumY (fun y => f y • y)]
      abel
    rw [hcoe]
    exact add_mem h01 hf.1
  have hqw : C0.q w ∈ span ℤ (C0.S : Set (Fin d → ℤ)) := (C0.mem_span_iff _).2 ⟨w, hwL, rfl⟩
  have hbK : qmk C0.S v.1 ∈ Kgrp C0.S (Y'.image C0.q.toAddMonoidHom) := by
    have hdec : v.1 = C0.q w + ∑ y ∈ Y', f (y : Sym2 V → ℤ) • C0.q y := by
      rw [hw, map_sub, map_sum]
      simp only [map_zsmul, hx0]
      abel
    have hcl : C0.q w ∈ AddSubgroup.closure (C0.S : Set (Fin d → ℤ)) := by
      rw [← Submodule.span_int_eq_addSubgroupClosure]; exact hqw
    rw [hdec, qmk_hom, map_add]
    have hz0 : (QuotientAddGroup.mk' (AddSubgroup.closure (C0.S : Set (Fin d → ℤ)))) (C0.q w) = 0 :=
      (QuotientAddGroup.eq_zero_iff _).2 hcl
    rw [hz0, zero_add, map_sum]
    refine AddSubgroup.sum_mem _ fun y hy => ?_
    rw [map_zsmul]
    exact AddSubgroup.zsmul_mem _ (AddSubgroup.subset_closure (Set.mem_image_of_mem (qmk C0.S)
      (Finset.mem_coe.2 (Finset.mem_image.2 ⟨y, hy, rfl⟩)))) _
  obtain ⟨x, hxP, hxU, hxq⟩ := bounded_representative_explicit d R k (fun x : MCore H lab F W => l1E (x : Sym2 V → ℤ)) hℓ P
    C0.q.toAddMonoidHom C0.S hS Y' hY' v.1 hb hbK
  refine ⟨x, hxP.1, hxP.2, hxU, ?_⟩
  rw [C0.class_eq_iff]
  have : qmk C0.S (C0.q x) = qmk C0.S (C0.q x0) := by rw [hx0]; exact hxq
  rw [qmk_hom, qmk_hom, QuotientAddGroup.mk'_apply, QuotientAddGroup.mk'_apply,
    QuotientAddGroup.eq] at this
  have h2 : C0.q x - C0.q x0 = -(-C0.q x + C0.q x0) := by abel
  rw [h2]
  refine neg_mem ?_
  rw [← Submodule.mem_toAddSubgroup, Submodule.span_int_eq_addSubgroupClosure]
  exact this


#print axioms catalog_generates_explicit
#print axioms native_reroute_explicit
end S07V42.Explicit
end BankPart04

section BankPart05
open Finset Classical
namespace S07V42.Explicit
open TypedTriangle.SparseEdge TypedTriangle.Dispersal
variable {V I : Type*} [Fintype V] {H : SimpleGraph V} {lab : V → I} {F : Set (Multiset I)} {W : Finset V}

theorem nativeSetting_catalog_small_explicit {β : ℝ} {h : ℕ} (hβ : 0 < β) {d c E d' c' E' : ℕ}
    (hH3 : CommonNbrCond (H.comap (Subtype.val : {x // x ∈ W} → V)) (lab ∘ Subtype.val) F β)
    (hH4 : HingeCond (H.comap (Subtype.val : {x // x ∈ W} → V)) (lab ∘ Subtype.val) F β h)
    (hW : coreN0 β h ≤ W.card) (C0 : CoreCompression H lab F W d c E) (P q Ecell zmax : ℕ)
    (hzmax : (zmax : ℝ) ≤ coreDelta β h * W.card)
    (CZ : ∀ Z : Finset V, Z.card ≤ zmax → DelCompression H lab F Z d' c' E')
    (Z : Finset V) (hZ : Z.card ≤ zmax) :
    AddSubgroup.closure {x | ∃ v, (nativeSetting C0 (catRadius β d c E d' c' E') P q Ecell zmax).g v = x ∧
      (nativeSetting C0 (catRadius β d c E d' c' E') P q Ecell zmax).g v ∈
        (nativeSetting C0 (catRadius β d c E d' c' E') P q Ecell zmax).K Z} =
      (nativeSetting C0 (catRadius β d c E d' c' E') P q Ecell zmax).K Z :=
  catalog_generates_explicit hβ hH3 hH4 hW C0 ((Nat.cast_le.2 hZ).trans hzmax) (CZ Z hZ)


theorem nativeSetting_chainBound_explicit {β : ℝ} {h : ℕ} (hβ : 0 < β) {d c E d' c' E' : ℕ}
    (hH3 : CommonNbrCond (H.comap (Subtype.val : {x // x ∈ W} → V)) (lab ∘ Subtype.val) F β)
    (hH4 : HingeCond (H.comap (Subtype.val : {x // x ∈ W} → V)) (lab ∘ Subtype.val) F β h)
    (hW : coreN0 β h ≤ W.card) (C0 : CoreCompression H lab F W d c E) (P q Ecell zmax : ℕ)
    (hzmax : (zmax : ℝ) ≤ coreDelta β h * W.card)
    (CZ : ∀ Z : Finset V, Z.card ≤ zmax → DelCompression H lab F Z d' c' E') :
    S07V40.ChainBound (nativeSetting C0 (catRadius β d c E d' c' E') P q Ecell zmax)
      (Fintype.card (Cat d (catRadius β d c E d' c' E'))) := by
  set S := nativeSetting C0 (catRadius β d c E d' c' E') P q Ecell zmax with hS
  intro n Z hmono hsmall
  let act : ℕ → Finset (Cat d (catRadius β d c E d' c' E')) := fun i => univ.filter (fun v => S.g v ∈ S.K (Z i))
  have hgen : ∀ i ≤ n, AddSubgroup.closure {x | ∃ v, S.g v = x ∧ v ∈ act i} = S.K (Z i) := by
    intro i hi
    have := nativeSetting_catalog_small_explicit hβ hH3 hH4 hW C0 P q Ecell zmax hzmax CZ (Z i)
      (hsmall i hi)
    rw [← this]
    congr 1
    ext x
    simp only [act, hS, Set.mem_setOf_eq, Finset.mem_filter, Finset.mem_univ, true_and]
  have hsub : ∀ i, act (i + 1) ⊆ act i := by
    intro i v hv
    simp only [act, Finset.mem_filter, Finset.mem_univ, true_and] at hv ⊢
    exact nativeSetting_K_antitone C0 _ P q Ecell zmax (hmono (Nat.le_succ i)) hv
  have key : ∀ m ≤ n, ((range m).filter (fun i => S.K (Z (i + 1)) ≠ S.K (Z i))).card +
      (act m).card ≤ (act 0).card := by
    intro m
    induction m with
    | zero => intro _; simp
    | succ m ih =>
      intro hm
      have ih' := ih (Nat.le_of_succ_le hm)
      rw [Finset.range_add_one, Finset.filter_insert]
      by_cases hch : S.K (Z (m + 1)) ≠ S.K (Z m)
      · rw [if_pos hch, Finset.card_insert_of_notMem (by simp)]
        have hlt : (act (m + 1)).card < (act m).card := by
          apply Finset.card_lt_card
          refine Finset.ssubset_iff_subset_ne.2 ⟨hsub m, fun heq => hch ?_⟩
          rw [← hgen (m + 1) hm, ← hgen m (Nat.le_of_succ_le hm), heq]
        omega
      · rw [if_neg hch]
        have := Finset.card_le_card (hsub m)
        omega
  have := key n le_rfl
  have h0 : (act 0).card ≤ Fintype.card (Cat d (catRadius β d c E d' c' E')) := Finset.card_le_univ _
  omega


end S07V42.Explicit
namespace S07V43.Explicit
open S07V42 S07V42.Explicit S07V40 TypedTriangle.SparseEdge TypedTriangle.Dispersal
variable {V I : Type*} [Fintype V] {H : SimpleGraph V} {lab : V → I} {F : Set (Multiset I)} {W : Finset V}
theorem childSetting_chainBound_explicit {β : ℝ} {h : ℕ} (hβ : 0 < β) {d c E d' c' E' : ℕ}
    (hH3 : CommonNbrCond (H.comap (Subtype.val : {x // x ∈ W} → V)) (lab ∘ Subtype.val) F β)
    (hH4 : HingeCond (H.comap (Subtype.val : {x // x ∈ W} → V)) (lab ∘ Subtype.val) F β h)
    (hW : coreN0 β h ≤ W.card) (C0 : CoreCompression H lab F W d c E) (P q Ecell zmax : ℕ)
    (hzmax : (zmax : ℝ) ≤ coreDelta β h * W.card)
    (CZ : ∀ Z : Finset V, Z.card ≤ zmax → DelCompression H lab F Z d' c' E') :
    ChainBound (childSetting C0 (catRadius β d c E d' c' E') P q Ecell zmax)
      (Fintype.card (Cat d (catRadius β d c E d' c' E'))) := by
  intro n Z hmono hsmall
  have := nativeSetting_chainBound_explicit hβ hH3 hH4 hW C0 P q Ecell zmax hzmax CZ n Z hmono hsmall
  refine le_of_eq_of_le ?_ this
  congr 1
  apply filter_congr
  intro i _
  exact not_congr ⟨fun h' => inl_map_injective h', fun h' => by
    show (KZ H lab F W (Z (i + 1))).toAddSubgroup.map _ =
      (KZ H lab F W (Z i)).toAddSubgroup.map _
    exact congrArg _ h'⟩


#print axioms childSetting_chainBound_explicit
end S07V43.Explicit
end BankPart05

section BankPart06
open Finset Classical
namespace TypedTriangle.CatalogNative.Explicit

def quadraticBankRate (ε δ : ℝ) (E B : ℕ) : ℝ := ε*δ/(32*((E*B:ℕ)+1))
def quadraticBankOrder (ε δ : ℝ) (E B : ℕ) : ℕ :=
  max 1 (max ⌈4/ε⌉₊ (max ⌈2/δ⌉₊ ⌈2*(B*E:ℕ)/ε⌉₊))

theorem quadraticBankRate_pos {ε δ : ℝ} (E B : ℕ) (hε : 0<ε) (hδ : 0<δ) :
    0<quadraticBankRate ε δ E B := by unfold quadraticBankRate; positivity

theorem quadratic_bank_budget_explicit (ε δ : ℝ) (E B : ℕ) (hε : 0 < ε) (hδ : 0 < δ) :
    ∀ n : ℕ, quadraticBankOrder ε δ E B ≤ n →
      let q := ⌊ε*n/2⌋₊;
      let z := ⌊δ*n⌋₊;
      0 < q ∧ (z:ℝ) ≤ δ*n ∧
        ((q+B*E:ℕ):ℝ) ≤ ε*n ∧
        2*E*B*⌊quadraticBankRate ε δ E B*(n:ℝ)^2⌋₊ ≤ q*z ∧
        ε/4*n ≤ (q:ℝ) := by
  let κ := ε*δ/(32*((E*B:ℕ)+1))
  have hκ : 0 < κ := by dsimp [κ]; positivity
  intro n hn
  change max 1 (max ⌈4/ε⌉₊ (max ⌈2/δ⌉₊ ⌈2*(B*E:ℕ)/ε⌉₊)) ≤ n at hn
  have hn1 : 1 ≤ n := (le_max_left _ _).trans hn
  have hne : 4 ≤ ε*n := by
    have hc : ⌈4/ε⌉₊ ≤ n := (le_max_left _ _).trans ((le_max_right _ _).trans hn)
    have hh := (Nat.le_ceil (4/ε)).trans (show (⌈4/ε⌉₊:ℝ) ≤ n by exact_mod_cast hc)
    rw [div_le_iff₀ hε] at hh
    linarith
  have hnd : 2 ≤ δ*n := by
    have hc : ⌈2/δ⌉₊ ≤ n := (le_max_left _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans hn))
    have hh := (Nat.le_ceil (2/δ)).trans (show (⌈2/δ⌉₊:ℝ) ≤ n by exact_mod_cast hc)
    rw [div_le_iff₀ hδ] at hh
    linarith
  have hnB : 2*(B*E:ℕ) ≤ ε*n := by
    have hc : ⌈2*(B*E:ℕ)/ε⌉₊ ≤ n :=
      (le_max_right _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans hn))
    have hh := (Nat.le_ceil (2*(B*E:ℕ)/ε)).trans
      (show (⌈2*(B*E:ℕ)/ε⌉₊:ℝ) ≤ n by exact_mod_cast hc)
    rw [div_le_iff₀ hε] at hh
    linarith
  let q := ⌊ε*n/2⌋₊
  let z := ⌊δ*n⌋₊
  have hqu : (q:ℝ) ≤ ε*n/2 := Nat.floor_le (by positivity)
  have hzu : (z:ℝ) ≤ δ*n := Nat.floor_le (by positivity)
  have hql : ε/4*n ≤ (q:ℝ) := by
    have hh := Nat.sub_one_lt_floor (ε*n/2)
    change ε*n/2-1 < (q:ℝ) at hh
    linarith
  have hzl : δ/2*n ≤ (z:ℝ) := by
    have hh := Nat.sub_one_lt_floor (δ*n)
    change δ*n-1 < (z:ℝ) at hh
    linarith
  have hqp : 0 < q := by
    have hh : (0:ℝ) < q := by linarith
    exact_mod_cast hh
  have hcoef : 2*(E:ℝ)*B*κ ≤ ε*δ/8 := by
    have hd : (0:ℝ) < 32*((E*B:ℕ)+1) := by positivity
    change 2*(E:ℝ)*B*(ε*δ/(32*((E*B:ℕ)+1))) ≤ ε*δ/8
    rw [←mul_div_assoc,div_le_iff₀ hd]
    push_cast
    nlinarith [mul_pos hε hδ,
      mul_nonneg (mul_pos hε hδ).le (by positivity : (0:ℝ) ≤ (E:ℝ)*B)]
  have hN : (⌊κ*(n:ℝ)^2⌋₊:ℝ) ≤ κ*(n:ℝ)^2 := Nat.floor_le (by positivity)
  have hcap : (2:ℝ)*E*B*(⌊κ*(n:ℝ)^2⌋₊:ℝ) ≤ (q:ℝ)*z := by
    have h₁ := mul_le_mul_of_nonneg_left hN (by positivity : (0:ℝ) ≤ 2*E*B)
    have h₂ := mul_le_mul_of_nonneg_right hcoef (sq_nonneg (n:ℝ))
    have h₃ := mul_le_mul hql hzl (by positivity : (0:ℝ) ≤ δ/2*n) (by positivity : (0:ℝ) ≤ q)
    nlinarith only [h₁,h₂,h₃]
  refine ⟨hqp,hzu,?_,by exact_mod_cast hcap,hql⟩
  push_cast
  push_cast at hnB
  linarith

#print axioms quadratic_bank_budget_explicit
end TypedTriangle.CatalogNative.Explicit
end BankPart06

section BankPart07
open Finset Classical
namespace TypedTriangle.ProtectedNibble.Explicit
variable {I : Type*}

def deletedSeedBudget (C α : ℝ) (h : ℕ) : ℝ := RawReference.Explicit.seedBudget (1/C) C α h

theorem deletedSeedBudget_pos {C α : ℝ} (h : ℕ) (hC : 1≤C) (hα : 0<α) :
    0<deletedSeedBudget C α h := by
  have hC0 : 0<C := by linarith
  exact RawReference.Explicit.seedBudget_pos h (by positivity)
    (by rw [div_le_iff₀ hC0]; nlinarith) hα

theorem seed_persistence_exact_explicit {F : Set (Multiset I)} {C α : ℝ} (hC : 1 ≤ C) (hα : 0 < α)
    (hh : ℕ) :
    ∀ {W : Type*} [Fintype W] (H : Host W I) (φ : Finset W → ℝ)
      (B : Finset (Sym2 W)) (Q : Finset (Finset W)) (d : ℕ),
      RawReference.Explicit.seedOrder C ≤ Fintype.card W → IsDiffuseSeed H F C φ → HingeCond H F α hh →
      B ⊆ edges H → IsDecomposition H F B Q → (∀ x, degIn B x ≤ d) →
      (d : ℝ) ≤ deletedSeedBudget C α hh * Fintype.card W →
      ∃ ψ : Finset W → ℝ, IsDiffuseSeed (residual H B) F (2 * C) ψ ∧
        (∀ S, ψ S ≠ 0 → IsAllowed (residual H B) F S) := by
  have hC0 : 0<C := by linarith
  intro W _ H φ B Q d hn0 hφ hcond hB hQ hdeg hd

  have hμ : ∀ T, IsAllowed H F T →
      1 / C / Fintype.card W ≤ φ T ∧ φ T ≤ C / Fintype.card W := by
    intro T hT
    obtain ⟨h1, h2⟩ := hφ.1 T hT
    refine ⟨?_, h2⟩
    rwa [div_div]
  have hload : ∀ f ∈ edges H, |bdry H F φ f - 1| ≤ 0 := by
    intro f hf
    have hfe : f ∈ H.G.edgeSet := by simpa [edges] using hf
    rw [bdry_eq_sum_triOn]
    unfold triOn
    rw [hφ.2 f hfe, sub_self, abs_zero]
  obtain ⟨ψ, hsupp, hpos, hld⟩ :=
    RawReference.Explicit.seed_persistence_approx_explicit (F:=F) (a:=1/C) (b:=C)
      (by positivity) (by rw [div_le_iff₀ hC0]; nlinarith) hα hh H φ B Q d 0 hn0 hcond hμ le_rfl (by norm_num) hload hB hQ hdeg hd
  refine ⟨ψ, ⟨fun T hT => ?_, fun f hf => ?_⟩, hsupp⟩
  · obtain ⟨h1, h2⟩ := hpos T hT
    have hn : (0 : ℝ) < Fintype.card W := by
      have := hT.1
      have : 0 < Fintype.card W := Fintype.card_pos_iff.2 ⟨Classical.choice
        (by obtain ⟨x, -⟩ := card_pos.1 (by omega : 0 < T.card); exact ⟨x⟩)⟩
      exact_mod_cast this
    constructor
    · refine le_trans (le_of_eq ?_) h1
      field_simp
    · refine h2.trans ?_
      rw [div_le_div_iff_of_pos_right hn]
      have : 1 / C / 2 ≤ C := by
        rw [div_div, div_le_iff₀ (by positivity)]; nlinarith
      linarith
  · have hfe : f ∈ edges H ∧ f ∉ B := by
      simp only [residual, subHost, SimpleGraph.edgeSet_inf, SimpleGraph.edgeSet_fromEdgeSet,
        Set.mem_inter_iff, Set.mem_diff, coe_sdiff, mem_coe] at hf
      exact ⟨hf.1.1.1, hf.1.1.2⟩
    have := hld f hfe.1 hfe.2
    rw [mul_zero, abs_nonpos_iff, sub_eq_zero] at this
    rw [← this, bdry_eq_sum_triOn]
    rfl


#print axioms seed_persistence_exact_explicit
end TypedTriangle.ProtectedNibble.Explicit
end BankPart07

section BankPart08
open Finset Classical
namespace TypedTriangle.NativeNibble.Explicit

def seedPackingCut (C η : ℝ) : ℕ :=
  PartitionedTriangleAbsorption.Nibble.Explicit.approxPackingCut C η

theorem packing_of_diffuse_seed_explicit (C η : ℝ) (hC : 1≤C) (hη : 0<η) (hη1 : η≤1) :
    ∀ {V I : Type} [Fintype V] (H : Host V I) (F : Set (Multiset I)) (φ : Finset V → ℝ),
      seedPackingCut C η ≤ Fintype.card V → IsDiffuseSeed H F C φ →
      ∃ P : Finset (Finset V), P ⊆ allowed H F ∧ IsPacking H F P ∧
        ∀ v, (((edges H\P.biUnion triEdges).filter (fun e => v∈e)).card : ℝ) ≤ η*Fintype.card V := by
  intro V I _ H F φ hn hφ
  have hn1 : 1≤Fintype.card V := (le_max_left _ _).trans hn
  have hnpos : (0:ℝ)<Fintype.card V := by exact_mod_cast (by omega : 0<Fintype.card V)
  obtain ⟨P,hP,hdeg⟩ := packing_of_approx_weights_explicit C η (by linarith) hη hη1 H F φ hn
    (fun T hT => ⟨(by positivity : (0:ℝ)≤1/(C*Fintype.card V)).trans (hφ.1 T hT).1,(hφ.1 T hT).2⟩)
    (fun e he => by
      have hfe : e∈H.G.edgeSet := by simpa [edges] using he
      rw [bdry_eq_sum_triOn]
      unfold triOn
      rw [hφ.2 e hfe,sub_self,abs_zero]
      positivity)
  refine ⟨P,?_,hP,hdeg⟩
  intro T hT
  simpa [allowed] using hP.1 T hT

#print axioms packing_of_diffuse_seed_explicit
end TypedTriangle.NativeNibble.Explicit
end BankPart08

section BankPart09
open Finset Classical
namespace TypedTriangle.StockEntry.Explicit

def coverDownRate (κ η : ℝ) : ℝ := min (κ/64) (min (η/64) (1/64))
def coverDownBudget (κ η : ℝ) : ℝ := (coverDownRate κ η)^2
def coverDownOrder (κ η : ℝ) : ℕ := ⌈1/coverDownRate κ η⌉₊
def coverDownQuota (κ η : ℝ) (n : ℕ) : ℕ := ⌈coverDownRate κ η*n⌉₊

theorem coverDownBudget_pos {κ η : ℝ} (hκ : 0<κ) (hη : 0<η) : 0<coverDownBudget κ η := by
  unfold coverDownBudget coverDownRate
  positivity

theorem cover_down_window_explicit (κ η : ℝ) (hκ : 0 < κ) (hη : 0 < η) :
    ∀ n m d : ℕ, coverDownOrder κ η ≤ n →
      m ≤ n*d → (d:ℝ) ≤ coverDownBudget κ η*n →
      let q := coverDownQuota κ η n;
      ((m + q*(2*d+4*q) : ℕ):ℝ) < q*κ*n ∧
        ((2*d+2*q : ℕ):ℝ) ≤ η*n := by
  let θ := min (κ/64) (min (η/64) (1/64))
  have hθ : 0 < θ := lt_min (by positivity) (lt_min (by positivity) (by norm_num))
  have hθκ : θ ≤ κ/64 := min_le_left _ _
  have hθη : θ ≤ η/64 := (min_le_right _ _).trans (min_le_left _ _)
  have hθ1 : θ ≤ 1 := ((min_le_right _ _).trans (min_le_right _ _)).trans (by norm_num)
  intro n m d hn hm hd
  change ⌈1/θ⌉₊ ≤ n at hn
  change (d:ℝ) ≤ θ^2*n at hd
  have hN : (0:ℝ) ≤ n := Nat.cast_nonneg _
  have hnθ : 1 ≤ θ*n := by
    have h1 : 1/θ ≤ (n:ℝ) := (Nat.le_ceil _).trans (by exact_mod_cast hn)
    have hh := (div_le_iff₀ hθ).mp h1
    nlinarith
  have hnpos : (0:ℝ) < n := by nlinarith
  let q := ⌈θ*n⌉₊
  have hlo : θ*n ≤ (q:ℝ) := Nat.le_ceil _
  have hhi : (q:ℝ) ≤ 2*θ*n := by
    have h1 : (q:ℝ) < θ*n+1 := Nat.ceil_lt_add_one (by positivity)
    linarith
  have hq : (0:ℝ) < q := by nlinarith
  have hd' : (d:ℝ) ≤ θ*n := by
    have ht : θ^2 ≤ θ := by nlinarith
    exact hd.trans (by nlinarith [mul_le_mul_of_nonneg_right ht hN])
  have hm' : (m:ℝ) ≤ (q:ℝ)*θ*n := by
    have hmR : (m:ℝ) ≤ n*d := by exact_mod_cast hm
    have h1 := mul_le_mul_of_nonneg_left hd hN
    have h2 := mul_le_mul_of_nonneg_right hlo (mul_nonneg hθ.le hN)
    nlinarith
  have hmid : (2*(d:ℝ)+4*q) ≤ 10*θ*n := by linarith
  have hsum : (m:ℝ)+(q:ℝ)*(2*d+4*q) ≤ (q:ℝ)*11*θ*n := by
    have hh := mul_le_mul_of_nonneg_left hmid hq.le
    nlinarith
  have hstrict : (q:ℝ)*11*θ*n < (q:ℝ)*κ*n := by
    have h11 : 11*θ < κ := by linarith
    have hh := mul_lt_mul_of_pos_left h11 (mul_pos hq hnpos)
    nlinarith
  refine ⟨?_,?_⟩
  · push_cast
    exact hsum.trans_lt hstrict
  · change ((2*d+2*q:ℕ):ℝ) ≤ η*n
    push_cast
    nlinarith


#print axioms cover_down_window_explicit
end TypedTriangle.StockEntry.Explicit
end BankPart09

section BankPart10
open Finset Classical
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace TypedTriangle.StockEntry.Explicit
open BasalIncidence

def stockEntryRemainderTolerance (κ : ℝ) : ℝ := min (coverDownBudget κ 1/4) (1/4)
def stockEntryOrder (C κ : ℝ) : ℕ :=
  max (RawReference.Explicit.seedOrder C)
    (max (NativeNibble.Explicit.seedPackingCut (2*C) (stockEntryRemainderTolerance κ))
      (max (coverDownOrder κ 1) ⌈2/coverDownBudget κ 1⌉₊))

theorem protected_stock_entry_explicit {I : Type} (F : Set (Multiset I))
    (C α : ℝ) (h : ℕ) (hC : 1 ≤ C) (hα : 0 < α) :
    ∀ κ : ℝ, 0 < κ →
      ∀ {V : Type} [Fintype V] (H : Host V I) (φ : Finset V → ℝ)
        (D DR : Finset (Finset V)) (R : Finset (Sym2 V)) (dS : ℕ),
        stockEntryOrder C κ ≤ Fintype.card V → IsDiffuseSeed H F C φ →
        IsPhysical H F (edges H) → HingeCond H F α h →
        IsDecomposition H F (cover D) D → IsDecomposition H F R DR →
        Disjoint (cover D) R → (∀ v, degIn (cover D ∪ R) v ≤ dS) →
        (dS:ℝ) ≤ ProtectedNibble.Explicit.deletedSeedBudget C α h*Fintype.card V →
        (∀ u v, H.G.Adj u v → κ*Fintype.card V ≤ (good H F D u v).card) →
        ∃ Q : Finset (Finset V), IsPacking H F Q ∧
          Disjoint (Q.biUnion triEdges) R ∧
          (edges H \ (R ∪ Q.biUnion triEdges)) ⊆ cover D ∧
          IsPhysical H F (edges H \ (R ∪ Q.biUnion triEdges)) := by
  intro κ hκ
  let nS := RawReference.Explicit.seedOrder C
  let εc := coverDownBudget κ 1
  have hεc : 0<εc := coverDownBudget_pos hκ (by norm_num)
  let nW := coverDownOrder κ 1
  let δ := min (εc/4) (1/4)
  have hδ : 0<δ := lt_min (by positivity) (by norm_num)
  let nP := NativeNibble.Explicit.seedPackingCut (2*C) δ
  intro V _ H φ D DR R dS hn hseed hphys hH4 hD hR hXR hdeg hsmall hSupply
  change max nS (max nP (max nW ⌈2/εc⌉₊)) ≤ Fintype.card V at hn

  let X := cover D
  let S := X ∪ R
  have hDX : IsDecomposition H F S (D ∪ DR) :=
    S07V26.isDecomposition_union hXR hD hR
  have hSH : S ⊆ edges H := by
    rw [← hDX.2.2]
    intro e he
    obtain ⟨T,hT,heT⟩ := mem_biUnion.mp he
    exact triEdges_subset_edges (hDX.1 T hT) heT
  have hXH : X ⊆ edges H := subset_union_left.trans hSH
  obtain ⟨ψ,hψ,_⟩ := ProtectedNibble.Explicit.seed_persistence_exact_explicit (F:=F) hC hα h H φ S (D ∪ DR) dS ((le_max_left _ _).trans hn)
    hseed hH4 hSH hDX hdeg hsmall
  obtain ⟨P,_,hp,hpd⟩ := NativeNibble.Explicit.packing_of_diffuse_seed_explicit (2*C) δ (by linarith) hδ ((min_le_right _ _).trans (by norm_num)) (residual H S) F ψ
    ((le_max_left _ _).trans ((le_max_right _ _).trans hn)) hψ
  have hpH : IsPacking H F P :=
    ⟨fun T hT => isAllowed_mono (subHost_le H _) rfl (hp.1 T hT),hp.2⟩
  have hEdges : edges (residual H S) = edges H \ S := Residual.edges_subHost_eq sdiff_subset
  have hPH : P.biUnion triEdges ⊆ edges H \ S := by
    rw [← hEdges]
    intro e he
    obtain ⟨T,hT,heT⟩ := mem_biUnion.mp he
    exact triEdges_subset_edges (hp.1 T hT) heT
  let J0 := (edges H \ S) \ P.biUnion triEdges
  have hJ0H : J0 ⊆ edges H := sdiff_subset.trans sdiff_subset
  have hJ0phys : IsPhysical H F J0 :=
    isPhysical_sdiff (isPhysical_sdiff_of_decomposition hphys hDX hSH)
      (isPhysical_of_isDecomposition hpH.isDecomposition) hPH
  have hPS : Disjoint (P.biUnion triEdges) S := disjoint_left.mpr fun e he heS =>
    (mem_sdiff.mp (hPH he)).2 heS
  have hJ0X : Disjoint J0 X := disjoint_left.mpr fun e he heX =>
    (mem_sdiff.mp (mem_sdiff.mp he).1).2 (mem_union_left _ heX)
  let J := X ∪ J0
  have hJH : J ⊆ edges H := union_subset hXH hJ0H
  have hXJ : X ⊆ J := subset_union_left
  have hJphys : IsPhysical H F J :=
    isPhysical_union (isPhysical_of_isDecomposition hD) hJ0phys hJ0X.symm
  have hUX : J \ X = J0 := by
    ext e
    have hz : e ∈ J0 → e ∉ X := fun he heX => disjoint_left.mp hJ0X he heX
    simp only [J,mem_sdiff,mem_union]
    tauto
  have hJ0d : ∀ v, ((J0.filter (fun e => v ∈ e)).card : ℝ) ≤ δ*Fintype.card V := by
    simpa only [hEdges] using hpd
  let d := ⌈δ*Fintype.card V⌉₊
  have hdU : ∀ v, ((J \ X).filter (fun e => v ∈ e)).card ≤ d := by
    intro v
    rw [hUX]
    exact_mod_cast (hJ0d v).trans (Nat.le_ceil _)
  have hN : (0:ℝ) ≤ Fintype.card V := Nat.cast_nonneg _
  have hnε : 2 ≤ εc*Fintype.card V := by
    have h1 : 2/εc ≤ (Fintype.card V:ℝ) := (Nat.le_ceil _).trans (by
      exact_mod_cast (le_max_right _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans hn)))
    have hh := (div_le_iff₀ hεc).mp h1
    nlinarith
  have hdε : (d:ℝ) ≤ εc*Fintype.card V := by
    have hc : (d:ℝ) < δ*Fintype.card V+1 := Nat.ceil_lt_add_one (by positivity)
    have hδc : δ ≤ εc/4 := min_le_left _ _
    nlinarith [mul_le_mul_of_nonneg_right hδc hN]
  have hdiag : ∀ e ∈ J \ X, ¬ e.IsDiag := by
    intro e he
    exact H.G.not_isDiag_of_mem_edgeSet (by simpa [edges] using hJH (mem_sdiff.mp he).1)
  have hm := Envelope.two_card_le_card_mul_degree (J \ X) hdiag hdU
  let q := coverDownQuota κ 1 (Fintype.card V)
  obtain ⟨hwin,_⟩ := cover_down_window_explicit κ 1 hκ (by norm_num) (Fintype.card V) (J \ X).card d
    ((le_max_left _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans hn)))
    (by omega) hdε
  obtain ⟨A,hA,hAJ,hleft,hAphys,_⟩ := enter_stock hSupply J hJH hXJ hJphys hdU hwin
  have hJP : Disjoint J (P.biUnion triEdges) := by
    apply disjoint_left.mpr
    intro e he heP
    rcases mem_union.mp he with heX | he0
    · exact disjoint_left.mp hPS heP (mem_union_left _ heX)
    · exact (mem_sdiff.mp he0).2 heP
  have hPA : Disjoint (P.biUnion triEdges) (A.biUnion triEdges) :=
    hJP.symm.mono_right hAJ
  have hQdec : IsDecomposition H F ((P.biUnion triEdges) ∪ A.biUnion triEdges) (P ∪ A) :=
    S07V26.isDecomposition_union hPA hpH.isDecomposition hA.isDecomposition
  have hQ : IsPacking H F (P ∪ A) := ⟨hQdec.1,hQdec.2.1⟩
  have hQedges : (P ∪ A).biUnion triEdges = (P.biUnion triEdges) ∪ A.biUnion triEdges := by
    rw [Finset.union_biUnion]
  have hJexact : J = (edges H \ R) \ P.biUnion triEdges := by
    ext e
    have hxe : e ∈ X → e ∈ edges H := fun he => hXH he
    have hxr : e ∈ X → e ∉ R := fun hx hr => disjoint_left.mp hXR hx hr
    have hxp : e ∈ X → e ∉ P.biUnion triEdges := fun hx hp =>
      disjoint_left.mp hPS hp (mem_union_left _ hx)
    simp only [J,J0,S,mem_union,mem_sdiff]
    tauto
  have hJR : Disjoint J R := by
    rw [hJexact]
    exact (sdiff_disjoint : Disjoint (edges H \ R) R).mono_left sdiff_subset
  have hfinal : edges H \ (R ∪ (P ∪ A).biUnion triEdges) = J \ A.biUnion triEdges := by
    rw [hQedges,hJexact]
    ext e
    simp only [mem_sdiff,mem_union]
    tauto
  refine ⟨P ∪ A,hQ,?_,?_,?_⟩
  · rw [hQedges,disjoint_union_left]
    exact ⟨hPS.mono_right subset_union_right,(hJR.mono_left hAJ)⟩
  · rw [hfinal]
    exact hleft
  · rw [hfinal]
    exact hAphys


#print axioms protected_stock_entry_explicit
end TypedTriangle.StockEntry.Explicit
end BankPart10

section BankPart11
open Finset Classical
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace TypedTriangle.ProtectedNibble.Explicit

def protectedPackingOrder (C η : ℝ) : ℕ :=
  max (RawReference.Explicit.seedOrder C) (NativeNibble.Explicit.seedPackingCut (2*C) η)

theorem packing_away_from_basal_reserve_explicit {I : Type} (F : Set (Multiset I))
    (C α η : ℝ) (h : ℕ) (hC : 1 ≤ C) (hα : 0 < α) (hη : 0 < η) (hη1 : η ≤ 1) :

      ∀ {V : Type} [Fintype V] (H : Host V I) (φ : Finset V → ℝ)
        (R : Finset (Sym2 V)) (D : Finset (Finset V)) (d : ℕ),
        protectedPackingOrder C η ≤ Fintype.card V → IsDiffuseSeed H F C φ →
        IsPhysical H F (edges H) → HingeCond H F α h →
        IsDecomposition H F R D → (∀ v, degIn R v ≤ d) →
        (d : ℝ) ≤ deletedSeedBudget C α h * Fintype.card V →
        ∃ P : Finset (Finset V), TypedTriangle.IsPacking H F P ∧
          Disjoint (P.biUnion triEdges) R ∧
          IsPhysical H F ((edges H \ R) \ P.biUnion triEdges) ∧
          (∀ v, ((((edges H \ R) \ P.biUnion triEdges).filter (fun e => v ∈ e)).card : ℝ)
            ≤ η * Fintype.card V) := by
  intro V _ H φ R D d hn hφ hH2 hH4 hD hdeg hd

  have hRsub : R ⊆ edges H := by
    rw [← hD.2.2]
    intro e he
    obtain ⟨T,hT,heT⟩ := mem_biUnion.mp he
    exact triEdges_subset_edges (hD.1 T hT) heT
  obtain ⟨ψ,hψ,-⟩ := seed_persistence_exact_explicit (F:=F) hC hα h H φ R D d ((le_max_left _ _).trans hn)
    hφ hH4 hRsub hD hdeg hd
  obtain ⟨P,-,hp,hsmall⟩ := NativeNibble.Explicit.packing_of_diffuse_seed_explicit (2*C) η (by linarith) hη hη1 (residual H R) F ψ ((le_max_right _ _).trans hn) hψ
  have hpH : TypedTriangle.IsPacking H F P := by
    refine ⟨?_,hp.2⟩
    intro T hT
    exact isAllowed_mono (subHost_le H _) rfl (hp.1 T hT)
  have hJ : edges (residual H R) = edges H \ R :=
    Residual.edges_subHost_eq sdiff_subset
  have hPsub : P.biUnion triEdges ⊆ edges H \ R := by
    rw [← hJ]
    intro e he
    obtain ⟨T,hT,heT⟩ := mem_biUnion.mp he
    exact triEdges_subset_edges (hp.1 T hT) heT
  have hdis : Disjoint (P.biUnion triEdges) R := by
    apply disjoint_left.mpr
    intro e he hR
    exact (mem_sdiff.mp (hPsub he)).2 hR
  have hphys : IsPhysical H F ((edges H \ R) \ P.biUnion triEdges) :=
    isPhysical_sdiff (isPhysical_sdiff_of_decomposition hH2 hD hRsub)
      (isPhysical_of_isDecomposition hpH.isDecomposition) hPsub
  refine ⟨P,hpH,hdis,hphys,?_⟩
  simpa only [hJ] using hsmall


#print axioms packing_away_from_basal_reserve_explicit
end TypedTriangle.ProtectedNibble.Explicit
end BankPart11

section BankPart12
open Finset Classical
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace TypedTriangle.BasalIncidence.Explicit

def protectedStockRate (ρ : ℝ) : ℝ := min (ρ/12) (1/2)
def protectedStockTolerance (α : ℝ) : ℝ := min (α/8) (1/2)
def protectedStockBudget (C α : ℝ) (h : ℕ) : ℝ :=
  min (ProtectedNibble.Explicit.deletedSeedBudget C α h) (α/8)
def protectedStockCompletion (α ρ : ℝ) : ℝ := α/2*(protectedStockRate ρ)^2/2
def protectedStockOrder (C α ρ : ℝ) : ℕ :=
  max (ProtectedNibble.Explicit.protectedPackingOrder C (protectedStockTolerance α))
    (BasalSampling.Explicit.samplingCut (protectedStockRate ρ) (α/2))

theorem protectedStockBudget_pos {C α : ℝ} (h : ℕ) (hC : 1≤C) (hα : 0<α) :
    0<protectedStockBudget C α h :=
  lt_min (ProtectedNibble.Explicit.deletedSeedBudget_pos h hC hα) (by positivity)

theorem protectedStockCompletion_pos {α ρ : ℝ} (hα : 0<α) (hρ : 0<ρ) :
    0<protectedStockCompletion α ρ := by unfold protectedStockCompletion protectedStockRate; positivity

theorem reserve_avoiding_basal_explicit {I : Type} (F : Set (Multiset I))
    (C α ρ : ℝ) (h : ℕ) (hC : 1 ≤ C) (hα : 0 < α) (hρ : 0 < ρ) :

      ∀ {V : Type} [Fintype V] (H : Host V I) (φ : Finset V → ℝ)
        (T : Finset (Sym2 V)) (DT : Finset (Finset V)) (dT : ℕ),
        protectedStockOrder C α ρ ≤ Fintype.card V → IsDiffuseSeed H F C φ →
        IsPhysical H F (edges H) → CommonNbrCond H F α → HingeCond H F α h →
        IsDecomposition H F T DT → (∀ v, SparseEdge.degIn T v ≤ dT) →
        (dT:ℝ) ≤ protectedStockBudget C α h*Fintype.card V →
        ∃ D : Finset (Finset V), IsDecomposition H F (cover D) D ∧
          Disjoint (cover D) T ∧
          (∀ v, (SparseEdge.degIn (cover D) v:ℝ) < ρ*Fintype.card V) ∧
          ∀ u v, H.G.Adj u v → protectedStockCompletion α ρ*Fintype.card V ≤ (good H F D u v).card := by
  let η := min (α/8) (1/2)
  have hη : 0<η := lt_min (by positivity) (by norm_num)
  let εP := ProtectedNibble.Explicit.deletedSeedBudget C α h
  let nP := ProtectedNibble.Explicit.protectedPackingOrder C η
  let ε := min εP (α/8)
  let q := min (ρ/12) (1/2)
  have hεP : 0<εP := ProtectedNibble.Explicit.deletedSeedBudget_pos h hC hα
  have hε : 0<ε := lt_min hεP (by positivity)
  have hq : 0<q := lt_min (by positivity) (by norm_num)
  let nS := BasalSampling.Explicit.samplingCut q (α/2)
  intro V _ H φ T DT dT hn hseed h2 h3 h4 hT hTd hTs
  change max nP nS ≤ Fintype.card V at hn

  obtain ⟨P,hPack,hPT,_,hUd⟩ := ProtectedNibble.Explicit.packing_away_from_basal_reserve_explicit F C α η h hC hα hη ((min_le_right _ _).trans (by norm_num)) H φ T DT dT ((le_max_left _ _).trans hn)
    hseed h2 h4 hT hTd (hTs.trans (mul_le_mul_of_nonneg_right
      (min_le_left _ _) (by positivity)))
  have hMiss : ∀ v, (((edges H\cover P).filter (fun e => v ∈ e)).card:ℝ) ≤
      (α/4)*Fintype.card V := by
    intro v
    have hsub : (edges H\cover P).filter (fun e => v ∈ e) ⊆
        T.filter (fun e => v ∈ e) ∪
          (((edges H\T)\P.biUnion triEdges).filter (fun e => v ∈ e)) := by
      intro e he
      obtain ⟨he,hv⟩ := mem_filter.mp he
      by_cases ht : e ∈ T
      · exact mem_union_left _ (mem_filter.mpr ⟨ht,hv⟩)
      · exact mem_union_right _ (mem_filter.mpr
          ⟨mem_sdiff.mpr ⟨mem_sdiff.mpr ⟨(mem_sdiff.mp he).1,ht⟩,(mem_sdiff.mp he).2⟩,hv⟩)
    have hc : (((edges H\cover P).filter (fun e => v ∈ e)).card:ℝ) ≤
        SparseEdge.degIn T v +
          ((((edges H\T)\P.biUnion triEdges).filter (fun e => v ∈ e)).card:ℝ) := by
      exact_mod_cast (card_le_card hsub).trans (card_union_le _ _)
    have hd : (SparseEdge.degIn T v:ℝ) ≤ (α/8)*Fintype.card V :=
      (show (SparseEdge.degIn T v:ℝ) ≤ dT by exact_mod_cast hTd v).trans
        (hTs.trans (mul_le_mul_of_nonneg_right (min_le_right _ _) (by positivity)))
    have hu := hUd v
    have hηa : η ≤ α/8 := min_le_left _ _
    nlinarith [mul_le_mul_of_nonneg_right hηa (show (0:ℝ) ≤ Fintype.card V by positivity)]
  let τ := {uv : V × V // H.G.Adj uv.1 uv.2}
  let u : τ → V := fun t => t.val.1
  let v : τ → V := fun t => t.val.2
  have hcount : Fintype.card τ ≤ Fintype.card V^2 := by
    calc
      Fintype.card τ ≤ Fintype.card (V×V) := Fintype.card_subtype_le _
      _ = _ := by rw [Fintype.card_prod]; ring
  have hSupply : ∀ t : τ, α/2*Fintype.card V ≤ (good H F P (u t) (v t)).card := by
    intro t
    obtain ⟨a,ha⟩ := edge_allowed_of_seed (by linarith : 0 < C) hseed t.property
    have hh := good_supply h3 P hMiss ha
    dsimp only [u,v]
    nlinarith only [hh]
  obtain ⟨D,hDP,hD,hsmall,hgood⟩ := sample_packing_explicit q (α/2) hq ((min_le_right _ _).trans (by norm_num)) (by positivity) V I H F P hPack ((le_max_right _ _).trans hn)
    τ u v hcount hSupply
  refine ⟨D,hD,?_,?_,?_⟩
  · apply hPT.mono_left
    intro e he
    obtain ⟨A,hA,heA⟩ := mem_biUnion.mp he
    exact mem_biUnion.mpr ⟨A,hDP hA,heA⟩
  · intro x
    have hx := hsmall x
    have hqρ : q ≤ ρ/12 := min_le_left _ _
    change (((cover D).filter (fun e => x ∈ e)).card:ℝ) < ρ*Fintype.card V
    nlinarith [mul_le_mul_of_nonneg_right hqρ (show (0:ℝ) ≤ Fintype.card V by positivity)]
  · intro x y hxy
    have hh := hgood ⟨(x,y),hxy⟩
    dsimp only [u,v] at hh
    change (α/2*q^2/2)*Fintype.card V ≤ (good H F D x y).card
    nlinarith only [hh]

#print axioms reserve_avoiding_basal_explicit
end TypedTriangle.BasalIncidence.Explicit
end BankPart12

section BankPart13
open Finset Classical
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace TypedTriangle.BasalIncidence.Explicit

def stockRate (ρ : ℝ) : ℝ := min (ρ/12) (1/2)
def rawStockBudget (a b α : ℝ) (h : ℕ) : ℝ :=
  min (RawReference.Explicit.stockBudget a b α h) (α/8)
def rawStockLoadTolerance (α : ℝ) : ℝ :=
  min (RawReference.Explicit.referenceLoadTolerance (α/8)) (1/2)
def rawStockAvoidBudget (a b α : ℝ) : ℝ :=
  RawReference.Explicit.referenceAvoidBudget a b (α/8)
def rawStockCompletion (α ρ : ℝ) : ℝ := α/2*(stockRate ρ)^2/2
def rawStockOrder (a b α ρ : ℝ) : ℕ :=
  max (RawReference.Explicit.referenceOrder a b (α/8))
    (BasalSampling.Explicit.samplingCut (stockRate ρ) (α/2))

theorem raw_stock_windows_pos (a b α : ℝ) (h : ℕ) (ha : 0<a) (hab : a≤b) (hα : 0<α) :
    0<rawStockBudget a b α h ∧ 0<rawStockLoadTolerance α ∧ 0<rawStockAvoidBudget a b α := by
  exact ⟨lt_min (RawReference.Explicit.stockBudget_pos h ha hab hα) (by positivity),
    lt_min (RawReference.Explicit.referenceLoadTolerance_pos (by positivity)) (by norm_num),
    RawReference.Explicit.referenceAvoidBudget_pos ha hab (by positivity)⟩

theorem raw_stock_completion_pos {α ρ : ℝ} (hα : 0<α) (hρ : 0<ρ) : 0<rawStockCompletion α ρ := by
  unfold rawStockCompletion stockRate
  positivity

theorem reserve_from_raw_profile_explicit {I : Type} (F : Set (Multiset I))
    (a b α : ℝ) (h : ℕ) (ha : 0 < a) (hab : a ≤ b) (hα : 0 < α) :
    ∀ ρ : ℝ, 0 < ρ →
        ∀ {V : Type} [Fintype V] (H : Host V I) (μ : Finset V → ℝ)
          (S B : Finset (Sym2 V)) (DS : Finset (Finset V)) (dS dB : ℕ),
          rawStockOrder a b α ρ ≤ Fintype.card V → CommonNbrCond H F α → HingeCond H F α h →
          (∀ T, IsAllowed H F T → a/Fintype.card V ≤ μ T ∧ μ T ≤ b/Fintype.card V) →
          (∀ e ∈ edges H, |bdry H F μ e-1| ≤ rawStockLoadTolerance α) →
          S ⊆ edges H → IsDecomposition H F S DS → Disjoint S B →
          (∀ v, degIn S v ≤ dS) → (dS:ℝ) ≤ rawStockBudget a b α h*Fintype.card V →
          (∀ v, degIn B v ≤ dB) → (dB:ℝ) ≤ rawStockAvoidBudget a b α*Fintype.card V →
          ∃ D : Finset (Finset V), IsDecomposition H F (cover D) D ∧
            Disjoint (cover D) (S∪B) ∧
            (∀ v, (degIn (cover D) v:ℝ) < ρ*Fintype.card V) ∧
            ∀ u v, H.G.Adj u v → rawStockCompletion α ρ*Fintype.card V ≤ (good H F D u v).card := by
  let θR := RawReference.Explicit.stockBudget a b α h
  let εR := RawReference.Explicit.referenceLoadTolerance (α/8)
  let γ := RawReference.Explicit.referenceAvoidBudget a b (α/8)
  have hθR : 0<θR := RawReference.Explicit.stockBudget_pos h ha hab hα
  have hεR : 0<εR := RawReference.Explicit.referenceLoadTolerance_pos (by positivity)
  have hγ : 0<γ := RawReference.Explicit.referenceAvoidBudget_pos ha hab (by positivity)
  let θ := min θR (α/8)
  let ε := min εR (1/2)
  have hθ : 0<θ := lt_min hθR (by positivity)
  have hε : 0<ε := lt_min hεR (by norm_num)
  intro ρ hρ
  let q := min (ρ/12) (1/2)
  have hq : 0<q := lt_min (by positivity) (by norm_num)
  let nR := RawReference.Explicit.referenceOrder a b (α/8)
  let nSample := BasalSampling.Explicit.samplingCut q (α/2)
  intro V _ H μ S B DS dS dB hn h3 h4 hμ hload hS hDS hSB hdS hdθ hdB hdγ
  change max nR nSample ≤ Fintype.card V at hn

  have hε1 : ε < 1 := (min_le_right _ _).trans_lt (by norm_num)
  have hCover : ∀ e∈edges H, ∃ T, IsAllowed H F T ∧ e∈triEdges T := by
    intro e he
    by_contra hNo
    have hZero : bdry H F μ e = 0 := by
      unfold bdry
      apply sum_eq_zero
      intro T hT
      have hAllowed : IsAllowed H F T := by simpa [allowed] using hT
      have hMissing : e∉triEdges T := fun heT => hNo ⟨T,hAllowed,heT⟩
      simp only [indR,if_neg hMissing,mul_zero]
    have hh := hload e he
    change |bdry H F μ e-1| ≤ ε at hh
    rw [hZero] at hh
    norm_num at hh
    linarith
  obtain ⟨E₀,D₀,hSE,hE,hD₀,hDS₀,hEB,hHoles⟩ :=
    RawReference.Explicit.dense_reference_containing_stock_explicit F a b α h ha hab hα (α/8) (by positivity) H μ S B DS dS dB ((le_max_left _ _).trans hn) h4 hμ
      (fun e he => (hload e he).trans (min_le_left _ _)) hS hDS hSB hdS
      (hdθ.trans (mul_le_mul_of_nonneg_right (min_le_left _ _) (by positivity))) hdB hdγ
  let P := D₀\DS
  have hPdec : IsDecomposition H F (E₀\S) P := by
    simpa only [hDS.2.2] using hD₀.sdiff_sub hDS₀
  have hPack : IsPacking H F P := ⟨hPdec.1,hPdec.2.1⟩
  have hPE : cover P = E₀\S := hPdec.2.2
  have hPdis : Disjoint (cover P) (S∪B) := by
    rw [hPE,disjoint_union_right]
    exact ⟨sdiff_disjoint,hEB.mono_left sdiff_subset⟩
  have hMissing : ∀ v, (((edges H\cover P).filter (fun e => v ∈ e)).card:ℝ) ≤
      (α/4)*Fintype.card V := by
    intro v
    have hs : (edges H\cover P).filter (fun e => v ∈ e) ⊆
        (edges H\E₀).filter (fun e => v ∈ e) ∪ S.filter (fun e => v ∈ e) := by
      intro e he
      obtain ⟨he,hv⟩ := mem_filter.mp he
      by_cases heS : e ∈ S
      · exact mem_union_right _ (mem_filter.mpr ⟨heS,hv⟩)
      · apply mem_union_left
        refine mem_filter.mpr ⟨mem_sdiff.mpr ⟨(mem_sdiff.mp he).1,?_⟩,hv⟩
        intro heE
        exact (mem_sdiff.mp he).2 (hPE.symm ▸ mem_sdiff.mpr ⟨heE,heS⟩)
    have hc : (((edges H\cover P).filter (fun e => v ∈ e)).card:ℝ) ≤
        degIn (edges H\E₀) v+degIn S v := by
      exact_mod_cast (card_le_card hs).trans (card_union_le _ _)
    have hstock : (degIn S v:ℝ) ≤ (α/8)*Fintype.card V :=
      (show (degIn S v:ℝ) ≤ dS by exact_mod_cast hdS v).trans
        (hdθ.trans (mul_le_mul_of_nonneg_right (min_le_right _ _) (by positivity)))
    nlinarith [hHoles v]
  let A := {uv : V×V // H.G.Adj uv.1 uv.2}
  let u : A → V := fun t => t.val.1
  let v : A → V := fun t => t.val.2
  have hA : Fintype.card A ≤ Fintype.card V^2 := by
    calc
      Fintype.card A ≤ Fintype.card (V×V) := Fintype.card_subtype_le _
      _ = _ := by rw [Fintype.card_prod]; ring
  have hSupply : ∀ t : A, (α/2)*Fintype.card V ≤ (good H F P (u t) (v t)).card := by
    intro t
    obtain ⟨T,hT,heT⟩ := hCover s(u t,v t) (by simpa [TypedTriangle.edges,u,v] using t.property)
    obtain ⟨w,hw⟩ := eq_insert_of_mem_triEdges hT.1 heT
    have hTa : IsAllowed H F {u t,v t,w} := by
      rwa [tri_eq_insert_toFinset,←hw]
    have hh := good_supply h3 P hMissing hTa
    nlinarith only [hh]
  obtain ⟨D,hDP,hD,hSmall,hGood⟩ := BasalIncidence.Explicit.sample_packing_explicit q (α/2) hq ((min_le_right _ _).trans (by norm_num)) (by positivity) V I H F P hPack
    ((le_max_right _ _).trans hn) A u v hA hSupply
  refine ⟨D,hD,?_,?_,?_⟩
  · apply hPdis.mono_left
    intro e he
    obtain ⟨T,hT,heT⟩ := mem_biUnion.mp he
    exact mem_biUnion.mpr ⟨T,hDP hT,heT⟩
  · intro x
    have hh := hSmall x
    have hqρ : q ≤ ρ/12 := min_le_left _ _
    change (((cover D).filter (fun e => x ∈ e)).card:ℝ) < ρ*Fintype.card V
    nlinarith [mul_le_mul_of_nonneg_right hqρ (show (0:ℝ) ≤ Fintype.card V by positivity)]
  · intro x y hxy
    have hh := hGood ⟨(x,y),hxy⟩
    dsimp only [u,v] at hh
    change (α/2*q^2/2)*Fintype.card V ≤ (good H F D x y).card
    nlinarith only [hh]


#print axioms reserve_from_raw_profile_explicit
end TypedTriangle.BasalIncidence.Explicit
end BankPart13

section BankPart14
open Finset Classical
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace TypedTriangle.CatalogNative.Explicit
open SparseEdge Dispersal S07V42 S07V42.Explicit

def catalogCellSize (α β : ℝ) (h d c E d' c' E' : ℕ) : ℕ :=
  let U := rerouteSize β d c E d' c' E'
  boundedPieceSize (α/2) h (4*U)+4*U

def catalogCellDegreeBudget (α β : ℝ) (h : ℕ) : ℝ :=
  min (β/8) (boundedPieceBudget (α/2) h/2)

def catalogCellDeletionBudget (α β : ℝ) (h : ℕ) : ℝ :=
  min (ExplicitGeometry.deletionBudget α h) (coreDelta β h)

def catalogCellOrder (α β : ℝ) (h d c E d' c' E' : ℕ) : ℕ :=
  let U := rerouteSize β d c E d' c' E'
  2*boundedPieceOrder (α/2) h (4*U)+⌈40*(U:ℝ)/β⌉₊+1

theorem catalogCellDegreeBudget_pos {α β : ℝ} (h : ℕ) (hα : 0<α) (hβ : 0<β) :
    0<catalogCellDegreeBudget α β h := by
  unfold catalogCellDegreeBudget
  exact lt_min (by positivity) (div_pos (boundedPieceBudget_pos h (by positivity)) (by norm_num))

theorem catalogCellDeletionBudget_pos {α β : ℝ} (h : ℕ) (hα : 0<α) (hβ : 0<β) :
    0<catalogCellDeletionBudget α β h := by
  exact lt_min (ExplicitGeometry.deletionBudget_spec hα h).1 (by unfold coreDelta; positivity)

theorem native_catalog_cell_explicit (α β : ℝ) (h : ℕ) (hα : 0 < α) (hβ : 0 < β)
    (d c E d' c' E' : ℕ) :

      ∀ {V I : Type} [Fintype V] (H : Host V I) (F : Set (Multiset I)) (W : Finset V),
        CommonNbrCond H F α → HingeCond H F α h →
        SparseEdge.CommonNbrCond (H.G.comap (Subtype.val : {x // x ∈ W} → V))
          (H.lab ∘ Subtype.val) F β →
        SparseEdge.HingeCond (H.G.comap (Subtype.val : {x // x ∈ W} → V))
          (H.lab ∘ Subtype.val) F β h →
        coreN0 β h ≤ W.card → catalogCellOrder α β h d c E d' c' E' ≤ W.card →
        ∀ C0 : CoreCompression H.G H.lab F W d c E,
        ∀ Z : Finset V, (Z.card:ℝ) ≤ catalogCellDeletionBudget α β h*W.card →
        DelCompression H.G H.lab F Z d' c' E' →
        ∀ (B : Finset (Sym2 V)) (b : ℕ), (∀ v, degIn B v ≤ b) →
          (b:ℝ) ≤ catalogCellDegreeBudget α β h*W.card →
        ∀ v : Cat d (catRadius β d c E d' c' E'),
          gCat C0 (catRadius β d c E d' c' E') v ∈ KZ H.G H.lab F W Z → ∀ σ : Bool,
        ∃ A Y : Finset (Sym2 V), IsAbsorber H F A Y ∧ Disjoint (A∪Y) B ∧
          (∀ e ∈ A∪Y, ∀ z ∈ Z, z ∉ e) ∧
          (∀ e ∈ Y, e ∈ SparseEdge.edges (indG H.G (W\Z))) ∧
          (A∪Y).card ≤ catalogCellSize α β h d c E d' c' E' ∧
          chargeQ H.G H.lab F W Y =
            (if σ then gCat C0 (catRadius β d c E d' c' E') v
              else -gCat C0 (catRadius β d c E d' c' E') v) := by
  let U := rerouteSize β d c E d' c' E'
  let εA := boundedPieceBudget (α/2) h
  let EA := boundedPieceSize (α/2) h (4*U)
  let nA := boundedPieceOrder (α/2) h (4*U)
  have hεA : 0<εA := boundedPieceBudget_pos h (by positivity)
  let δ₀ := ExplicitGeometry.deletionBudget α h
  obtain ⟨hδ₀,hδhalf,hWin⟩ := ExplicitGeometry.deletionBudget_spec hα h
  intro V I _ H F W h3 h4 hc3 hc4 hnC hn C0 Z hZ CZ B b hB hb v hv σ
  change 2*nA+⌈40*(U:ℝ)/β⌉₊+1 ≤ W.card at hn

  have hWn : (W.card:ℝ) ≤ Fintype.card V := by exact_mod_cast card_le_univ W
  have hW0 : (0:ℝ) ≤ W.card := by positivity
  have hZ₀ : (Z.card:ℝ) ≤ δ₀*Fintype.card V :=
    (hZ.trans (mul_le_mul_of_nonneg_right (min_le_left _ _) hW0)).trans
      (mul_le_mul_of_nonneg_left hWn hδ₀.le)
  have hZcore : (Z.card:ℝ) ≤ coreDelta β h*W.card :=
    hZ.trans (mul_le_mul_of_nonneg_right (min_le_right _ _) hW0)
  obtain ⟨x,hxM,hxL,hxU,hxc⟩ := native_reroute_explicit h hβ d c E d' c' E' hc3 hc4 hnC C0 hZcore CZ v hv
  let xs : Sym2 V → ℤ := if σ then x else -x
  have hxsM : xs ∈ MZ H.G H.lab F W Z := by
    dsimp [xs]; split_ifs <;> first | exact hxM | exact neg_mem hxM
  have hxsL : xs ∈ LamDel H.G H.lab F Z := by
    dsimp [xs]; split_ifs <;> first | exact hxL | exact neg_mem hxL
  have hxsU : Dispersal.l1E xs ≤ U := by
    dsimp [xs]; split_ifs
    · exact hxU
    · simpa only [Dispersal.l1E,Pi.neg_apply,abs_neg] using hxU
  have hxsc : clsQ H.G H.lab F W xs =
      (if σ then gCat C0 (catRadius β d c E d' c' E') v else -gCat C0 (catRadius β d c E d' c' E') v) := by
    dsimp [xs]; split_ifs
    · exact hxc
    · rw [←hxc]; rfl
  have hZhalf : (Z.card:ℝ) ≤ (Fintype.card V:ℝ)/2 := by
    have hh := mul_le_mul_of_nonneg_right hδhalf (by positivity : (0:ℝ) ≤ Fintype.card V)
    linarith
  have hgeom := hWin (by positivity : (0:ℝ) ≤ Fintype.card V) hZ₀
  obtain ⟨hg3,hg4⟩ := original_geometry_restrictedHost hα.le h3 h4 Z hgeom.1 hgeom.2
  have hcnt := card_survivors_add_card Z
  have hcntR : (Fintype.card (Survivors Z):ℝ)+Z.card = Fintype.card V := by exact_mod_cast hcnt
  have hNA : nA ≤ Fintype.card (Survivors Z) := by
    have hbig : (2:ℝ)*nA ≤ Fintype.card V := by
      have hh : 2*nA ≤ W.card := by omega
      exact_mod_cast hh.trans (card_le_univ W)
    exact_mod_cast (by linarith : (nA:ℝ) ≤ Fintype.card (Survivors Z))
  have hbA : (b:ℝ) ≤ εA*Fintype.card (Survivors Z) := by
    have hh := hb.trans (mul_le_mul_of_nonneg_right (min_le_right _ _) hW0)
    have hw : (W.card:ℝ) ≤ 2*Fintype.card (Survivors Z) := by linarith
    have hh' := mul_le_mul_of_nonneg_left hw hεA.le
    nlinarith
  have hbβ : (b:ℝ) ≤ β/8*W.card := hb.trans (mul_le_mul_of_nonneg_right (min_le_left _ _) hW0)
  have hzβ : (Z.card:ℝ) ≤ β/2*W.card :=
    hZcore.trans (mul_le_mul_of_nonneg_right (coreDelta_le hβ h) hW0)
  have hbig : 40*(U:ℝ)/β < W.card := by
    have hh := Nat.le_ceil (40*(U:ℝ)/β)
    have hh' : ((2*nA+⌈40*(U:ℝ)/β⌉₊+1:ℕ):ℝ) ≤ W.card := by exact_mod_cast hn
    push_cast at hh'
    linarith [show (0:ℝ) ≤ nA by positivity]
  have hroom : 5*(U:ℝ)+Z.card+2*b < β*W.card := by
    rw [div_lt_iff₀ hβ] at hbig
    linarith
  obtain ⟨Y,hYL,hYB,hYE,hYc⟩ := polarize hc3 Z hB hxsM hxsU hroom
  have hlatD : SparseEdge.lattice (indG H.G (W\Z)) H.lab F ≤ LamDel H.G H.lab F Z :=
    S07V37.lattice_mono (indG_le_delG H.G sdiff_disjoint) H.lab F
  have hlatC : SparseEdge.lattice (indG H.G (W\Z)) H.lab F ≤ LamCore H.G H.lab F W :=
    S07V37.lattice_mono (indG_mono H.G sdiff_subset) H.lab F
  have hYphys : IsPhysical (vertexDeleted H Z) F Y := by
    have heq : ind Y = (ind Y-xs)+xs := by abel
    change ind Y ∈ LamDel H.G H.lab F Z
    rw [heq]
    exact add_mem (hlatD hYL) hxsL
  have hYav : ∀ e ∈ Y, ∀ z ∈ Z, z ∉ e := by
    intro e he z hz hze
    have he' := hYE e he
    induction e using Sym2.ind with
    | h a b =>
      rw [SparseEdge.mem_edges,SimpleGraph.mem_edgeSet] at he'
      rw [Sym2.mem_iff] at hze
      rcases hze with rfl | rfl
      exacts [(mem_sdiff.mp he'.2.1).2 hz,(mem_sdiff.mp he'.2.2).2 hz]
  obtain ⟨A,hA,hAB,hAc,hAZ⟩ := bounded_piece_absorber_deleted_explicit (α/2) h (4*U) (by positivity) H F Z hNA hg3 hg4 Y hYphys hYc
    (fun e he z hz => fun h => hYav e he z h hz) B b hB hbA
  refine ⟨A,Y,hA,disjoint_union_left.mpr ⟨hAB,hYB⟩,?_,hYE,
    (card_union_le _ _).trans (Nat.add_le_add hAc hYc),?_⟩
  · intro e he z hz hze
    rcases mem_union.mp he with he | he
    · exact hAZ e he z hze hz
    · exact hYav e he z hz hze
  · rw [chargeQ_eq,←hxsc]
    unfold clsQ
    exact (Submodule.Quotient.eq _).2 (hlatC hYL)

#print axioms native_catalog_cell_explicit
end TypedTriangle.CatalogNative.Explicit
end BankPart14

section BankPart15
open Finset Classical
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace TypedTriangle.CatalogNative.Explicit
open S07V42 S07V42.Explicit S07V43 S07V40 ProtectedBank

theorem native_protected_child_bank_explicit (α β : ℝ) (h : ℕ) (hα : 0 < α) (hβ : 0 < β)
    (d c E d' c' E' : ℕ) :

      ∀ {V I : Type} [Fintype V] (H : Host V I) (F : Set (Multiset I)) (W : Finset V),
        CommonNbrCond H F α → HingeCond H F α h →
        SparseEdge.CommonNbrCond (H.G.comap (Subtype.val : {x // x ∈ W} → V))
          (H.lab ∘ Subtype.val) F β →
        SparseEdge.HingeCond (H.G.comap (Subtype.val : {x // x ∈ W} → V))
          (H.lab ∘ Subtype.val) F β h →
        coreN0 β h ≤ W.card → catalogCellOrder α β h d c E d' c' E' ≤ W.card →
        ∀ C0 : CoreCompression H.G H.lab F W d c E,
        ∀ P q zmax N b0 : ℕ, 0 < q →
        (zmax:ℝ) ≤ min (catalogCellDeletionBudget α β h) (coreDelta β h)*W.card →
        ((b0+q+(childSetting C0 (catRadius β d c E d' c' E') P q (catalogCellSize α β h d c E d' c' E') zmax).Bstar*(catalogCellSize α β h d c E d' c' E'):ℕ):ℝ) ≤ catalogCellDegreeBudget α β h*W.card →
        (∀ Z : Finset V, Z.card ≤ zmax → DelCompression H.G H.lab F Z d' c' E') →
        2*(catalogCellSize α β h d c E d' c' E')*(childSetting C0 (catRadius β d c E d' c' E') P q (catalogCellSize α β h d c E d' c' E') zmax).Bstar*N ≤ q*zmax →
        ∀ F0 : Finset (Sym2 V), (∀ v, degIn F0 v ≤ b0) →
        let S := childSetting C0 (catRadius β d c E d' c' E') P q (catalogCellSize α β h d c E d' c' E') zmax
        MacroBank (protect S F0) (Fintype.card (Cat d (catRadius β d c E d' c' E'))) N ∧
          Disjoint (Br (protect S F0) N) F0 := by
  let Ecell := catalogCellSize α β h d c E d' c' E'
  let ε := catalogCellDegreeBudget α β h
  let δ := catalogCellDeletionBudget α β h
  intro V I _ H F W h3 h4 hc3 hc4 hnC hn C0 P q zmax N b0 hq hz hbud CZ hcap F0 hF0

  let S := childSetting C0 (catRadius β d c E d' c' E') P q Ecell zmax
  have hzδ : (zmax:ℝ) ≤ δ*W.card := hz.trans
    (mul_le_mul_of_nonneg_right (min_le_left _ _) (by positivity))
  have hzcore : (zmax:ℝ) ≤ coreDelta β h*W.card := hz.trans
    (mul_le_mul_of_nonneg_right (min_le_right _ _) (by positivity))
  have hSup : CellSupply (protect S F0) := by
    intro B Z hB hZ l hl
    have hl' : S.g l.2.1 ∈ S.K Z := hl
    have hlRaw := (childSetting_g_mem_K_iff C0 (catRadius β d c E d' c' E')
      P q Ecell zmax l.2.1 Z).mp hl'
    have hbU : ∀ v, degIn (B∪F0) v ≤ b0+q+S.Bstar*Ecell := by
      intro v
      have hh : degIn (B∪F0) v ≤ degIn B v+degIn F0 v := by
        unfold degIn
        rw [filter_union]
        exact card_union_le _ _
      have hb := hB v
      have hf := hF0 v
      change degIn B v ≤ q+S.Bstar*Ecell at hb
      omega
    obtain ⟨A,Y,hA,hDis,hAv,hYE,hcard,hcharge⟩ := native_catalog_cell_explicit α β h hα hβ d c E d' c' E' H F W h3 h4 hc3 hc4 hnC hn C0 Z
      ((Nat.cast_le.mpr hZ).trans hzδ) (CZ Z hZ) (B∪F0) (b0+q+S.Bstar*Ecell)
      hbU hbud l.2.1 hlRaw l.1
    have hGood : GoodCell S (B∪F0) Z l ⟨A,Y⟩ := by
      refine ⟨hA.1,hA.2.1,hA.2.2,hDis,hAv,hcard,?_⟩
      show charge (tagW H.G H.lab F W) Y =
        sgnQ l.1 ((gCat C0 (catRadius β d c E d' c' E') l.2.1,0) : ClassQ H.G H.lab F W × ℤ)
      rw [charge_tagW_eq_sgnQ_iff]
      refine ⟨?_,fun e he => edge_child_of_deleted (hYE e he)⟩
      rw [hcharge]
      rfl
    exact ⟨⟨A,Y⟩,goodCell_protect (S:=S) F0 B Z l _ hGood⟩
  have hM : MacroBank (protect S F0)
      (Fintype.card (Cat d (catRadius β d c E d' c' E'))) N :=
    macro_bank hq hSup (protect_basal F0 (childSetting_basal C0 _ P q Ecell zmax))
      (S07V43.Explicit.childSetting_chainBound_explicit hβ hc3 hc4 hnC C0 P q Ecell zmax hzcore CZ) hcap
  exact ⟨hM,protected_bank_disjoint F0 hM⟩


#print axioms native_protected_child_bank_explicit
end TypedTriangle.CatalogNative.Explicit
end BankPart15

section BankPart16
namespace TypedTriangle.CatalogNative.Explicit

def bankCatalogRadius (α β : ℝ) (h : ℕ) : ℕ :=
  S07V42.Explicit.catRadius β
    (catalogDimension β h) (catalogCoefficient β h) (catalogColumn β h)
    (catalogDimension (α/2) h) (catalogCoefficient (α/2) h) (catalogColumn (α/2) h)

def bankCatalogSize (α β : ℝ) (h : ℕ) : ℕ :=
  (2*bankCatalogRadius α β h+1)^(catalogDimension β h)

def bankCellSize (α β : ℝ) (h : ℕ) : ℕ :=
  catalogCellSize α β h
    (catalogDimension β h) (catalogCoefficient β h) (catalogColumn β h)
    (catalogDimension (α/2) h) (catalogCoefficient (α/2) h) (catalogColumn (α/2) h)

def bankCellOrder (α β : ℝ) (h : ℕ) : ℕ :=
  catalogCellOrder α β h
    (catalogDimension β h) (catalogCoefficient β h) (catalogColumn β h)
    (catalogDimension (α/2) h) (catalogCoefficient (α/2) h) (catalogColumn (α/2) h)

def bankProtectionBudget (α β : ℝ) (h : ℕ) : ℝ := catalogCellDegreeBudget α β h/2

def bankTolerance (α β εcap : ℝ) (h : ℕ) : ℝ := min (bankProtectionBudget α β h) εcap

def bankDeletionBudget (α β δcap : ℝ) (h : ℕ) : ℝ :=
  min (ExplicitGeometry.deletionBudget α h)
    (min (min (catalogCellDeletionBudget α β h) (S07V42.coreDelta β h)) δcap)

def bankCopies (α β : ℝ) (h P : ℕ) : ℕ := 2*bankCatalogSize α β h*P

def bankRoundRate (α β εcap δcap : ℝ) (h P : ℕ) : ℝ :=
  quadraticBankRate (bankTolerance α β εcap h) (bankDeletionBudget α β δcap h)
    (bankCellSize α β h) (bankCopies α β h P)

def bankOrder (α β εcap δcap : ℝ) (h P : ℕ) : ℕ :=
  max (catalogCompressionOrder α β h) (max (bankCellOrder α β h)
    (max (S07V42.coreN0 β h)
      (quadraticBankOrder (bankTolerance α β εcap h) (bankDeletionBudget α β δcap h)
        (bankCellSize α β h) (bankCopies α β h P))))

theorem bankProtectionBudget_pos {α β : ℝ} (h : ℕ) (hα : 0<α) (hβ : 0<β) :
    0<bankProtectionBudget α β h :=
  div_pos (catalogCellDegreeBudget_pos h hα hβ) (by norm_num)

theorem bankTolerance_pos {α β εcap : ℝ} (h : ℕ)
    (hα : 0<α) (hβ : 0<β) (hεcap : 0<εcap) : 0<bankTolerance α β εcap h :=
  lt_min (bankProtectionBudget_pos h hα hβ) hεcap

theorem bankDeletionBudget_pos {α β δcap : ℝ} (h : ℕ)
    (hα : 0<α) (hβ : 0<β) (hδcap : 0<δcap) : 0<bankDeletionBudget α β δcap h := by
  exact lt_min (ExplicitGeometry.deletionBudget_spec hα h).1
    (lt_min (lt_min (catalogCellDeletionBudget_pos h hα hβ)
      (by unfold S07V42.coreDelta; positivity)) hδcap)

theorem bankRoundRate_pos {α β εcap δcap : ℝ} (h P : ℕ)
    (hα : 0<α) (hβ : 0<β) (hεcap : 0<εcap) (hδcap : 0<δcap) :
    0<bankRoundRate α β εcap δcap h P :=
  quadraticBankRate_pos _ _ (bankTolerance_pos h hα hβ hεcap)
    (bankDeletionBudget_pos h hα hβ hδcap)

end TypedTriangle.CatalogNative.Explicit
end BankPart16

section BankPart17
open Finset Classical
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace TypedTriangle.CatalogNative.Explicit
open S07V42 S07V42.Explicit S07V43 S07V40 ProtectedBank

theorem native_protected_geometric_bank_early_protection_explicit
    (α β : ℝ) (h : ℕ) (hα : 0<α) (hβ : 0<β)
    (P : ℕ) (εcap δcap : ℝ) (hεcap : 0<εcap) (hδcap : 0<δcap) :
    ∀ {V I : Type} [Fintype V] (H : Host V I) (F : Set (Multiset I)) (W : Finset V),
        bankOrder α β εcap δcap h P ≤ W.card → CommonNbrCond H F α → HingeCond H F α h →
        SparseEdge.CommonNbrCond (H.G.comap (Subtype.val : {x // x ∈ W} → V))
          (H.lab ∘ Subtype.val) F β →
        SparseEdge.HingeCond (H.G.comap (Subtype.val : {x // x ∈ W} → V))
          (H.lab ∘ Subtype.val) F β h →
        ∃ C0 : CoreCompression H.G H.lab F W (catalogDimension β h) (catalogCoefficient β h) (catalogColumn β h), ∃ q z : ℕ,
          0 < q ∧ (bankTolerance α β εcap h)/4*W.card ≤ (q:ℝ) ∧ (z:ℝ) ≤ δcap*W.card ∧
          (∀ Z : Finset V, Z.card ≤ z → Nonempty (DelCompression H.G H.lab F Z (catalogDimension (α/2) h) (catalogCoefficient (α/2) h) (catalogColumn (α/2) h))) ∧
          ∀ F0 : Finset (Sym2 V), (∀ v, (degIn F0 v:ℝ) ≤ bankProtectionBudget α β h*W.card) →
          let S := childSetting C0 (bankCatalogRadius α β h) P q (bankCellSize α β h) z
          let N := ⌊bankRoundRate α β εcap δcap h P*(W.card:ℝ)^2⌋₊
          MacroBank (protect S F0) (Fintype.card (Cat (catalogDimension β h) (bankCatalogRadius α β h))) N ∧
            Disjoint (Br (protect S F0) N) F0 ∧
            ∀ v, (deg (Br (protect S F0) N) v:ℝ) < bankTolerance α β εcap h*W.card := by
  let d := catalogDimension β h
  let c := catalogCoefficient β h
  let E := catalogColumn β h
  let d' := catalogDimension (α/2) h
  let c' := catalogCoefficient (α/2) h
  let E' := catalogColumn (α/2) h
  let Ecell := bankCellSize α β h
  let εb := catalogCellDegreeBudget α β h
  let δb := min (catalogCellDeletionBudget α β h) (coreDelta β h)
  let δc := ExplicitGeometry.deletionBudget α h
  let nc := catalogCompressionOrder α β h
  let nb := bankCellOrder α β h
  have hεb : 0<εb := catalogCellDegreeBudget_pos h hα hβ
  have hδb : 0<δb := lt_min (catalogCellDeletionBudget_pos h hα hβ) (by unfold coreDelta; positivity)
  have hδc : 0<δc := (ExplicitGeometry.deletionBudget_spec hα h).1
  let ε := min (εb/2) εcap
  have hε : 0<ε := lt_min (by positivity) hεcap
  let δ := min δc (min δb δcap)
  have hδ : 0<δ := lt_min hδc (lt_min hδb hδcap)
  let B := 2*Fintype.card (Cat d (bankCatalogRadius α β h))*P
  have hCat : Fintype.card (Cat d (bankCatalogRadius α β h)) = bankCatalogSize α β h := by
    simpa only [d,bankCatalogSize] using card_Cat (catalogDimension β h) (bankCatalogRadius α β h)
  have hB : B = bankCopies α β h P := by dsimp [B,bankCopies]; rw [hCat]
  let κ := quadraticBankRate ε δ Ecell B
  let nq := quadraticBankOrder ε δ Ecell B
  intro V I _ H F W hn h3 h4 hc3 hc4
  change max nc (max nb (max (coreN0 β h) (quadraticBankOrder ε δ Ecell (bankCopies α β h P)))) ≤ W.card at hn
  rw [← hB] at hn
  have hκEq : bankRoundRate α β εcap δcap h P = κ := by
    dsimp only [bankRoundRate,κ,bankTolerance,bankProtectionBudget,bankDeletionBudget,ε,εb,δ,δc,δb,Ecell]
    rw [hB]
  simp only [hκEq]

  have hnc : nc ≤ W.card := (le_max_left _ _).trans hn
  have hnb : nb ≤ W.card := (le_max_left _ _).trans ((le_max_right _ _).trans hn)
  have hnCore : coreN0 β h ≤ W.card :=
    (le_max_left _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans hn))
  have hnq : nq ≤ W.card :=
    (le_max_right _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans hn))
  obtain ⟨⟨C0⟩,hCZ⟩ := native_all_catalog_compressions_explicit α β h hα hβ H F W hnc h3 h4 hc3 hc4
  let q := ⌊ε*W.card/2⌋₊
  let z := ⌊δ*W.card⌋₊
  obtain ⟨hq,hz,hdegree,hcap,hql⟩ := quadratic_bank_budget_explicit ε δ Ecell B hε hδ W.card hnq
  have hzC : (z:ℝ) ≤ δc*W.card := hz.trans
    (mul_le_mul_of_nonneg_right (min_le_left _ _) (by positivity))
  have hzB : (z:ℝ) ≤ δb*W.card := hz.trans
    (mul_le_mul_of_nonneg_right ((min_le_right _ _).trans (min_le_left _ _)) (by positivity))
  have hzCap : (z:ℝ) ≤ δcap*W.card := hz.trans
    (mul_le_mul_of_nonneg_right ((min_le_right _ _).trans (min_le_right _ _)) (by positivity))
  let CZ : ∀ Z : Finset V, Z.card ≤ z → DelCompression H.G H.lab F Z d' c' E' :=
    fun Z hZ => Classical.choice (hCZ Z ((Nat.cast_le.mpr hZ).trans hzC))
  refine ⟨C0,q,z,hq,hql,hzCap,fun Z hZ => ⟨CZ Z hZ⟩,?_⟩
  intro F0 hF0
  let b0 := ⌊(εb/2)*W.card⌋₊
  have hb0 : ∀ v, degIn F0 v ≤ b0 := fun v => Nat.le_floor (hF0 v)
  have hb0R : (b0:ℝ) ≤ (εb/2)*W.card := Nat.floor_le (by positivity)
  have hdegreeHalf : ((q+B*Ecell:ℕ):ℝ) ≤ (εb/2)*W.card := hdegree.trans
    (mul_le_mul_of_nonneg_right (min_le_left _ _) (by positivity))
  have hbudget : ((b0+q+B*Ecell:ℕ):ℝ) ≤ εb*W.card := by
    push_cast at hdegreeHalf ⊢
    linarith
  obtain ⟨hM,hDis⟩ := native_protected_child_bank_explicit α β h hα hβ d c E d' c' E' H F W h3 h4 hc3 hc4 hnCore hnb C0 P q z
    ⌊κ*(W.card:ℝ)^2⌋₊ b0 hq hzB hbudget CZ hcap F0 hb0
  refine ⟨hM,hDis,?_⟩
  intro v
  exact (show (deg (Br (protect (childSetting C0 (bankCatalogRadius α β h) P q Ecell z) F0)
    ⌊κ*(W.card:ℝ)^2⌋₊) v:ℝ) < (q+B*Ecell:ℕ) by exact_mod_cast hM.maxdeg v).trans_le hdegree



#print axioms native_protected_geometric_bank_early_protection_explicit
end TypedTriangle.CatalogNative.Explicit
end BankPart17
