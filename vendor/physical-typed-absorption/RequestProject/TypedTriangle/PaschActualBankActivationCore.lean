module
public import RequestProject.TypedTriangle.PaschActualBankStrata
public import RequestProject.S07V47.Shape
public import RequestProject.S07V47.Criteria
public import RequestProject.TypedTriangle.PaschAmbientBankSetting
public import RequestProject.TypedTriangle.ExplicitPhysicalMonitorWeights
public import RequestProject.TypedTriangle.G4MomentToProtectedBank
public import RequestProject.TypedTriangle.G4ActualMomentCap
public import RequestProject.TypedTriangle.CoreEdgeGraph
public import RequestProject.TypedTriangle.PaschEmbeddingStatistics
public import RequestProject.TypedTriangle.PaschAmbientCellModes
set_option maxHeartbeats 4000000 -- build option (original: -DmaxHeartbeats=1600000; raised)
set_option maxRecDepth 16384 -- build option (original: -DmaxRecDepth=8192; raised)
@[expose] public section
noncomputable section

section
open Finset Classical Submodule
set_option autoImplicit false
set_option maxHeartbeats 600000
namespace TypedTriangle.Pasch.ActualAllocation
open TypedTriangle.SparseEdge TypedTriangle.ComponentRows TypedTriangle.Composition
open TypedTriangle.Dispersal S07V42 S07V34 S07V32 S07V44 S07V43 S07V40 S07V46
variable {V I : Type*} [Fintype V] {H : SimpleGraph V} {lab : V → I}
  {F : Set (Multiset I)} {W : Finset V} {d c E : ℕ}
variable (H lab F W) in
/-- the stratum chain of an arbitrary setting: `K_{Zstrat ℓ}` for `ℓ  ≤  J`, then `⊥` -/
def pChain (Z : ℕ → Finset V) (J ℓ : ℕ) : AddSubgroup (ClassQ H lab F W) :=
  if ℓ  ≤  J then (KZ H lab F W (Z ℓ)).toAddSubgroup else ⊥

/-- step monitors with the FULL monitor at the last step -/
def pMonF (C0 : CoreCompression H lab F W d c E) {R A M K : ℕ} (Z : ℕ → Finset V)
    (J : ℕ) (Pk : ∀ ℓ, ℓ  <  J → PhysicalMonitors C0 R (Z (ℓ + 1)) A M K)
    (Fm : FullMonitor C0 R A M K) (ℓ : ℕ) (y : ClassQ H lab F W) : ℝ :=
  if h : ℓ  <  J then monQ (physMon C0 (Dset C0 R (Z (ℓ + 1))) (Pk ℓ h).psi) y
  else monQ (physMon C0 ∅ Fm.psi) y

/-- step monitors LOCALIZED at every step (early stop) -/
def pMonL (C0 : CoreCompression H lab F W d c E) {R A M K : ℕ} (Z : ℕ → Finset V)
    (J : ℕ) (Pk : ∀ ℓ, ℓ  ≤  J → PhysicalMonitors C0 R (Z (ℓ + 1)) A M K)
    (ℓ : ℕ) (y : ClassQ H lab F W) : ℝ :=
  if h : ℓ  ≤  J then monQ (physMon C0 (Dset C0 R (Z (ℓ + 1))) (Pk ℓ h).psi) y else 0

variable (C0 : CoreCompression H lab F W d c E)

lemma pChain_le {Z : ℕ → Finset V} {J ℓ : ℕ} (hℓ : ℓ  ≤  J) :
    pChain H lab F W Z J ℓ = (KZ H lab F W (Z ℓ)).toAddSubgroup := by
  unfold pChain; rw [if_pos hℓ]

lemma pChain_succ {Z : ℕ → Finset V} {J : ℕ} : pChain H lab F W Z J (J + 1) = ⊥ := by
  unfold pChain; rw [if_neg (by omega)]

/-- the catalog support condition shared by both step interfaces -/
lemma active_support {R : ℕ} {Z : ℕ → Finset V} {J ℓ : ℕ} (hℓ : ℓ  ≤  J)
    (z : Cat d R → ℤ)
    (hz0 : ∀ v, v ∉ (univ.filter fun v => gCat C0 R v  ∈  KZ H lab F W (Z ℓ)) → z v = 0) :
    ∀ v, z v  ≠  0 → gCat C0 R v  ∈  pChain H lab F W Z J ℓ := by
  intro v hv
  have hvC : v  ∈  (univ.filter fun v => gCat C0 R v  ∈  KZ H lab F W (Z ℓ)) := by
    by_contra h; exact hv (hz0 v h)
  rw [pChain_le hℓ]
  exact (mem_filter.1 hvC).2

/-- **step interface, full monitor at the last step** (V46 `stepPay_strata`, any setting) -/
theorem stepPay_full {R A M K : ℕ} (Z : ℕ → Finset V) (J : ℕ)
    (Pk : ∀ ℓ, ℓ  <  J → PhysicalMonitors C0 R (Z (ℓ + 1)) A M K)
    (Fm : FullMonitor C0 R A M K) (hgen : ∀ j  ≤  J, CatalogGen C0 R (Z j)) :
    StepPay (gCat C0 R) (clsCore H lab F W).range (pChain H lab F W Z J)
      (pMonF C0 Z J Pk Fm) A M J := by
  refine ⟨gCat_mem_range C0, ?_, ?_⟩
  · intro ℓ hℓ y hy hyK
    obtain ⟨x, rfl⟩ := hy
    rw [clsCore_apply] at hyK ⊢
    rw [pChain_le hℓ] at hyK
    have hx : clsQ H lab F W (x : Sym2 V → ℤ)  ∈  AddSubgroup.closure (gCat C0 R ''
        ((univ.filter fun v => gCat C0 R v  ∈  KZ H lab F W (Z ℓ) : Finset _) : Set _)) := by
      rw [closure_active_eq C0 (hgen ℓ hℓ)]; exact hyK
    by_cases hlt : ℓ  <  J
    · obtain ⟨z, hz0, -, hzK, hzc⟩ := (Pk ℓ hlt).pay _ x hx
      refine ⟨z, active_support C0 hℓ z hz0, ?_, ?_⟩
      · rw [pChain_le (by omega)]; exact hzK
      · have hcg : ∀ a b : MCore H lab F W,
            clsQ H lab F W (a : Sym2 V → ℤ) = clsQ H lab F W (b : Sym2 V → ℤ) →
            physMon C0 _ (Pk ℓ hlt).psi a = physMon C0 _ (Pk ℓ hlt).psi b :=
          fun a b h => physMon_congr C0 _ _ h
        unfold pMonF
        rw [dif_pos hlt, monQ_clsQ _ hcg]
        have : ((wcost z : ℤ) : ℝ)  ≤ 
            (((A : ℤ) * (1 + S07V32.l1 (physMon C0 _ (Pk ℓ hlt).psi x)) : ℤ) : ℝ) := by
          rw [wcost_cast]; exact_mod_cast hzc
        push_cast at this ⊢
        exact this
    · obtain ⟨z, hz0, -, hz0', hzc⟩ := Fm.pay _ x hx
      refine ⟨z, active_support C0 hℓ z hz0, ?_, ?_⟩
      · unfold pChain; rw [if_neg (by omega)]
        exact (AddSubgroup.mem_bot).2 hz0'
      · have hcg : ∀ a b : MCore H lab F W,
            clsQ H lab F W (a : Sym2 V → ℤ) = clsQ H lab F W (b : Sym2 V → ℤ) →
            physMon C0 ∅ Fm.psi a = physMon C0 ∅ Fm.psi b :=
          fun a b h => physMon_congr C0 _ _ h
        unfold pMonF
        rw [dif_neg hlt, monQ_clsQ _ hcg]
        have : ((wcost z : ℤ) : ℝ)  ≤ 
            (((A : ℤ) * (1 + S07V32.l1 (physMon C0 ∅ Fm.psi x)) : ℤ) : ℝ) := by
          rw [wcost_cast]; exact_mod_cast hzc
        push_cast at this ⊢
        exact this
  · intro ℓ _ y hy u
    unfold pMonF
    by_cases hlt : ℓ  <  J
    · simp only [dif_pos hlt]
      exact monQ_word_le C0 _ _ (Pk ℓ hlt).box_le y hy u
    · simp only [dif_neg hlt]
      exact monQ_word_le C0 _ _ Fm.box_le y hy u

/-- **step interface, localized monitors at EVERY step** (early stop: the final subgroup
`K_{Zstrat (J+1)}` is zero, so the localized payment at step `J` is already exact) -/
theorem stepPay_local {R A M K : ℕ} (Z : ℕ → Finset V) (J : ℕ)
    (Pk : ∀ ℓ, ℓ  ≤  J → PhysicalMonitors C0 R (Z (ℓ + 1)) A M K)
    (hgen : ∀ j  ≤  J, CatalogGen C0 R (Z j))
    (hfin : (KZ H lab F W (Z (J + 1))).toAddSubgroup = ⊥) :
    StepPay (gCat C0 R) (clsCore H lab F W).range (pChain H lab F W Z J)
      (pMonL C0 Z J Pk) A M J := by
  refine ⟨gCat_mem_range C0, ?_, ?_⟩
  · intro ℓ hℓ y hy hyK
    obtain ⟨x, rfl⟩ := hy
    rw [clsCore_apply] at hyK ⊢
    rw [pChain_le hℓ] at hyK
    have hx : clsQ H lab F W (x : Sym2 V → ℤ)  ∈  AddSubgroup.closure (gCat C0 R ''
        ((univ.filter fun v => gCat C0 R v  ∈  KZ H lab F W (Z ℓ) : Finset _) : Set _)) := by
      rw [closure_active_eq C0 (hgen ℓ hℓ)]; exact hyK
    obtain ⟨z, hz0, -, hzK, hzc⟩ := (Pk ℓ hℓ).pay _ x hx
    refine ⟨z, active_support C0 hℓ z hz0, ?_, ?_⟩
    · by_cases hlt : ℓ  <  J
      · rw [pChain_le (by omega)]; exact hzK
      · have hJ : ℓ = J := by omega
        subst hJ
        rw [pChain_succ]
        have h' : clsQ H lab F W (x : Sym2 V → ℤ) + ∑ v, z v • gCat C0 R v  ∈ 
            (KZ H lab F W (Z (ℓ + 1))).toAddSubgroup := hzK
        rw [hfin] at h'
        exact h'
    · have hcg : ∀ a b : MCore H lab F W,
          clsQ H lab F W (a : Sym2 V → ℤ) = clsQ H lab F W (b : Sym2 V → ℤ) →
          physMon C0 _ (Pk ℓ hℓ).psi a = physMon C0 _ (Pk ℓ hℓ).psi b :=
        fun a b h => physMon_congr C0 _ _ h
      unfold pMonL
      rw [dif_pos hℓ, monQ_clsQ _ hcg]
      have : ((wcost z : ℤ) : ℝ)  ≤ 
          (((A : ℤ) * (1 + S07V32.l1 (physMon C0 _ (Pk ℓ hℓ).psi x)) : ℤ) : ℝ) := by
        rw [wcost_cast]; exact_mod_cast hzc
      push_cast at this ⊢
      exact this
  · intro ℓ hℓ y hy u
    unfold pMonL
    simp only [dif_pos hℓ]
    exact monQ_word_le C0 _ _ (Pk ℓ hℓ).box_le y hy u

end TypedTriangle.Pasch.ActualAllocation
end

section
open Finset Classical
set_option autoImplicit false
set_option maxHeartbeats 600000
namespace TypedTriangle.Pasch.ActualAllocation
open TypedTriangle.SparseEdge TypedTriangle.Dispersal S07V42 S07V34 S07V32 S07V44 S07V46
variable {V I : Type*} [Fintype V] {H : SimpleGraph V} {lab : V → I}
  {F : Set (Multiset I)} {W : Finset V} {d c E : ℕ}

/-- Concrete allocation from physical monitors and the proved prefix capacities.
The set sequence may be the pullback of the actual ambient bank strata. -/
theorem physical_allocation_full (C0 : CoreCompression H lab F W d c E)
    {R A M K P L J : ℕ} (hJL : J ≤ L) (Z : ℕ → Finset V) (hZ : Monotone Z) (m : ℕ → ℕ)
    (Pk : ∀ ℓ,ℓ < J → PhysicalMonitors C0 R (Z (ℓ+1)) A M K)
    (Fm : FullMonitor C0 R A M K) (hgen : ∀ j ≤ J,CatalogGen C0 R (Z j))
    {eta gamma tau : ℝ} (n q cp : ℕ) (hγ : 0 < gamma) (hη : 0 ≤ eta)
    (hqn : gamma*n ≤ q) (hθ : eta*(cp:ℝ)/gamma ≤ 1)
    (hpre : ∀ ℓ ≤ J,q*(Z (ℓ+1)).card ≤ cp*∑i ∈ range (ℓ+1),m i)
    (hP : 2*gammaL A M L ≤ P) (hm0 : 1 ≤ m 0)
    (hSJ : 1+tau*n^2 ≤ 2*∑i ∈ range (J+1),(m i:ℝ))
    (x : MCore H lab F W) (hx : clsQ H lab F W (x:Sym2 V→ℤ) ∈ KZ H lab F W (Z 0))
    (hloc : ∀ ℓ (h : ℓ < J),
      (S07V32.l1 (physMon C0 (Dset C0 R (Z (ℓ+1))) (Pk ℓ h).psi x):ℝ) ≤ eta*n*(Z (ℓ+1)).card)
    (hfull : (S07V32.l1 (physMon C0 ∅ Fm.psi x):ℝ) ≤ tau*n^2) :
    ∃ z : ℕ → Fin P → Cat d R → ℤ,
      (∀ i p v,z i p v ≠ 0 → i ≤ J ∧ gCat C0 R v ∈ KZ H lab F W (Z i)) ∧
      (∀ i p v,(z i p v).natAbs ≤ m i) ∧
      clsQ H lab F W (x:Sym2 V→ℤ)+∑i ∈ range (J+1),∑p,wcls (gCat C0 R) (z i p)=0 := by
  have hθ0 : 0 ≤ eta*(cp:ℝ)/gamma := by positivity
  let μ := pMonF C0 Z J Pk Fm
  have hcg : ∀ (D : Finset (Fin d → ℤ)) {K' : ℕ} (psi : Qt C0.S ⧸ Hgrp C0.S D →+ (Fin K' → ℤ))
      (a b : MCore H lab F W), clsQ H lab F W (a:Sym2 V→ℤ)=clsQ H lab F W (b:Sym2 V→ℤ) →
      physMon C0 D psi a=physMon C0 D psi b := fun D _ psi a b hab => physMon_congr C0 D psi hab
  have hloc' : ∀ ℓ < J,μ ℓ (clsQ H lab F W (x:Sym2 V→ℤ)) ≤ 
      eta*(cp:ℝ)/gamma*∑i ∈ range (ℓ+1),(m i:ℝ) := by
    intro ℓ hℓ
    have he : μ ℓ (clsQ H lab F W (x:Sym2 V→ℤ))=
        (S07V32.l1 (physMon C0 (Dset C0 R (Z (ℓ+1))) (Pk ℓ hℓ).psi x):ℝ) := by
      simp only [μ,pMonF,dif_pos hℓ]
      exact monQ_clsQ _ (hcg _ _) x
    rw [he]
    apply (hloc ℓ hℓ).trans
    have hh := local_scale hγ hη hqn (hpre ℓ hℓ.le)
    push_cast at hh ⊢
    exact hh
  have hfull' : μ J (clsQ H lab F W (x:Sym2 V→ℤ)) ≤ tau*n^2 := by
    have he : μ J (clsQ H lab F W (x:Sym2 V→ℤ))=(S07V32.l1 (physMon C0 ∅ Fm.psi x):ℝ) := by
      simp only [μ,pMonF,dif_neg (lt_irrefl J)]
      exact monQ_clsQ _ (hcg _ _) x
    rw [he]
    exact hfull
  have hanti : ∀ i j,i ≤ j → (KZ H lab F W (Z j)).toAddSubgroup ≤ 
      (KZ H lab F W (Z i)).toAddSubgroup := fun i j hij a ha => KZ_antitone H lab F W (hZ hij) ha
  exact S07V47.strata_allocation_of_cap hanti (fun ℓ hℓ => pChain_le hℓ) pChain_succ
    (stepPay_full C0 Z J Pk Fm hgen) m (clsQ H lab F W (x:Sym2 V→ℤ)) ⟨x,rfl⟩ hx
    (fun a hrec => S07V47.prefix_capacity_relaxed A M P L J hJL m a _ hθ0 hθ hrec hloc' hfull' hP hm0 hSJ)

/-- The early-stop branch uses the same real monitors, ending in the zero subgroup. -/
theorem physical_allocation_local (C0 : CoreCompression H lab F W d c E)
    {R A M K P L J : ℕ} (hJL : J ≤ L) (Z : ℕ → Finset V) (hZ : Monotone Z) (m : ℕ → ℕ)
    (Pk : ∀ ℓ,ℓ ≤ J → PhysicalMonitors C0 R (Z (ℓ+1)) A M K)
    (hgen : ∀ j ≤ J,CatalogGen C0 R (Z j))
    (hfin : (KZ H lab F W (Z (J+1))).toAddSubgroup=⊥)
    {eta gamma : ℝ} (n q cp : ℕ) (hγ : 0 < gamma) (hη : 0 ≤ eta)
    (hqn : gamma*n ≤ q) (hθ : eta*(cp:ℝ)/gamma ≤ 1)
    (hpre : ∀ ℓ ≤ J,q*(Z (ℓ+1)).card ≤ cp*∑i ∈ range (ℓ+1),m i)
    (hP : 2*gammaL A M L ≤ P) (hm0 : 1 ≤ m 0)
    (x : MCore H lab F W) (hx : clsQ H lab F W (x:Sym2 V→ℤ) ∈ KZ H lab F W (Z 0))
    (hloc : ∀ ℓ (h : ℓ ≤ J),
      (S07V32.l1 (physMon C0 (Dset C0 R (Z (ℓ+1))) (Pk ℓ h).psi x):ℝ) ≤ eta*n*(Z (ℓ+1)).card) :
    ∃ z : ℕ → Fin P → Cat d R → ℤ,
      (∀ i p v,z i p v ≠ 0 → i ≤ J ∧ gCat C0 R v ∈ KZ H lab F W (Z i)) ∧
      (∀ i p v,(z i p v).natAbs ≤ m i) ∧
      clsQ H lab F W (x:Sym2 V→ℤ)+∑i ∈ range (J+1),∑p,wcls (gCat C0 R) (z i p)=0 := by
  have hθ0 : 0 ≤ eta*(cp:ℝ)/gamma := by positivity
  let μ := pMonL C0 Z J Pk
  have hloc' : ∀ ℓ ≤ J,μ ℓ (clsQ H lab F W (x:Sym2 V→ℤ)) ≤ 
      eta*(cp:ℝ)/gamma*∑i ∈ range (ℓ+1),(m i:ℝ) := by
    intro ℓ hℓ
    have he : μ ℓ (clsQ H lab F W (x:Sym2 V→ℤ))=
        (S07V32.l1 (physMon C0 (Dset C0 R (Z (ℓ+1))) (Pk ℓ hℓ).psi x):ℝ) := by
      simp only [μ,pMonL,dif_pos hℓ]
      exact monQ_clsQ _ (fun a b hab => physMon_congr C0 _ _ hab) x
    rw [he]
    apply (hloc ℓ hℓ).trans
    have hh := local_scale hγ hη hqn (hpre ℓ hℓ)
    push_cast at hh ⊢
    exact hh
  have hanti : ∀ i j,i ≤ j → (KZ H lab F W (Z j)).toAddSubgroup ≤ 
      (KZ H lab F W (Z i)).toAddSubgroup := fun i j hij a ha => KZ_antitone H lab F W (hZ hij) ha
  exact S07V47.strata_allocation_of_cap hanti (fun ℓ hℓ => pChain_le hℓ) pChain_succ
    (stepPay_local C0 Z J Pk hgen hfin) m (clsQ H lab F W (x:Sym2 V→ℤ)) ⟨x,rfl⟩ hx
    (fun a hrec => S07V47.prefix_capacity_local A M P L J hJL m a _ hθ0 hθ hrec hloc' hP hm0)

end TypedTriangle.Pasch.ActualAllocation
end

section
open Finset Classical
set_option autoImplicit false
set_option maxHeartbeats 600000
namespace TypedTriangle.Pasch.RichBank.Actual
open S07V40 S07V43
variable {V I Q C : Type*} [Fintype V] [AddCommGroup Q] [Fintype C]
variable {H : Host V I} {F : Set (Multiset I)} {S : MacroSetting V Q C}
  {Ub : ℕ} {pay : ℝ} {R0 : Finset (Finset V)} {N : ℕ} {es : List (Entry V C S.P)}

/-- Selections are positions in this same list, even across several strata. -/
def selectedPositions (S : MacroSetting V Q C) (es : List (Entry V C S.P)) (J : ℕ)
    (z : ℕ → Fin S.P → C → ℤ) (hs : ∀j,(stratBank S es j).Supplies (z j)) :
    Finset (Fin es.length) := (range (J+1)).biUnion
      (fun j => (Bank.selJ (hs j)).image (fun i => i.1))

theorem selectedPayload_eq_strata (J : ℕ) (z : ℕ → Fin S.P → C → ℤ)
    (hs : ∀j,(stratBank S es j).Supplies (z j)) :
    selectedPayload es (selectedPositions S es J z hs)=
      (range (J+1)).biUnion (fun j => Bank.payload (hs j)) := by
  ext f
  constructor
  · intro hf
    obtain ⟨k,hk,hf⟩ := mem_biUnion.mp hf
    obtain ⟨j,hj,hk⟩ := mem_biUnion.mp hk
    obtain ⟨i,hi,hik⟩ := mem_image.mp hk
    subst k
    exact mem_biUnion.mpr ⟨j,hj,mem_biUnion.mpr ⟨i,hi,hf⟩⟩
  · intro hf
    obtain ⟨j,hj,hf⟩ := mem_biUnion.mp hf
    obtain ⟨i,hi,hf⟩ := mem_biUnion.mp hf
    exact mem_biUnion.mpr ⟨i.1,mem_biUnion.mpr ⟨j,hj,mem_image.mpr ⟨i,hi,rfl⟩⟩,hf⟩

theorem activated_payload_charge (hInv : Seeded.RunInv H F S Ub pay R0 N es)
    (J : ℕ) (z : ℕ → Fin S.P → C → ℤ) (hs : ∀j,(stratBank S es j).Supplies (z j)) :
    charge S.w ((range (J+1)).biUnion (fun j => Bank.payload (hs j)))=
      ∑j ∈ range (J+1),∑p,∑c,z j p c • S.g c := by
  have hDis : ((range (J+1):Finset ℕ):Set ℕ).PairwiseDisjoint
      (fun j => Bank.payload (hs j)) := by
    intro i hi j hj hij
    exact (stratBank_totals_disjoint hInv hij).mono
      (Bank.payload_subset_total (hs i)) (Bank.payload_subset_total (hs j))
  unfold charge
  rw [sum_biUnion hDis]
  exact sum_congr rfl (fun j _ => Bank.charge_payload (hs j) (stratBank_valid hInv j))

theorem activated_payload_card (hInv : Seeded.RunInv H F S Ub pay R0 N es)
    (J : ℕ) (z : ℕ → Fin S.P → C → ℤ) (hs : ∀j,(stratBank S es j).Supplies (z j)) :
    ((range (J+1)).biUnion (fun j => Bank.payload (hs j))).card ≤ 
      S.E*∑j ∈ range (J+1),∑p,∑c,(z j p c).natAbs := by
  calc _  ≤  ∑j ∈ range (J+1),(Bank.payload (hs j)).card := card_biUnion_le
    _  ≤  ∑j ∈ range (J+1),S.E*∑p,∑c,(z j p c).natAbs := by
      apply sum_le_sum
      intro j hj
      exact Bank.card_payload_le (hs j) (stratBank_valid hInv j)
        (fun i => occurrence_cell_size hInv.history.local_history (Function.Embedding.subtype _) i)
    _ = _ := (mul_sum _ _ _).symm

/-- Concrete activation uses the exact word supplied by the actual fibres.
Its complement includes every unused ON cell and its decomposition is the
stored selectedFamily, with local and external budgets kept separate. -/
theorem activate_actual_words (hInv : Seeded.RunInv H F S Ub pay R0 N es)
    (J : ℕ) (z : ℕ → Fin S.P → C → ℤ)
    (hact : ∀j p c,z j p c ≠ 0 → S.g c ∈ Kstrat S es N j)
    (hzm : ∀j p c,(z j p c).natAbs ≤ mStrat S es N j) :
    ∃ hs : ∀j,(stratBank S es j).Supplies (z j),
      let selected := selectedPositions S es J z hs
      let Y := (range (J+1)).biUnion (fun j => Bank.payload (hs j))
      usedEdges es=selectedCover es selected∪Y ∧ Disjoint (selectedCover es selected) Y ∧
      IsDecomposition H F (selectedCover es selected) (selectedFamily es selected) ∧
      selectedFamily es selected ⊆ modes es ∧
      (count (selectedFamily es selected):ℝ) ≤ es.length*pay ∧
      (count (R0∪selectedFamily es selected):ℝ) ≤ count R0+es.length*pay ∧
      charge S.w Y=∑j ∈ range (J+1),∑p,∑c,z j p c • S.g c ∧
      Y.card ≤ S.E*∑j ∈ range (J+1),∑p,∑c,(z j p c).natAbs := by
  let hs : ∀j,(stratBank S es j).Supplies (z j) :=
    fun j => stratBank_supplies hInv.trace j (z j) (hact j) (hzm j)
  let selected := selectedPositions S es J z hs
  have hPart := selected_partition hInv.history.local_history selected
  have hBudget := selectedCover_two_budgets hInv.history selected
  have hPayload := selectedPayload_eq_strata J z hs
  rw [hPayload] at hPart
  exact ⟨hs,hPart.1,hPart.2,hBudget.1,hBudget.2.1,hBudget.2.2.1,hBudget.2.2.2,
    activated_payload_charge hInv J z hs,activated_payload_card hInv J z hs⟩

end TypedTriangle.Pasch.RichBank.Actual
end

section
open Finset Classical
set_option autoImplicit false
namespace TypedTriangle.Pasch.AmbientBank
open S07V40 S07V42 S07V43 ProtectedBank
variable {X V I : Type*} [Fintype X] [Fintype V]

/-- This is the native setting already used by the constructed ambient run. -/
theorem native_lifted_g_mem_K (J : Host X I) (F : Set (Multiset I)) (W : Finset X)
    {d c E : ℕ} (C0 : CoreCompression J.G J.lab F W d c E)
    (ι : X ↪ V) (R P q Ecell zmax : ℕ) (F0 : Finset (Sym2 V)) (a : Cat d R) (Z : Finset V) :
    let S := liftSetting ι (protect (childSetting C0 R P q Ecell zmax) (pullEdges ι F0))
    S.g a ∈ S.K Z ↔ gCat C0 R a ∈ KZ J.G J.lab F W (pullVertices ι Z) :=
  childSetting_g_mem_K_iff C0 R P q Ecell zmax a (pullVertices ι Z)

theorem native_lifted_K_bot_iff (J : Host X I) (F : Set (Multiset I)) (W : Finset X)
    {d c E : ℕ} (C0 : CoreCompression J.G J.lab F W d c E)
    (ι : X ↪ V) (R P q Ecell zmax : ℕ) (F0 : Finset (Sym2 V)) (Z : Finset V) :
    let S := liftSetting ι (protect (childSetting C0 R P q Ecell zmax) (pullEdges ι F0))
    S.K Z=⊥ ↔ (KZ J.G J.lab F W (pullVertices ι Z)).toAddSubgroup=⊥ :=
  (S07V47.childSetting_shape C0 R P q Ecell zmax).K_eq_bot_iff (pullVertices ι Z)

variable {Q C : Type*} [AddCommGroup Q] [Fintype C]

theorem pulled_strata_mono (ι : X ↪ V) (S : MacroSetting V Q C)
    (es : List (RichBank.Entry V C S.P)) (N : ℕ) :
    Monotone (fun j => pullVertices ι (RichBank.Actual.Zstrat S es N j)) := by
  intro i j hij x hx
  exact mem_preimage.mpr (RichBank.Actual.Zstrat_mono hij (mem_preimage.mp hx))

theorem pulled_strata_prefix_bound {H : Host V I} {F : Set (Multiset I)} {S : MacroSetting V Q C}
    {Ub : ℕ} {pay : ℝ} {R0 : Finset (Finset V)} {N : ℕ} {es : List (RichBank.Entry V C S.P)}
    (h : RichBank.Seeded.RunInv H F S Ub pay R0 N es) (ι : X ↪ V) (j : ℕ) :
    S.q*(pullVertices ι (RichBank.Actual.Zstrat S es N j)).card ≤ 
      2*S.E*S.Bstar*∑i ∈ range j,RichBank.Actual.mStrat S es N i :=
  (Nat.mul_le_mul_left S.q (pull_vertices_card_le ι _)).trans (RichBank.Actual.card_Zstrat_le h j)

/-- A payload known to lie in the embedded host is recovered literally by pullback. -/
theorem lift_pull_edges_of_subset (ι : X ↪ V) (E : Finset (Sym2 V)) (D : Finset (Sym2 X))
    (hE : E ⊆ liftEdges ι D) : liftEdges ι (pullEdges ι E)=E := by
  ext f
  constructor
  · intro hf
    obtain ⟨g,hg,rfl⟩ := mem_map.mp hf
    exact mem_preimage.mp hg
  · intro hf
    obtain ⟨g,hg,rfl⟩ := mem_map.mp (hE hf)
    exact mem_map.mpr ⟨g,mem_preimage.mpr hf,rfl⟩

theorem charge_pull_edges_of_subset (ι : X ↪ V) (w : Sym2 X → Q)
    (E : Finset (Sym2 V)) (D : Finset (Sym2 X)) (hE : E ⊆ liftEdges ι D) :
    charge w (pullEdges ι E)=charge (zeroCharge ι w) E := by
  calc charge w (pullEdges ι E)=charge (zeroCharge ι w) (liftEdges ι (pullEdges ι E)) :=
        (charge_lift ι w (pullEdges ι E)).symm
    _ = charge (zeroCharge ι w) E := by rw [lift_pull_edges_of_subset ι E D hE]


theorem history_used_lift (ι : X ↪ V) (Sloc : MacroSetting X Q C)
    {H : Host V I} {F : Set (Multiset I)} {Ub : ℕ} {pay : ℝ}
    {es : List (RichBank.Entry V C Sloc.P)}
    (h : RichBank.ValidHistory H F (liftSetting ι Sloc) Ub pay es) :
    ∃ D : Finset (Sym2 X),RichBank.usedEdges es=liftEdges ι D := by
  have hEach : ∀ e ∈ es,∃D : Finset (Sym2 X),e.cell.tot=liftEdges ι D := by
    intro e he
    obtain ⟨D,hD,_⟩ := (h.good e he).good.2.2.1
    exact ⟨D,hD⟩
  clear h
  induction es with
  | nil => exact ⟨∅,by simp [RichBank.usedEdges,liftEdges]⟩
  | cons e es ih =>
    obtain ⟨D,hD⟩ := hEach e (by simp)
    obtain ⟨E,hE⟩ := ih (fun f hf => hEach f (List.mem_cons_of_mem _ hf))
    refine ⟨D∪E,?_⟩
    change e.cell.tot∪RichBank.usedEdges es=liftEdges ι (D∪E)
    rw [hD,hE]
    exact (map_union D E).symm

/-- Pull the literal ambient decomposition; no packing is reselected. -/
theorem decomposition_pull_of_supported (J : Host X I) (H : Host V I)
    (F : Set (Multiset I)) (ι : X ↪ V) (hLab : ∀ x, J.lab x=H.lab (ι x))
    {Bc : Finset (Sym2 V)} {Dc : Finset (Finset V)}
    (hD : IsDecomposition H F Bc Dc) (hE : Bc ⊆ liftEdges ι (edges J)) :
    ∃ Dl : Finset (Finset X), IsDecomposition J F (pullEdges ι Bc) Dl ∧
      mapConfiguration ι Dl=Dc ∧ count Dl=count Dc := by
  let pullT : Finset V → Finset X := fun T => T.preimage ι ι.injective.injOn
  have hMap : ∀ T ∈ Dc,(pullT T).map ι=T := by
    intro T hT
    ext v
    constructor
    · intro hv
      obtain ⟨x,hx,rfl⟩ := mem_map.mp hv
      exact mem_preimage.mp hx
    · intro hv
      obtain ⟨w,hw,hwv⟩ := exists_mem_ne (by rw [(hD.1 T hT).1]; norm_num : 1 < T.card) v
      have he := hE (hD.subset hT (mem_triEdges.mpr ⟨hv,hw,hwv.symm⟩))
      obtain ⟨f,hf,hfe⟩ := mem_map.mp he
      have hvf : v ∈ edgeEmbedding ι f := by rw [hfe]; simp
      obtain ⟨x,_,hx⟩ := Sym2.mem_map.mp hvf
      exact mem_map.mpr ⟨x,mem_preimage.mpr (hx.symm ▸ hv),hx⟩
  have hAllowed : ∀ T ∈ Dc,IsAllowed J F (pullT T) := by
    intro T hT
    refine ⟨?_,?_,?_⟩
    · rw [←card_map ι, hMap T hT]
      exact (hD.1 T hT).1
    · intro x hx y hy hxy
      have he : edgeEmbedding ι s(x,y) ∈ Bc :=
        hD.subset hT (mem_triEdges.mpr ⟨mem_preimage.mp hx,mem_preimage.mp hy,
          fun hh => hxy (ι.injective hh)⟩)
      obtain ⟨f,hf,hfe⟩ := mem_map.mp (hE he)
      have hfx : f=s(x,y) := (edgeEmbedding ι).injective hfe
      exact SparseEdge.mem_edges.mp (hfx ▸ hf)
    · have hh := (hD.1 T hT).2.2
      rw [←hMap T hT,Finset.map_val,Multiset.map_map] at hh
      have hl : H.lab ∘ ι=J.lab := funext (fun x => (hLab x).symm)
      change (pullT T).val.map (H.lab ∘ ι) ∈ F at hh
      rwa [hl] at hh
  let Dl := Dc.image pullT
  have hSame : mapConfiguration ι Dl=Dc := by
    ext T
    constructor
    · intro hT
      obtain ⟨A,hA,rfl⟩ := mem_mapConfiguration.mp hT
      obtain ⟨B,hB,rfl⟩ := mem_image.mp hA
      simpa only [hMap B hB] using hB
    · intro hT
      exact mem_mapConfiguration.mpr ⟨pullT T,mem_image.mpr ⟨T,hT,rfl⟩,hMap T hT⟩
  have hLocal : IsDecomposition J F (pullEdges ι Bc) Dl := by
    refine ⟨?_,?_,?_⟩
    · intro T hT
      obtain ⟨A,hA,rfl⟩ := mem_image.mp hT
      exact hAllowed A hA
    · intro T hT U hU hTU
      obtain ⟨A,hA,rfl⟩ := mem_image.mp hT
      obtain ⟨B,hB,rfl⟩ := mem_image.mp hU
      change Disjoint (triEdges (pullT A)) (triEdges (pullT B))
      rw [disjoint_left]
      intro f hfA hfB
      have hfa : edgeEmbedding ι f ∈ triEdges A := by
        rw [←hMap A hA,triEdges_lift]
        exact mem_map.mpr ⟨f,hfA,rfl⟩
      have hfb : edgeEmbedding ι f ∈ triEdges B := by
        rw [←hMap B hB,triEdges_lift]
        exact mem_map.mpr ⟨f,hfB,rfl⟩
      exact disjoint_left.mp (hD.2.1 hA hB (fun hh => hTU (congrArg pullT hh))) hfa hfb
    · ext f
      constructor
      · intro hf
        obtain ⟨T,hT,hf⟩ := mem_biUnion.mp hf
        obtain ⟨A,hA,rfl⟩ := mem_image.mp hT
        apply mem_preimage.mpr
        apply hD.subset hA
        rw [←hMap A hA,triEdges_lift]
        exact mem_map.mpr ⟨f,hf,rfl⟩
      · intro hf
        obtain ⟨T,hT,he⟩ := hD.exists_mem (mem_preimage.mp hf)
        rw [←hMap T hT,triEdges_lift] at he
        obtain ⟨g,hg,hgf⟩ := mem_map.mp he
        have hgfe : g=f := (edgeEmbedding ι).injective hgf
        exact mem_biUnion.mpr ⟨pullT T,mem_image.mpr ⟨T,hT,rfl⟩,hgfe ▸ hg⟩
  exact ⟨Dl,hLocal,hSame,by rw [←count_mapConfiguration ι Dl,hSame]⟩

theorem protected_history_disjoint (ι : X ↪ V) (Sloc : MacroSetting X Q C)
    (F0 : Finset (Sym2 V))
    {H : Host V I} {F : Set (Multiset I)} {Ub : ℕ} {pay : ℝ}
    {es : List (RichBank.Entry V C Sloc.P)}
    (h : RichBank.ValidHistory H F (liftSetting ι (protect Sloc (pullEdges ι F0))) Ub pay es) :
    Disjoint (RichBank.usedEdges es) F0 := by
  rw [disjoint_left]
  intro f hf hF
  rw [←RichBank.Actual.toBank_total es] at hf
  obtain ⟨i,_,hi⟩ := mem_biUnion.mp hf
  have hb := (h.good (es.get i) (List.get_mem ..)).good.2.2.1
  obtain ⟨D,hD,hBas,hDis⟩ := hb
  rw [RichBank.Actual.toBank_tot,hD] at hi
  obtain ⟨g,hg,hgf⟩ := mem_map.mp hi
  exact disjoint_left.mp hDis hg (mem_preimage.mpr (hgf.symm ▸ hF))

end TypedTriangle.Pasch.AmbientBank
end

section
open Finset Classical
set_option autoImplicit false
set_option maxHeartbeats 600000
namespace TypedTriangle.Pasch.ActualAllocation
open TypedTriangle.SparseEdge TypedTriangle.Dispersal S07V40 S07V42 S07V44 S07V46
open RichBank.Actual AmbientBank
variable {X V I : Type*} [Fintype X] [Fintype V]

/-- The full/early-stop allocation dichotomy for THIS actual bank. The two
shape equalities are discharged by native_lifted_g_mem_K/K_bot_iff. No
canonical run, numerical choice or word provider is assumed. -/
theorem actual_allocation_dichotomy
    (Jhost : Host X I) (Hambient : Host V I) (F : Set (Multiset I)) (W : Finset X)
    {d c E R A M K L N Ub : ℕ} {pay : ℝ}
    (C0 : CoreCompression Jhost.G Jhost.lab F W d c E) (ι : X ↪ V)
    (S : MacroSetting V (ClassQ Jhost.G Jhost.lab F W×ℤ) (Cat d R))
    (R0 : Finset (Finset V)) (es : List (RichBank.Entry V (Cat d R) S.P))
    (hInv : RichBank.Seeded.RunInv Hambient F S Ub pay R0 N es)
    (hq : 0 < S.q) (hChain : ChainBound S L) (hRunCap : 2*S.E*S.Bstar*N ≤ S.q*S.zmax)
    (hMember : ∀ a Z,S.g a ∈ S.K Z ↔ gCat C0 R a ∈ KZ Jhost.G Jhost.lab F W (pullVertices ι Z))
    (hBot : ∀ Z,S.K Z=⊥ ↔ (KZ Jhost.G Jhost.lab F W (pullVertices ι Z)).toAddSubgroup=⊥)
    (Mon : ∀ Z : Finset X,CatalogGen C0 R Z → PhysicalMonitors C0 R Z A M K)
    (Fm : FullMonitor C0 R A M K)
    (hgen : ∀ j,CatalogGen C0 R (pullVertices ι (RichBank.Actual.Zstrat S es N j)))
    {eta gamma tau : ℝ} (n : ℕ) (hγ : 0 < gamma) (hη : 0 ≤ eta)
    (hqn : gamma*n ≤ S.q) (hθ : eta*((2*S.E*S.Bstar:ℕ):ℝ)/gamma ≤ 1)
    (hP : 2*gammaL A M L ≤ S.P)
    (x : MCore Jhost.G Jhost.lab F W)
    (hx : clsQ Jhost.G Jhost.lab F W (x:Sym2 X→ℤ) ∈ KZ Jhost.G Jhost.lab F W ∅)
    (hloc : ∀ ℓ ≤ L,(ℓ < L ∨ S.K (saturatedPrefix S es N)=⊥) →
      (S07V32.l1 (physMon C0 (Dset C0 R (pullVertices ι (RichBank.Actual.Zstrat S es N (ℓ+1))))
        (Mon _ (hgen (ℓ+1))).psi x):ℝ) ≤ eta*n*(pullVertices ι (RichBank.Actual.Zstrat S es N (ℓ+1))).card)
    (hfull : S.K (saturatedPrefix S es N) ≠ ⊥ → (S07V32.l1 (physMon C0 ∅ Fm.psi x):ℝ) ≤ tau*n^2)
    (hN : S.K (saturatedPrefix S es N) ≠ ⊥ → 1+tau*n^2 ≤ 2*N) :
    ∃ J ≤ L,∃ z : ℕ → Fin S.P → Cat d R → ℤ,
      (∀ i p a,z i p a ≠ 0 → i ≤ J ∧ gCat C0 R a ∈ KZ Jhost.G Jhost.lab F W
        (pullVertices ι (RichBank.Actual.Zstrat S es N i))) ∧
      (∀ i p a,(z i p a).natAbs ≤ mStrat S es N i) ∧
      clsQ Jhost.G Jhost.lab F W (x:Sym2 X→ℤ)+∑i ∈ range (J+1),∑p,wcls (gCat C0 R) (z i p)=0 ∧
      (S.K (saturatedPrefix S es N) ≠ ⊥ → J=L) := by
  let Z : ℕ → Finset X := fun j => pullVertices ι (RichBank.Actual.Zstrat S es N j)
  let m : ℕ → ℕ := mStrat S es N
  have hZm : Monotone Z := pulled_strata_mono ι S es N
  have hZ0 : Z 0=∅ := by
    dsimp only [Z]
    rw [RichBank.Actual.Zstrat_zero hq]
    simp [pullVertices]
  have hx0 : clsQ Jhost.G Jhost.lab F W (x:Sym2 X→ℤ) ∈ KZ Jhost.G Jhost.lab F W (Z 0) := by
    rw [hZ0]; exact hx
  have hpre : ∀ ℓ ≤ L,S.q*(Z (ℓ+1)).card ≤ (2*S.E*S.Bstar)*∑i ∈ range (ℓ+1),m i :=
    fun ℓ _ => pulled_strata_prefix_bound hInv ι (ℓ+1)
  by_cases hStop : S.K (saturatedPrefix S es N)=⊥
  · have hLast : (KZ Jhost.G Jhost.lab F W (Z (numStrata S es N))).toAddSubgroup=⊥ :=
      (hBot _).mp (K_Zstrat_numStrata_bot hInv hq hChain hRunCap hStop)
    rcases Nat.eq_zero_or_pos (numStrata S es N) with hZero | hPos
    · have hxZero : clsQ Jhost.G Jhost.lab F W (x:Sym2 X→ℤ)=0 := by
        rw [hZero,hZ0] at hLast
        have hh : clsQ Jhost.G Jhost.lab F W (x:Sym2 X→ℤ) ∈ 
            (KZ Jhost.G Jhost.lab F W ∅).toAddSubgroup := hx
        rw [hLast] at hh
        exact AddSubgroup.mem_bot.mp hh
      refine ⟨0,Nat.zero_le _,fun _ _ _ => 0,?_,?_,?_,?_⟩
      · intro i p a ha; exact (ha rfl).elim
      · intro i p a; simp
      · simp [hxZero,wcls]
      · intro ha; exact (ha hStop).elim
    · let J := numStrata S es N-1
      have hJ : numStrata S es N=J+1 := by dsimp [J]; omega
      have hJL : J ≤ L := by have hh := numStrata_le hInv hq hChain hRunCap; omega
      have hm0Nat : 0 < RichBank.Actual.mStrat S es N 0 :=
        (RichBank.Actual.mStrat_pos_iff_lt_numStrata (S:=S) (es:=es) (N:=N) (j:=0)).mpr hPos
      have hm0 : 1 ≤ m 0 := hm0Nat
      rw [hJ] at hLast
      obtain ⟨z,hzs,hzm,hzx⟩ := physical_allocation_local C0 hJL Z hZm m
        (fun ℓ _ => Mon _ (hgen (ℓ+1))) (fun j _ => hgen j) hLast
        n S.q (2*S.E*S.Bstar) hγ hη hqn hθ (fun ℓ hℓ => hpre ℓ (hℓ.trans hJL)) hP hm0 x hx0
        (fun ℓ hℓ => hloc ℓ (hℓ.trans hJL) (Or.inr hStop))
      exact ⟨J,hJL,z,hzs,hzm,hzx,fun ha => (ha hStop).elim⟩
  · have hSum : ∑i ∈ range (L+1),m i=N := by
      rw [sum_mStrat hInv hq hChain hRunCap]
      exact (RichBank.Actual.stop_dichotomy hInv.trace).resolve_left hStop
    have hSJ : 1+tau*n^2 ≤ 2*∑i ∈ range (L+1),(m i:ℝ) := by
      have hh : (∑i ∈ range (L+1),(m i:ℝ))=N := by exact_mod_cast hSum
      rw [hh]; exact hN hStop
    have hm0 : 1 ≤ m 0 := by
      apply one_le_m0 (S:=S) (es:=es) (N:=N) (J:=L)
      by_contra hc
      change ¬ 1 ≤ ∑i ∈ range (L+1),m i at hc
      have hz : ∑i ∈ range (L+1),m i=0 := Nat.eq_zero_of_not_pos hc
      have hzR : (∑i ∈ range (L+1),(m i:ℝ))=0 := by exact_mod_cast hz
      have hf := hfull hStop
      have hNonneg : (0:ℝ) ≤ (S07V32.l1 (physMon C0 ∅ Fm.psi x):ℝ) := by
        exact_mod_cast (sum_nonneg (fun _ _ => abs_nonneg _): (0:ℤ) ≤ S07V32.l1 (physMon C0 ∅ Fm.psi x))
      rw [hzR] at hSJ
      linarith only [hSJ,hf,hNonneg]
    obtain ⟨z,hzs,hzm,hzx⟩ := physical_allocation_full C0 (L:=L) le_rfl Z hZm m
      (fun ℓ _ => Mon _ (hgen (ℓ+1))) Fm (fun j _ => hgen j)
      n S.q (2*S.E*S.Bstar) hγ hη hqn hθ hpre hP hm0 hSJ x hx0
      (fun ℓ hℓ => hloc ℓ hℓ.le (Or.inl hℓ)) (hfull hStop)
    exact ⟨L,le_rfl,z,hzs,hzm,hzx,fun _ => rfl⟩

end TypedTriangle.Pasch.ActualAllocation
end

section
open Finset Classical
set_option autoImplicit false
set_option maxHeartbeats 600000
namespace TypedTriangle.Pasch.ActualAllocation
open S07V40 S07V42 S07V44 S07V46 CatalogNative.Explicit AmbientBank LocalizedCover

/-- Actual bank test weights are chosen before the packing, on the local
pullbacks of its real saturated-prefix sets. Only geometry on X is used. -/
theorem choose_weights_on_rich_bank_core (α β qCore : ℝ) (h d c E R A M K : ℕ)
    (hα : 0 < α) (hβ : 0 < β) (hqCore : 0 < qCore) (hβα : β ≤ α)
    {X V I Q C : Type} [Fintype X] [Fintype V] [AddCommGroup Q] [Fintype C]
    (ι : X ↪ V) (Jhost : Host X I) (Hambient : Host V I) (F : Set (Multiset I)) (W : Finset X)
    (C0 : CoreCompression Jhost.G Jhost.lab F W d c E) (S : MacroSetting V Q C)
    {N Ub : ℕ} {pay : ℝ} {R0 : Finset (Finset V)} {es : List (RichBank.Entry V C S.P)}
    (hInv : RichBank.Seeded.RunInv Hambient F S Ub pay R0 N es) (hq : 0 < S.q)
    (hcap : 2*S.E*S.Bstar*N ≤ S.q*S.zmax)
    (MonS : ∀ ℓ,PhysicalMonitors C0 R (pullVertices ι (RichBank.Actual.Zstrat S es N (ℓ+1))) A M K)
    (Fm : FullMonitor C0 R A M K)
    (hn : nativeWeightOrder α β qCore h ≤ Fintype.card X)
    (hWlo : qCore*Fintype.card X/2 ≤ W.card)
    (h3 : CommonNbrCond Jhost F α) (h4 : HingeCond Jhost F α h)
    (hCore3 : SparseEdge.CommonNbrCond (Jhost.G.comap (Subtype.val : {x // x ∈ W}→X))
      (Jhost.lab ∘ Subtype.val) F β)
    (hCore4 : SparseEdge.HingeCond (Jhost.G.comap (Subtype.val : {x // x ∈ W}→X))
      (Jhost.lab ∘ Subtype.val) F β h)
    (hzCore : (S.zmax:ℝ) ≤ coreDelta β h*W.card)
    (hz3 : (S.zmax:ℝ) ≤ β/2*W.card)
    (hz4 : (S.zmax:ℝ)*2^Nat.choose (h+1) 2 ≤ β/2*W.card)
    (hzDel : (S.zmax:ℝ) ≤ S07V37.delOf (β/2) h*W.card) :
    ∃ loc : ℕ → Fin K → Sym2 X → ℝ,∃ full : Fin K → Sym2 X → ℝ,
      (∀ ℓ j (x : MCore Jhost.G Jhost.lab F W),∑e,loc ℓ j e*((x.1 e:ℤ):ℝ)=
        physMonReal C0 (Dset C0 R (pullVertices ι (RichBank.Actual.Zstrat S es N (ℓ+1)))) (MonS ℓ).psi j x) ∧
      (∀ j (x : MCore Jhost.G Jhost.lab F W),∑e,full j e*((x.1 e:ℤ):ℝ)=physMonReal C0 ∅ Fm.psi j x) ∧
      (∀ ℓ j T,IsAllowed Jhost F T → |triSum (loc ℓ j) T| ≤ 
        3*physicalWeightMagnitude (α/2) (β/2) h d c M*(T∩pullVertices ι (RichBank.Actual.Zstrat S es N (ℓ+1))).card) ∧
      (∀ j T,IsAllowed Jhost F T → |triSum (full j) T| ≤ 
        3*physicalWeightMagnitude (α/2) (β/2) h d c M*T.card) := by
  have hSmall : ∀ ℓ,(pullVertices ι (RichBank.Actual.Zstrat S es N (ℓ+1))).card ≤ S.zmax := by
    intro ℓ
    apply (pull_vertices_card_le ι _).trans
    exact RichBank.Actual.saturatedPrefix_small hInv hq hcap _
      ((RichBank.Actual.preStrat_le (S:=S) (es:=es) N (ℓ+1)).trans
        (RichBank.Actual.numRounds_le N))
  obtain ⟨outer,hW⟩ : ∃ outer : Finset X,W=univ\outer := ⟨univ\W,by simp⟩
  cases hW
  exact choose_uniform_native_stratum_weights_explicit α β qCore h d c E R A M K
    hα hβ hqCore hβα Jhost F (univ\outer) outer rfl C0
    (fun ℓ => pullVertices ι (RichBank.Actual.Zstrat S es N (ℓ+1))) MonS Fm S.zmax
    hn hWlo h3 h4 hCore3 hCore4 hSmall hzCore hz3 hz4 hzDel

end TypedTriangle.Pasch.ActualAllocation
end

section
open Finset Classical
set_option autoImplicit false
set_option maxHeartbeats 600000
namespace TypedTriangle.Pasch.ActualAllocation
open TypedTriangle.SparseEdge TypedTriangle.Dispersal S07V40 S07V42 S07V44 S07V46
open RichBank.Actual AmbientBank CatalogNative LocalizedCover

/-- Consume the moments of the packing already chosen. This does not invoke
another packing constructor or discard any extra statistics of that witness. -/
theorem activate_actual_bank_of_physical_moments
    {X V I : Type*} [Fintype X] [Fintype V]
    (Jhost : Host X I) (Hambient : Host V I) (F : Set (Multiset I)) (W : Finset X)
    {d c E R A M K L N Ub : ℕ} {pay : ℝ}
    (C0 : CoreCompression Jhost.G Jhost.lab F W d c E) (ι : X ↪ V)
    (S : MacroSetting V (ClassQ Jhost.G Jhost.lab F W×ℤ) (Cat d R))
    (R0 : Finset (Finset V)) (es : List (RichBank.Entry V (Cat d R) S.P))
    (hInv : RichBank.Seeded.RunInv Hambient F S Ub pay R0 N es)
    (hq : 0 < S.q) (hChain : ChainBound S L) (hRunCap : 2*S.E*S.Bstar*N ≤ S.q*S.zmax)
    (hMember : ∀ a Z,S.g a ∈ S.K Z ↔ gCat C0 R a ∈ KZ Jhost.G Jhost.lab F W (pullVertices ι Z))
    (hBot : ∀ Z,S.K Z=⊥ ↔ (KZ Jhost.G Jhost.lab F W (pullVertices ι Z)).toAddSubgroup=⊥)
    (Mon : ∀ Z : Finset X,CatalogGen C0 R Z → PhysicalMonitors C0 R Z A M K)
    (Fm : FullMonitor C0 R A M K)
    (hgen : ∀ j,CatalogGen C0 R (pullVertices ι (RichBank.Actual.Zstrat S es N j)))
    {eta gamma : ℝ} (n : ℕ) (hγ : 0 < gamma) (hη : 0 ≤ eta)
    (hqn : gamma*n ≤ S.q) (hθ : eta*((2*S.E*S.Bstar:ℕ):ℝ)/gamma ≤ 1)
    (hP : 2*gammaL A M L ≤ S.P)
    (Y : Finset (Sym2 X)) (x : MCore Jhost.G Jhost.lab F W)
    (hxY : (x:Sym2 X→ℤ)=SparseEdge.ind Y)
    (hx : clsQ Jhost.G Jhost.lab F W (x:Sym2 X→ℤ) ∈ KZ Jhost.G Jhost.lab F W ∅)
    (loc : ℕ → Fin K → Sym2 X → ℝ) (full : Fin K → Sym2 X → ℝ)
    (hLocRep : ∀ ℓ j,∑e,loc ℓ j e*((x.1 e:ℤ):ℝ)=
      physMonReal C0 (Dset C0 R (pullVertices ι (RichBank.Actual.Zstrat S es N (ℓ+1))))
        (Mon _ (hgen (ℓ+1))).psi j x)
    (hFullRep : ∀ j,∑e,full j e*((x.1 e:ℤ):ℝ)=physMonReal C0 ∅ Fm.psi j x)
    (B : ℝ) (hKB : (K:ℝ)*B ≤ eta)
    (hLocMom : ∀ ℓ ≤ L,∀ j,|edgeSum (loc ℓ j) Y| ≤ 
      B*n*(pullVertices ι (RichBank.Actual.Zstrat S es N (ℓ+1))).card)
    (hFullMom : ∀ j,|edgeSum (full j) Y| ≤ B*n^2)
    (hN : S.K (saturatedPrefix S es N) ≠ ⊥ → 1+eta*n^2 ≤ 2*N) :
    ∃ J ≤ L,∃ z : ℕ → Fin S.P → Cat d R → ℤ,
      (∀ i p a,z i p a ≠ 0 → i ≤ J ∧ gCat C0 R a ∈ KZ Jhost.G Jhost.lab F W
        (pullVertices ι (RichBank.Actual.Zstrat S es N i))) ∧
      (∀ i p a,(z i p a).natAbs ≤ mStrat S es N i) ∧
      clsQ Jhost.G Jhost.lab F W (x:Sym2 X→ℤ)+∑i ∈ range (J+1),∑p,wcls (gCat C0 R) (z i p)=0 ∧
      (S.K (saturatedPrefix S es N) ≠ ⊥ → J=L) := by
  have hloc : ∀ ℓ ≤ L,(ℓ < L ∨ S.K (saturatedPrefix S es N)=⊥) →
      (S07V32.l1 (physMon C0 (Dset C0 R (pullVertices ι (RichBank.Actual.Zstrat S es N (ℓ+1))))
        (Mon _ (hgen (ℓ+1))).psi x):ℝ) ≤ eta*n*(pullVertices ι (RichBank.Actual.Zstrat S es N (ℓ+1))).card := by
    intro ℓ hℓ _
    have hh := physical_monitor_norm_of_edge_moments (Mon _ (hgen (ℓ+1))) x Y hxY
      (loc ℓ) (hLocRep ℓ) (B*n*(pullVertices ι (RichBank.Actual.Zstrat S es N (ℓ+1))).card) (hLocMom ℓ hℓ)
    have hscaled := mul_le_mul_of_nonneg_right hKB
      (by positivity : (0:ℝ) ≤ n*(pullVertices ι (RichBank.Actual.Zstrat S es N (ℓ+1))).card)
    have hs : (K:ℝ)*(B*n*(pullVertices ι (RichBank.Actual.Zstrat S es N (ℓ+1))).card) ≤ 
        eta*(n*(pullVertices ι (RichBank.Actual.Zstrat S es N (ℓ+1))).card) := by
      convert hscaled using 1 <;> ring
    convert hh.trans hs using 1 <;> ring
  have hfull : S.K (saturatedPrefix S es N) ≠ ⊥ → (S07V32.l1 (physMon C0 ∅ Fm.psi x):ℝ) ≤ eta*n^2 := by
    intro _
    have hh := full_monitor_norm_of_edge_moments C0 Fm x Y hxY full hFullRep (B*n^2) hFullMom
    have hs : (K:ℝ)*(B*n^2) ≤ eta*n^2 := by
      convert mul_le_mul_of_nonneg_right hKB (by positivity : (0:ℝ) ≤ (n:ℝ)^2) using 1 <;> ring
    exact hh.trans hs
  exact actual_allocation_dichotomy Jhost Hambient F W C0 ι S R0 es hInv hq hChain hRunCap
    hMember hBot Mon Fm hgen n hγ hη hqn hθ hP x hx hloc hfull hN

end TypedTriangle.Pasch.ActualAllocation
end

section
open Finset Classical
set_option autoImplicit false
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace TypedTriangle.Pasch.ActualAllocation
open SparseEdge Dispersal S07V40 S07V42 S07V43 S07V46 ProtectedBank AmbientBank
open RichBank.Actual

/-- The reference avoids the actual used-edge set. The complement is the
literal stored off/on decomposition paid during construction, on the full
ambient host; its child payload is pulled back without changing any mode. -/
theorem actual_activated_mode_avoiding_reference
    {X V I : Type} [Fintype X] [Fintype V]
    (Jhost : Host X I) (Hambient : Host V I) (F : Set (Multiset I)) (W : Finset X)
    {d c E Rc P q Ecell zmax N Ub J : ℕ} {pay : ℝ}
    (C0 : CoreCompression Jhost.G Jhost.lab F W d c E) (ι : X ↪ V)
    (hLab : ∀ x,Jhost.lab x=Hambient.lab (ι x))
    (F0 : Finset (Sym2 V)) (R0 : Finset (Finset V))
    (es : List (RichBank.Entry V (Cat d Rc) P))
    (hInv : RichBank.Seeded.RunInv Hambient F
      (liftSetting ι (protect (childSetting C0 Rc P q Ecell zmax) (pullEdges ι F0))) Ub pay R0 N es)
    (Y U Eref : Finset (Sym2 X)) (x : MCore Jhost.G Jhost.lab F W)
    (hYF : liftEdges ι Y ⊆ F0) (hYE : Y ⊆ edges Jhost)
    (hx : (x:Sym2 X→ℤ)=SparseEdge.ind Y)
    (z : ℕ → Fin P → Cat d Rc → ℤ)
    (hact : ∀j p a,z j p a ≠ 0 → gCat C0 Rc a ∈ KZ Jhost.G Jhost.lab F W
      (pullVertices ι (RichBank.Actual.Zstrat
        (liftSetting ι (protect (childSetting C0 Rc P q Ecell zmax) (pullEdges ι F0))) es N j)))
    (hzm : ∀j p a,(z j p a).natAbs ≤ mStrat
      (liftSetting ι (protect (childSetting C0 Rc P q Ecell zmax) (pullEdges ι F0))) es N j)
    (hCancel : clsQ Jhost.G Jhost.lab F W (x:Sym2 X→ℤ)+
      ∑j ∈ range (J+1),∑p,wcls (gCat C0 Rc) (z j p)=0)
    (hYU : Y ⊆ U) (hBU : pullEdges ι (RichBank.usedEdges es) ⊆ U) (hAvoid : Disjoint Eref U) :
    ∃ Ytot Yb : Finset (Sym2 X),∃ Bc : Finset (Sym2 V),∃ Dc : Finset (Finset V),∃ Dclocal : Finset (Finset X),
      Ytot=Y∪Yb ∧ Ytot ⊆ edges Jhost ∧ Ytot ⊆ U ∧ Disjoint Eref Ytot ∧
      RichBank.usedEdges es=Bc∪liftEdges ι Yb ∧
      IsDecomposition Hambient F Bc Dc ∧
      IsDecomposition Jhost F (pullEdges ι Bc) Dclocal ∧ mapConfiguration ι Dclocal=Dc ∧
      count Dclocal=count Dc ∧ Dc ⊆ RichBank.modes es ∧
      (count Dc:ℝ) ≤ es.length*pay ∧ (count (R0∪Dc):ℝ) ≤ count R0+es.length*pay ∧
      Disjoint Bc F0 ∧ Disjoint Bc (liftEdges ι Yb) ∧ Disjoint Y Yb ∧
      SparseEdge.ind Ytot ∈ LamCore Jhost.G Jhost.lab F W ∧ Yb ⊆ childEdges Jhost.G W := by
  let Sloc := protect (childSetting C0 Rc P q Ecell zmax) (pullEdges ι F0)
  let S := liftSetting ι Sloc
  have hActS : ∀j p a,z j p a ≠ 0 → S.g a ∈ RichBank.Actual.Kstrat S es N j := by
    intro j p a ha
    exact (native_lifted_g_mem_K Jhost F W C0 ι Rc P q Ecell zmax F0 a (RichBank.Actual.Zstrat S es N j)).mpr (hact j p a ha)
  let hs : ∀j,(stratBank S es j).Supplies (z j) :=
    fun j => stratBank_supplies hInv.trace j (z j) (hActS j) (hzm j)
  let selected := selectedPositions S es J z hs
  let Yamb := (range (J+1)).biUnion (fun j => Bank.payload (hs j))
  let Bc := selectedCover es selected
  let Dc := selectedFamily es selected
  let Yb := pullEdges ι Yamb
  have hPart := selected_partition hInv.history.local_history selected
  have hPayload : selectedPayload es selected=Yamb := by
    exact selectedPayload_eq_strata (S:=S) (es:=es) J z hs
  rw [hPayload] at hPart
  have hBud := selectedCover_two_budgets hInv.history selected
  have hYused : Yamb ⊆ RichBank.usedEdges es := by rw [hPart.1]; exact subset_union_right
  have hBcUsed : Bc ⊆ RichBank.usedEdges es := by rw [hPart.1]; exact subset_union_left
  obtain ⟨Dlocal,hUsed⟩ := history_used_lift ι Sloc hInv.history.local_history
  have hYembed : Yamb ⊆ liftEdges ι Dlocal := by rwa [←hUsed]
  have hLift : liftEdges ι Yb=Yamb := lift_pull_edges_of_subset ι Yamb Dlocal hYembed
  have hUsedHost : RichBank.usedEdges es ⊆ liftEdges ι (edges Jhost) := by
    intro f hf
    rw [←RichBank.Actual.toBank_total es] at hf
    obtain ⟨i,_,hi⟩ := mem_biUnion.mp hf
    obtain ⟨D,hD,hBas,_⟩ := (hInv.history.local_history.good (es.get i) (List.get_mem ..)).good.2.2.1
    rw [RichBank.Actual.toBank_tot,hD] at hi
    obtain ⟨g,hg,rfl⟩ := mem_map.mp hi
    exact mem_map.mpr ⟨g,CorePaid.basal_subset_edges hBas hg,rfl⟩
  obtain ⟨Dclocal,hDcLocal,hDcMap,hDcCount⟩ := decomposition_pull_of_supported
    Jhost Hambient F ι hLab hBud.1 (hBcUsed.trans hUsedHost)
  have hProtect : Disjoint (RichBank.usedEdges es) F0 :=
    protected_history_disjoint ι (childSetting C0 Rc P q Ecell zmax) F0 hInv.history.local_history
  have hYYb : Disjoint Y Yb := by
    rw [disjoint_left]
    intro f hfY hfYb
    have hmF : edgeEmbedding ι f ∈ F0 := hYF (mem_map.mpr ⟨f,hfY,rfl⟩)
    have hmB : edgeEmbedding ι f ∈ Yamb := mem_preimage.mp hfYb
    exact disjoint_left.mp hProtect (hYused hmB) hmF
  let totalClass : ClassQ Jhost.G Jhost.lab F W := ∑j ∈ range (J+1),∑p,∑a,z j p a • gCat C0 Rc a
  have hCharge := activated_payload_charge hInv J z hs
  change charge (zeroCharge ι (tagW Jhost.G Jhost.lab F W)) Yamb=
    ∑j ∈ range (J+1),∑p,∑a,z j p a • ((gCat C0 Rc a,0):ClassQ Jhost.G Jhost.lab F W×ℤ) at hCharge
  have hPair : (∑j ∈ range (J+1),∑p,∑a,z j p a • ((gCat C0 Rc a,0):ClassQ Jhost.G Jhost.lab F W×ℤ))=
      (totalClass,0) := by
    apply Prod.ext
    · simp [Prod.fst_sum,totalClass]
    · simp [Prod.snd_sum]
  have hTag : charge (tagW Jhost.G Jhost.lab F W) Yb=(totalClass,0) := by
    calc _ = charge (zeroCharge ι (tagW Jhost.G Jhost.lab F W)) Yamb :=
          charge_pull_edges_of_subset ι _ Yamb Dlocal hYembed
      _ = _ := hCharge.trans hPair
  have hTagData : chargeQ Jhost.G Jhost.lab F W Yb=totalClass ∧ Yb ⊆ childEdges Jhost.G W :=
    (charge_tagW_eq_sgnQ_iff Yb true totalClass).mp (by simpa [sgnQ] using hTag)
  have hLam : SparseEdge.ind (Y∪Yb) ∈ LamCore Jhost.G Jhost.lab F W := by
    rw [←S07V43.clsQ_eq_zero_iff,←chargeQ_eq,
      S07V43.chargeQ_union Jhost.G Jhost.lab F W hYYb,hTagData.1,chargeQ_eq,←hx]
    simpa only [totalClass,wcls] using hCancel
  have hYbU : Yb ⊆ U := by
    intro f hf
    exact hBU (mem_preimage.mpr (hYused (mem_preimage.mp hf)))
  have hYtotU : Y∪Yb ⊆ U := union_subset hYU hYbU
  have hYbE : Yb ⊆ edges Jhost := by
    intro f hf
    have ha := SparseEdge.mem_edges.mp (hTagData.2 hf)
    induction f using Sym2.ind with
    | _ a b => exact SparseEdge.mem_edges.mpr ((S07V42.indG_le Jhost.G W) ha)
  refine ⟨Y∪Yb,Yb,Bc,Dc,Dclocal,rfl,union_subset hYE hYbE,hYtotU,hAvoid.mono_right hYtotU,?_,
    hBud.1,hDcLocal,hDcMap,hDcCount,hBud.2.1,hBud.2.2.1,hBud.2.2.2,hProtect.mono_left hBcUsed,?_,hYYb,hLam,hTagData.2⟩
  · rw [hLift]; exact hPart.1
  · rw [hLift]; exact hPart.2

end TypedTriangle.Pasch.ActualAllocation
end

#print axioms TypedTriangle.Pasch.ActualAllocation.stepPay_full
#print axioms TypedTriangle.Pasch.ActualAllocation.stepPay_local
#print axioms TypedTriangle.Pasch.ActualAllocation.physical_allocation_full
#print axioms TypedTriangle.Pasch.ActualAllocation.physical_allocation_local
#print axioms TypedTriangle.Pasch.RichBank.Actual.selectedPayload_eq_strata
#print axioms TypedTriangle.Pasch.RichBank.Actual.activated_payload_charge
#print axioms TypedTriangle.Pasch.RichBank.Actual.activated_payload_card
#print axioms TypedTriangle.Pasch.RichBank.Actual.activate_actual_words
#print axioms TypedTriangle.Pasch.AmbientBank.native_lifted_g_mem_K
#print axioms TypedTriangle.Pasch.AmbientBank.native_lifted_K_bot_iff
#print axioms TypedTriangle.Pasch.AmbientBank.pulled_strata_mono
#print axioms TypedTriangle.Pasch.AmbientBank.pulled_strata_prefix_bound
#print axioms TypedTriangle.Pasch.AmbientBank.lift_pull_edges_of_subset
#print axioms TypedTriangle.Pasch.AmbientBank.charge_pull_edges_of_subset
#print axioms TypedTriangle.Pasch.AmbientBank.history_used_lift
#print axioms TypedTriangle.Pasch.AmbientBank.protected_history_disjoint
#print axioms TypedTriangle.Pasch.ActualAllocation.actual_allocation_dichotomy
#print axioms TypedTriangle.Pasch.ActualAllocation.choose_weights_on_rich_bank_core
#print axioms TypedTriangle.Pasch.ActualAllocation.activate_actual_bank_of_physical_moments
#print axioms TypedTriangle.Pasch.ActualAllocation.actual_activated_mode_avoiding_reference

#print axioms TypedTriangle.Pasch.AmbientBank.decomposition_pull_of_supported
