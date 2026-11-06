module
public import RequestProject.TypedTriangle.ClonedPacking
set_option maxHeartbeats 4000000 -- build option (original: -DmaxHeartbeats=1600000; raised)
set_option maxRecDepth 16384 -- build option (original: -DmaxRecDepth=8192; raised)
@[expose] public section
open Finset Classical
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 800000
namespace TypedTriangle.WeightedClone
variable {ι : Type*} [Fintype ι]

def copyProjection (m : ι → ℕ) (C : Finset (Copy m)) : Finset ι := C.image Sigma.fst

def NoRepeatedBase {m : ι → ℕ} (C : Finset (Copy m)) : Prop :=
  Set.InjOn Sigma.fst (C : Set (Copy m))

def copyFiber (m : ι → ℕ) (S : Finset ι) : Finset (Finset (Copy m)) :=
  univ.powerset.filter (fun C => copyProjection m C = S ∧ NoRepeatedBase C)

/-- Choose exactly one tagged copy over each base index of S. -/
def selectCopies (m : ι → ℕ) (S : Finset ι) (f : ∀ i : S, Fin (m i.val)) : Finset (Copy m) :=
  univ.image (fun i : S => (⟨i.val,f i⟩ : Copy m))

theorem selectCopies_projection (m : ι → ℕ) (S : Finset ι) (f : ∀ i : S, Fin (m i.val)) :
    copyProjection m (selectCopies m S f) = S := by
  ext i
  constructor
  · intro hi
    obtain ⟨c,hc,hci⟩ := mem_image.mp hi
    obtain ⟨j,_,rfl⟩ := mem_image.mp hc
    exact hci ▸ j.property
  · intro hi
    exact mem_image.mpr ⟨⟨i,f ⟨i,hi⟩⟩,mem_image.mpr ⟨⟨i,hi⟩,mem_univ _,rfl⟩,rfl⟩

theorem selectCopies_noRepeatedBase (m : ι → ℕ) (S : Finset ι) (f : ∀ i : S, Fin (m i.val)) :
    NoRepeatedBase (selectCopies m S f) := by
  intro c hc d hd hcd
  obtain ⟨i,_,rfl⟩ := mem_image.mp hc
  obtain ⟨j,_,rfl⟩ := mem_image.mp hd
  have hij : i = j := Subtype.ext hcd
  subst j
  rfl

theorem selectCopies_injective (m : ι → ℕ) (S : Finset ι) :
    Function.Injective (selectCopies m S) := by
  intro f g hfg
  funext i
  have hc : (⟨i.val,f i⟩ : Copy m) ∈ selectCopies m S g := by
    rw [← hfg]
    exact mem_image.mpr ⟨i,mem_univ _,rfl⟩
  obtain ⟨j,_,hji⟩ := mem_image.mp hc
  have hsub : j = i := Subtype.ext (congrArg Sigma.fst hji)
  subst j
  apply Fin.ext
  exact (congrArg (fun c : Copy m => c.2.val) hji).symm

theorem selectCopies_surjective (m : ι → ℕ) (S : Finset ι) (C : Finset (Copy m))
    (hC : copyProjection m C = S) (hNo : NoRepeatedBase C) :
    ∃ f : ∀ i : S, Fin (m i.val), selectCopies m S f = C := by
  have hex (i : S) : ∃ j : Fin (m i.val), (⟨i.val,j⟩ : Copy m) ∈ C := by
    have hi : i.val ∈ copyProjection m C := hC.symm ▸ i.property
    obtain ⟨⟨k,j⟩,hc,hki⟩ := mem_image.mp hi
    dsimp only at hki
    subst k
    exact ⟨j,hc⟩
  choose f hf using hex
  refine ⟨f,?_⟩
  ext c
  constructor
  · intro hc
    obtain ⟨i,_,rfl⟩ := mem_image.mp hc
    exact hf i
  · intro hc
    have hi : c.1 ∈ S := hC ▸ mem_image.mpr ⟨c,hc,rfl⟩
    have heq : (⟨c.1,f ⟨c.1,hi⟩⟩ : Copy m) = c := hNo (hf ⟨c.1,hi⟩) hc rfl
    exact mem_image.mpr ⟨⟨c.1,hi⟩,mem_univ _,heq⟩

theorem mem_copyFiber {m : ι → ℕ} {S : Finset ι} {C : Finset (Copy m)} :
    C ∈ copyFiber m S ↔ copyProjection m C = S ∧ NoRepeatedBase C := by
  simp [copyFiber]

theorem card_copyFiber (m : ι → ℕ) (S : Finset ι) :
    (copyFiber m S).card = ∏ i ∈ S, m i := by
  have hc : (copyFiber m S).card = Fintype.card (∀ i : S, Fin (m i.val)) := by
    symm
    apply Finset.card_bij (fun f _ => selectCopies m S f)
    · intro f _
      exact mem_copyFiber.mpr ⟨selectCopies_projection m S f,selectCopies_noRepeatedBase m S f⟩
    · intro f _ g _ hfg
      exact selectCopies_injective m S hfg
    · intro C hC
      obtain ⟨f,hf⟩ := selectCopies_surjective m S C (mem_copyFiber.mp hC).1 (mem_copyFiber.mp hC).2
      exact ⟨f,mem_univ _,hf⟩
  rw [hc,Fintype.card_pi]
  simpa only [Fintype.card_fin] using (Finset.prod_coe_sort S m)

theorem projection_card_of_noRepeatedBase {m : ι → ℕ} {C : Finset (Copy m)}
    (hC : NoRepeatedBase C) : (copyProjection m C).card = C.card :=
  card_image_of_injOn hC

theorem copyFiber_fixed_card {m : ι → ℕ} {S : Finset ι} {ℓ : ℕ} (hS : S.card = ℓ) :
    ((univ.powersetCard ℓ).filter NoRepeatedBase).filter (fun C => copyProjection m C = S) = copyFiber m S := by
  ext C
  simp only [mem_filter,mem_powersetCard,subset_univ,true_and,mem_copyFiber]
  constructor
  · rintro ⟨⟨_,hNo⟩,hproj⟩
    exact ⟨hproj,hNo⟩
  · rintro ⟨hproj,hNo⟩
    have hc := projection_card_of_noRepeatedBase hNo
    rw [hproj,hS] at hc
    exact ⟨⟨hc.symm,hNo⟩,hproj⟩

/-- This counts the actual finite sets of copies in each injective fiber. -/
theorem sum_noRepeatedBase_copies (m : ι → ℕ) (ℓ : ℕ) (w : Finset ι → ℝ) :
    (∑ C ∈ univ.powersetCard ℓ, if NoRepeatedBase C then w (copyProjection m C) else 0) =
      ∑ S ∈ univ.powersetCard ℓ, w S * ∏ i ∈ S, (m i : ℝ) := by
  let A := (univ.powersetCard ℓ).filter (NoRepeatedBase (m:=m))
  have hmap : ∀ C ∈ A, copyProjection m C ∈ (univ : Finset ι).powersetCard ℓ := by
    intro C hC
    obtain ⟨hC,hNo⟩ := mem_filter.mp hC
    exact mem_powersetCard.mpr ⟨subset_univ _,(projection_card_of_noRepeatedBase hNo).trans (mem_powersetCard.mp hC).2⟩
  rw [← sum_filter]
  change (∑ C ∈ A, w (copyProjection m C)) = _
  rw [← sum_fiberwise_of_maps_to hmap]
  apply sum_congr rfl
  intro S hS
  rw [copyFiber_fixed_card (mem_powersetCard.mp hS).2]
  have hs : (∑ C ∈ copyFiber m S, w (copyProjection m C)) = ∑ _C ∈ copyFiber m S, w S := by
    apply sum_congr rfl
    intro C hC
    rw [(mem_copyFiber.mp hC).1]
  rw [hs]
  simp only [sum_const,nsmul_eq_mul,card_copyFiber,Nat.cast_prod]
  ring

#print axioms selectCopies_projection
#print axioms selectCopies_noRepeatedBase
#print axioms selectCopies_injective
#print axioms selectCopies_surjective
#print axioms card_copyFiber
#print axioms sum_noRepeatedBase_copies
end TypedTriangle.WeightedClone
