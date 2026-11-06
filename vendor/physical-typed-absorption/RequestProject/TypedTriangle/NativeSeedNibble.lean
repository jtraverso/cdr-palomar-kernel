/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module
public import RequestProject.TypedTriangle.Packing
public import PartitionedTriangleAbsorption.Nibble.Consumer
set_option maxHeartbeats 4000000 -- build option (original: -DmaxHeartbeats=1600000; raised)
set_option maxRecDepth 16384 -- build option (original: -DmaxRecDepth=8192; raised)
@[expose] public section

/-! Ordinary physical nibble from exact seed loads. This reuses the proved
Paper I nibble closure, without importing its Nash--Williams theorem. Labels
are arbitrary and no balancing, typicality or new degree assumption is imposed.
The output is a real packing and a bound at EVERY original vertex. Additional
monitors and the global refiner capacity remain separate obligations. -/

open Finset Classical
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace TypedTriangle.NativeNibble
open PartitionedTriangleAbsorption
variable {V I : Type*} [Fintype V] [DecidableEq V]

lemma nibble_triEdges_eq (T : Finset V) : Nibble.triEdges T = triEdges T := by
  ext e
  induction e using Sym2.ind with
  | _ x y => rw [Nibble.mem_triEdges,TypedTriangle.mem_triEdges]

def system (H : Host V I) (F : Set (Multiset I)) : Nibble.TriSystem V (allowed H F).card where
  tri i := ((allowed H F).equivFin.symm i).val
  card_tri i := (isAllowed_of_mem_allowed ((allowed H F).equivFin.symm i).property).1
  tri_inj := Subtype.val_injective.comp (allowed H F).equivFin.symm.injective

lemma system_mem (H : Host V I) (F : Set (Multiset I)) (i : Fin (allowed H F).card) :
    (system H F).tri i ∈ allowed H F := ((allowed H F).equivFin.symm i).property

lemma system_surj (H : Host V I) (F : Set (Multiset I)) {T : Finset V}
    (hT : T ∈ allowed H F) : ∃ i, (system H F).tri i = T :=
  ⟨(allowed H F).equivFin ⟨T,hT⟩,by simp [system]⟩

def weights (H : Host V I) (F : Set (Multiset I)) (φ : Finset V → ℝ) :
    Fin (allowed H F).card → ℝ := fun i => φ ((system H F).tri i)

lemma system_load (H : Host V I) (F : Set (Multiset I)) (φ : Finset V → ℝ) (e : Sym2 V) :
    (system H F).load (weights H F φ) e =
      ∑ T ∈ (allowed H F).filter (fun T => e ∈ triEdges T), φ T := by
  unfold Nibble.TriSystem.load Nibble.TriSystem.edgeTris weights
  refine sum_bij (fun i _ => (system H F).tri i) ?_ ?_ ?_ ?_
  · intro i hi
    exact mem_filter.mpr ⟨system_mem H F i,by
      simpa only [nibble_triEdges_eq] using (mem_filter.mp hi).2⟩
  · intro i _ j _ hij
    exact (system H F).tri_inj hij
  · intro T hT
    obtain ⟨i,hi⟩ := system_surj H F (mem_filter.mp hT).1
    refine ⟨i,mem_filter.mpr ⟨mem_univ _,?_⟩,hi⟩
    rw [nibble_triEdges_eq,hi]
    exact (mem_filter.mp hT).2
  · intro i _; rfl

def packed (H : Host V I) (F : Set (Multiset I))
    (P : Finset (Fin (allowed H F).card)) : Finset (Finset V) := P.image (system H F).tri

lemma packed_edges (H : Host V I) (F : Set (Multiset I)) (P : Finset (Fin (allowed H F).card)) :
    Nibble.edgesOf (system H F) P = (packed H F P).biUnion triEdges := by
  rw [packed,image_biUnion]
  simp only [Nibble.edgesOf,nibble_triEdges_eq]

lemma packed_isPacking (H : Host V I) (F : Set (Multiset I))
    (P : Finset (Fin (allowed H F).card)) (hP : Nibble.IsPacking (system H F) P) :
    TypedTriangle.IsPacking H F (packed H F P) := by
  constructor
  · intro T hT
    obtain ⟨i,hi,rfl⟩ := mem_image.mp hT
    exact isAllowed_of_mem_allowed (system_mem H F i)
  · intro T hT U hU hne
    obtain ⟨i,hi,rfl⟩ := mem_image.mp hT
    obtain ⟨j,hj,rfl⟩ := mem_image.mp hU
    simpa only [nibble_triEdges_eq] using
      hP i hi j hj (fun hij => hne (by rw [hij]))

/-- Exact physical loads and a uniform coefficient cap construct a packing
with uniformly small leftover degrees. No regularization provider is assumed. -/
theorem packing_of_exact_weights (b η : ℝ) (hb : 0 < b) (hη : 0 < η) (hη1 : η ≤ 1) :
    ∃ n₀ : ℕ, ∀ {V I : Type} [Fintype V] (H : Host V I) (F : Set (Multiset I))
      (φ : Finset V → ℝ), n₀ ≤ Fintype.card V →
      (∀ T ∈ allowed H F, 0 ≤ φ T ∧ φ T ≤ b / Fintype.card V) →
      (∀ e ∈ edges H, ∑ T ∈ (allowed H F).filter (fun T => e ∈ triEdges T), φ T = 1) →
      ∃ P : Finset (Finset V), P ⊆ allowed H F ∧ TypedTriangle.IsPacking H F P ∧
        ∀ v, (((edges H \ P.biUnion triEdges).filter (fun e => v ∈ e)).card : ℝ) ≤
          η * Fintype.card V := by
  obtain ⟨n₀,hn⟩ := Nibble.nibble_packing b η hb hη hη1
  refine ⟨n₀,?_⟩
  intro V I _ H F φ hcard hφ hload
  classical
  obtain ⟨P,hP,hdeg⟩ := hn V hcard (allowed H F).card (system H F) (edges H)
    (weights H F φ) (fun i => triEdges_subset_edges (isAllowed_of_mem_allowed (system_mem H F i)))
    (fun i => (hφ _ (system_mem H F i)).1) (fun i => (hφ _ (system_mem H F i)).2)
    (fun e he => by rw [system_load]; exact hload e he)
  refine ⟨packed H F P,?_,packed_isPacking H F P hP,?_⟩
  · intro T hT; obtain ⟨i,hi,rfl⟩ := mem_image.mp hT; exact system_mem H F i
  · rw [packed_edges] at hdeg
    exact hdeg

/-- H1 of the original theorem alone gives ordinary nibble packing with a
prescribed local residual tolerance, uniformly before the host and label family. -/
theorem packing_of_diffuse_seed (C η : ℝ) (hC : 1 ≤ C) (hη : 0 < η) (hη1 : η ≤ 1) :
    ∃ n₀ : ℕ, ∀ {V I : Type} [Fintype V] (H : Host V I) (F : Set (Multiset I))
      (φ : Finset V → ℝ), n₀ ≤ Fintype.card V → IsDiffuseSeed H F C φ →
      ∃ P : Finset (Finset V), P ⊆ allowed H F ∧ TypedTriangle.IsPacking H F P ∧
        ∀ v, (((edges H \ P.biUnion triEdges).filter (fun e => v ∈ e)).card : ℝ) ≤
          η * Fintype.card V := by
  obtain ⟨n₀,hn⟩ := packing_of_exact_weights C η (by linarith) hη hη1
  refine ⟨max n₀ 1,?_⟩
  intro V I _ H F φ hcard hφ
  have hnpos : (0 : ℝ) < Fintype.card V := by
    exact_mod_cast (show 0 < Fintype.card V by omega)
  apply hn H F φ ((le_max_left _ _).trans hcard)
  · intro T hT
    obtain ⟨hlo,hhi⟩ := hφ.1 T (isAllowed_of_mem_allowed hT)
    exact ⟨(by positivity : (0 : ℝ) ≤ 1 / (C * Fintype.card V)).trans hlo,hhi⟩
  · intro e he
    exact hφ.2 e (by simpa [edges] using he)

/-- The ordinary nibble plus H2 gives an actual sparse residual in the ambient
INTEGER physical lattice. No intrinsic lattice claim for the residual graph is
made, and no preassigned stock is consumed by an unspecified repair. -/
theorem physical_leftover_of_H1H2 (C η : ℝ) (hC : 1 ≤ C) (hη : 0 < η) (hη1 : η ≤ 1) :
    ∃ n₀ : ℕ, ∀ {V I : Type} [Fintype V] (H : Host V I) (F : Set (Multiset I))
      (φ : Finset V → ℝ), n₀ ≤ Fintype.card V → IsDiffuseSeed H F C φ →
      IsPhysical H F (edges H) →
      ∃ P : Finset (Finset V), P ⊆ allowed H F ∧ TypedTriangle.IsPacking H F P ∧
        IsPhysical H F (edges H \ P.biUnion triEdges) ∧
        ∀ v, (((edges H \ P.biUnion triEdges).filter (fun e => v ∈ e)).card : ℝ) ≤
          η * Fintype.card V := by
  obtain ⟨n₀,hn⟩ := packing_of_diffuse_seed C η hC hη hη1
  refine ⟨n₀,?_⟩
  intro V I _ H F φ hcard hφ hH2
  obtain ⟨P,hPsub,hP,hdeg⟩ := hn H F φ hcard hφ
  have hQ : P.biUnion triEdges ⊆ edges H := by
    intro e he
    obtain ⟨T,hT,heT⟩ := mem_biUnion.mp he
    exact triEdges_subset_edges (hP.1 T hT) heT
  exact ⟨P,hPsub,hP,isPhysical_sdiff hH2 (isPhysical_of_isDecomposition hP.isDecomposition) hQ,hdeg⟩

end TypedTriangle.NativeNibble
