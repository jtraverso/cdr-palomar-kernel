/-
Copyright (c) 2026 Juan Pablo Traverso Gianini.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module
public import RequestProject.TypedTriangle.G1ZSplice
public import RequestProject.TypedTriangle.ExplicitIntLift
set_option maxHeartbeats 4000000 -- build option (original: -DmaxHeartbeats=1600000; raised)
set_option maxRecDepth 16384 -- build option (original: -DmaxRecDepth=8192; raised)
@[expose] public section
open Finset Classical
noncomputable section
namespace TypedTriangle.ExplicitCertificate
open Incidence

def compressionCertCost (s H₀ D₀ : ℕ) : ℕ :=
  H₀+(1+3*H₀)*GroupingExplicit.kernelBound ((s+1)^2) (max 1 (3*D₀))*D₀

theorem g1z_of_compression_explicit (s H₀ D₀ : ℕ) :
    ∀ {V I : Type} [Fintype V] (H : Host V I) (F : Set (Multiset I)),
      Compression H F s H₀ D₀ → UniformCert H F (compressionCertCost s H₀ D₀) := by
  let K₀ := GroupingExplicit.kernelBound ((s+1)^2) (max 1 (3*D₀))
  intro V I _ H F cmp
  change UniformCert H F (H₀+(1+3*H₀)*K₀*D₀)
  intro x hx
  have hdm := card_sym2_le cmp.W cmp.card_W
  set W := cmp.W
  -- columnas residuales y realizadores ambientales
  let ι := {T : Finset V // T ∈ allowed H F}
  have hmemL : ∀ T : ι, ind (triEdges T.1) ∈ localGroup H F := fun T =>
    lattice_le_localGroup H F (Submodule.subset_span
      ⟨T.1, (Finset.mem_filter.1 T.2).2, rfl⟩)
  let colT : ι → localGroup H F := fun T => ⟨ind (triEdges T.1), hmemL T⟩
  let B₀ : ι → Fin ((s + 1) ^ 2) → ℤ := fun T => eProj W hdm (cmp.P (colT T))
  let q : ι → Finset V → ℤ := fun T => Pi.single T.1 1 - cmp.C₀ (colT T)
  have hcard3 : ∀ T : ι, (T.1).card = 3 := fun T => (Finset.mem_filter.1 T.2).2.1
  have hB : ∀ T j, |B₀ T j| ≤ (3 * D₀ : ℕ) := by
    intro T j
    refine (abs_eProj_le W hdm _ j).trans ?_
    have := cmp.costP (colT T)
    rw [show (colT T).1 = ind (triEdges T.1) from rfl, l1E_ind_triEdges (hcard3 T)] at this
    push_cast; linarith
  have hq : ∀ T, triBd H F (q T) = eEmb W hdm (B₀ T) := by
    intro T
    simp only [q, B₀, map_sub, triBd_single T.2]
    rw [← cmp.decomp, eEmb_eProj W hdm (cmp.supp _)]
    simp [colT]
  have hJ : ∀ T, ∑ t, |q T t| ≤ (1 + 3 * H₀ : ℕ) := by
    intro T
    have h1 : ∑ t, |q T t| ≤ ∑ t, |(Pi.single T.1 1 : Finset V → ℤ) t| +
        ∑ t, |cmp.C₀ (colT T) t| := by
      rw [← Finset.sum_add_distrib]
      exact Finset.sum_le_sum fun t _ => abs_sub _ _
    have h2 : ∑ t, |(Pi.single T.1 1 : Finset V → ℤ) t| = 1 := by
      rw [Finset.sum_eq_single T.1]
      · simp
      · intro b _ hb; simp [hb]
      · simp
    have h3 := cmp.costC (colT T)
    rw [show (colT T).1 = ind (triEdges T.1) from rfl, l1E_ind_triEdges (hcard3 T)] at h3
    push_cast; linarith
  -- la demanda
  set x' : localGroup H F := ⟨x, lattice_le_localGroup H F hx⟩
  have hsplit : x - eEmb W hdm (eProj W hdm (cmp.P x')) = triBd H F (cmp.C₀ x') := by
    rw [eEmb_eProj W hdm (cmp.supp _)]; exact cmp.decomp x'
  have hspan : eProj W hdm (cmp.P x') ∈ Submodule.span ℤ (Set.range B₀) := by
    have key : ∀ y (hy : y ∈ lattice H F),
        eProj W hdm (cmp.P ⟨y, lattice_le_localGroup H F hy⟩) ∈
          Submodule.span ℤ (Set.range B₀) := by
      intro y hy
      induction hy using Submodule.span_induction with
      | mem y hy =>
        obtain ⟨T, hT, rfl⟩ := hy
        have hTa : T ∈ allowed H F := Finset.mem_filter.2 ⟨Finset.mem_univ _, hT⟩
        exact Submodule.subset_span ⟨⟨T, hTa⟩, rfl⟩
      | zero =>
        have : (⟨0, lattice_le_localGroup H F (Submodule.zero_mem _)⟩ : localGroup H F) = 0 :=
          rfl
        rw [this, map_zero, map_zero]; exact Submodule.zero_mem _
      | add y z hy hz ihy ihz =>
        have : (⟨y + z, lattice_le_localGroup H F (Submodule.add_mem _ hy hz)⟩ :
            localGroup H F) = ⟨y, lattice_le_localGroup H F hy⟩ +
              ⟨z, lattice_le_localGroup H F hz⟩ := rfl
        rw [this, map_add, map_add]; exact Submodule.add_mem _ ihy ihz
      | smul k y hy ihy =>
        have : (⟨k • y, lattice_le_localGroup H F (Submodule.smul_mem _ k hy)⟩ :
            localGroup H F) = k • ⟨y, lattice_le_localGroup H F hy⟩ := rfl
        rw [this, map_smul, map_smul]; exact Submodule.smul_mem _ k ihy
    exact key x hx
  have hcostC : ∑ t, |cmp.C₀ x' t| ≤ H₀ * ∑ e, |x e| := cmp.costC x'
  have hcostP : IntLift.l1 (eProj W hdm (cmp.P x')) ≤ D₀ * ∑ e, |x e| :=
    (l1_eProj_le W hdm _).trans (cmp.costP x')
  obtain ⟨c, hc, hcc⟩ := IntLiftExplicit.recovery_splice_explicit ((s+1)^2) (3*D₀) (triBd H F) (eEmb W hdm) B₀ q H₀ D₀ (1 + 3 * H₀) hB hq hJ
    x (cmp.C₀ x') (eProj W hdm (cmp.P x')) hsplit hcostC hcostP hspan
  refine ⟨c, hc, ?_⟩
  refine hcc.trans (le_of_eq ?_)
  simp only [l1E, K₀]; push_cast; ring


#print axioms g1z_of_compression_explicit
end TypedTriangle.ExplicitCertificate
