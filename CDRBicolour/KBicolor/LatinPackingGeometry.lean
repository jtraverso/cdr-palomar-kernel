/-
Copyright (c) 2026 Juan Pablo Traverso Gianini.
Released under Apache 2.0 license.
Authors: Juan Pablo Traverso Gianini
-/
module

public import CDRBicolour.KBicolor.LatinCompletionReplacement
public import CDRBicolour.KBicolor.LatinIsotopyProbabilities
public import CDRBicolour.KBicolor.PaschPartiteParity

/-! # The fixed tripartite universe of all Latin replacements -/

@[expose] public section
noncomputable section
set_option autoImplicit false

namespace CDRBicolour.KBicolor.LatinPasch
open Finset Classical TypedTriangle CDRBicolour.Absorption
variable {k n m : ℕ} {lab : Fin n → Fin k} {X Y : Fin k}
variable {r c s : Fin m → Fin n} (h : LatPlace lab X Y r c s)
include h

def placedTriangle (r c s : Fin m → Fin n) (i j q : Fin m) : Finset (Fin n) :=
  {r i, c j, s q}

def latinUniverse (r c s : Fin m → Fin n) : Finset (Finset (Fin n)) :=
  (univ : Finset (Fin m×Fin m×Fin m)).image
    (fun p => placedTriangle r c s p.1 p.2.1 p.2.2)

def slotPart (r c s : Fin m → Fin n) (v : Fin n) : Option (Fin 3) :=
  if v ∈ univ.image r then some 0 else if v ∈ univ.image c then some 1
  else if v ∈ univ.image s then some 2 else none

theorem slotPart_row (i : Fin m) : slotPart r c s (r i) = some 0 := by
  simp [slotPart, mem_image.mpr ⟨i, mem_univ _, rfl⟩]

theorem slotPart_column (j : Fin m) : slotPart r c s (c j) = some 1 := by
  have hn : c j ∉ univ.image r := by
    intro hh
    obtain ⟨i, _, he⟩ := mem_image.mp hh
    exact h.rc i j he
  simp [slotPart, hn, mem_image.mpr ⟨j, mem_univ _, rfl⟩]

theorem slotPart_symbol (q : Fin m) : slotPart r c s (s q) = some 2 := by
  have hr : s q ∉ univ.image r := by
    intro hh
    obtain ⟨i, _, he⟩ := mem_image.mp hh
    exact h.rs i q he
  have hc : s q ∉ univ.image c := by
    intro hh
    obtain ⟨j, _, he⟩ := mem_image.mp hh
    exact h.cs j q he
  simp [slotPart, hr, hc, mem_image.mpr ⟨q, mem_univ _, rfl⟩]

theorem slotPart_zero_iff (v : Fin n) : slotPart r c s v = some 0 ↔ v ∈ univ.image r := by
  unfold slotPart
  split_ifs <;> simp_all

theorem slotPart_one_iff (v : Fin n) : slotPart r c s v = some 1 ↔ v ∈ univ.image c := by
  constructor
  · unfold slotPart
    split_ifs <;> simp_all
  · intro hv
    obtain ⟨j, _, rfl⟩ := mem_image.mp hv
    exact slotPart_column h j

theorem slotPart_two_iff (v : Fin n) : slotPart r c s v = some 2 ↔ v ∈ univ.image s := by
  constructor
  · unfold slotPart
    split_ifs <;> simp_all
  · intro hv
    obtain ⟨q, _, rfl⟩ := mem_image.mp hv
    exact slotPart_symbol h q

theorem partite_iff_universe (T : Finset (Fin n)) :
    IsPartite (slotPart r c s) T ↔ T ∈ latinUniverse r c s := by
  constructor
  · rintro ⟨hcard, hc⟩
    obtain ⟨u, hu⟩ := card_pos.mp (show 0 < #(T.filter (fun v => slotPart r c s v = some 0)) by rw [hc]; norm_num)
    obtain ⟨v, hv⟩ := card_pos.mp (show 0 < #(T.filter (fun v => slotPart r c s v = some 1)) by rw [hc]; norm_num)
    obtain ⟨w, hw⟩ := card_pos.mp (show 0 < #(T.filter (fun v => slotPart r c s v = some 2)) by rw [hc]; norm_num)
    obtain ⟨huT, hu⟩ := mem_filter.mp hu
    obtain ⟨hvT, hv⟩ := mem_filter.mp hv
    obtain ⟨hwT, hw⟩ := mem_filter.mp hw
    obtain ⟨i, _, hi⟩ := mem_image.mp ((slotPart_zero_iff h u).mp hu)
    obtain ⟨j, _, hj⟩ := mem_image.mp ((slotPart_one_iff h v).mp hv)
    obtain ⟨q, _, hq⟩ := mem_image.mp ((slotPart_two_iff h w).mp hw)
    subst u
    subst v
    subst w
    have heq : T = placedTriangle r c s i j q := by
      symm
      apply eq_of_subset_of_card_le
        (insert_subset_iff.mpr ⟨huT, insert_subset_iff.mpr ⟨hvT, singleton_subset_iff.mpr hwT⟩⟩)
      rw [hcard]
      simp [placedTriangle, h.rc i j, h.rs i q, h.cs j q]
    exact mem_image.mpr ⟨(i,j,q), mem_univ _, heq.symm⟩
  · intro hT
    obtain ⟨⟨i,j,q⟩, _, rfl⟩ := mem_image.mp hT
    refine ⟨by simp [placedTriangle, h.rc i j, h.rs i q, h.cs j q], fun a => ?_⟩
    fin_cases a <;> simp [placedTriangle, filter_insert, filter_singleton,
      slotPart_row h, slotPart_column h, slotPart_symbol h]

theorem placedTriangle_mem_packing (l : Fin m → Fin m → Fin m) (i j q : Fin m) :
    placedTriangle r c s i j q ∈ latPackK r c s l ↔ l i j = q := by
  constructor
  · intro hm
    obtain ⟨⟨i',j'⟩, _, he⟩ := mem_image.mp hm
    obtain ⟨rfl, rfl, hq⟩ := mem_tri_iffK h he
    exact hq
  · intro he
    exact mem_image.mpr ⟨(i,j), mem_univ _, by simp only [he, placedTriangle]⟩

theorem packing_subset_universe (l : Fin m → Fin m → Fin m) :
    latPackK r c s l ⊆ latinUniverse r c s := by
  intro T hT
  obtain ⟨⟨i,j⟩, _, rfl⟩ := mem_image.mp hT
  exact mem_image.mpr ⟨(i,j,l i j), mem_univ _, rfl⟩

theorem residual_not_universe (l₀ : Fin m → Fin m → Fin m)
    {D : Finset (Finset (Fin n))}
    (hD : IsDecomposition (kHost lab) (bicF k) (edges (kHost lab)) D)
    (hsub : latPackK r c s l₀ ⊆ D) : Disjoint (D \ latPackK r c s l₀) (latinUniverse r c s) := by
  apply disjoint_left.mpr
  intro T hTR hTU
  obtain ⟨⟨i,j,q⟩, _, rfl⟩ := mem_image.mp hTU
  let Q₀ : Finset (Fin n) := {r i, c j, s (l₀ i j)}
  have hQ₀ : Q₀ ∈ latPackK r c s l₀ := mem_image.mpr ⟨(i,j), mem_univ _, rfl⟩
  have heT : s(r i, c j) ∈ triEdges (placedTriangle r c s i j q) := by
    rw [placedTriangle, triEdges_triple (h.rc i j) (h.rs i q) (h.cs j q)]
    simp
  have heQ : s(r i, c j) ∈ triEdges Q₀ := by
    rw [triEdges_triple (h.rc i j) (h.rs i _) (h.cs j _)]
    simp
  have heq := hD.unique (mem_sdiff.mp hTR).1 (hsub hQ₀) heT heQ
  exact (mem_sdiff.mp hTR).2 (heq ▸ hQ₀)

theorem isotopy_isLatin (l : Fin m → Fin m → Fin m) (hl : _root_.STS.IsLatin l)
    (ρ σ : Equiv.Perm (Fin m)) : _root_.STS.IsLatin (isotopyValue l ρ σ) := by
  exact ⟨fun i => σ.bijective.comp (hl.1 (ρ i)),
    fun j => σ.bijective.comp ((hl.2 j).comp ρ.bijective)⟩

end CDRBicolour.KBicolor.LatinPasch
