/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license.
Authors: Juan Pablo Traverso Gianini
-/
module

public import CDRBicolour.Master.L168
public import Balanced.Bridge

/-!
# Rudašová–Soták, Theorem 3.1 (Palomar)

Palomar entry PALOMAR-2026-11-05-000001 (`jtraverso/rudasova-sotak-equitable-strong` @ `57535a7`,
thin wrapper): the proof is `Balanced.exists_equitable_strong` in `Balanced.Bridge` of the pinned
dependency `jtraverso/plantholt-overfull-criterion` @ `28ff33d` (PALOMAR-2026-11-04-000016), which
is already our dependency `plantholt_overfull`.

The Palomar statement uses colourings of the line graph (`G.lineGraph.Coloring (Fin k)`, palettes
as sets, colour classes measured with `Set.ncard`); ours (`Master.RS_Theorem_3_1`) uses a map
`Sym2 V → Fin k` proper on `G.edgeFinset`, palettes `present G χ v` and `IsEquitable` on
`G.edgeFinset`.  `rs_theorem_3_1` translates in both directions:

* a proper `χ` gives a line-graph colouring `lgColoring χ` with the same palettes;
* the equitable strong colouring `C'` is extended off the edges by `χ`; palettes and colour-class
  sizes agree (`mem_palette_iff`, `ncard_colorClass_eq`).
-/

@[expose] public section

namespace CDRBicolour.Palomar

open Finset SimpleGraph LeanPool.Vizing LeanPool.Vizing.ColourClasses
  LeanPool.Vizing.EquitableDefinitions CDRBicolour.Prefix

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]
  {k : ℕ}

theorem share_of_not_disjoint {e f : Sym2 V} (h : ¬ Disjoint e.toFinset f.toFinset) :
    ∃ v, v ∈ e ∧ v ∈ f := by
  rw [Finset.not_disjoint_iff] at h
  obtain ⟨v, he, hf⟩ := h
  exact ⟨v, Sym2.mem_toFinset.1 he, Sym2.mem_toFinset.1 hf⟩

/-- The line-graph colouring of a proper edge colouring. -/
def lgColoring (χ : Sym2 V → Fin k) (hχ : ProperOn G.edgeFinset χ) :
    G.lineGraph.Coloring (Fin k) :=
  Coloring.mk (fun e => χ e.1) fun {e f} hadj hc => by
    rw [lineGraph_adj_iff_exists] at hadj
    obtain ⟨hne, v, hve, hvf⟩ := hadj
    have := hχ e.1 (mem_edgeFinset.2 e.2) f.1 (mem_edgeFinset.2 f.2)
      (fun h => hne (Subtype.ext h)) hc
    exact Finset.disjoint_left.1 this (Sym2.mem_toFinset.2 hve) (Sym2.mem_toFinset.2 hvf)

/-- Palettes of a line-graph colouring agree with `present` of any map extending it. -/
theorem mem_palette_iff (C : G.lineGraph.Coloring (Fin k)) (χ : Sym2 V → Fin k)
    (hC : ∀ e : G.edgeSet, C e = χ e.1) (v : V) (θ : Fin k) :
    θ ∈ Balanced.palette C v ↔ θ ∈ present G χ v := by
  unfold Balanced.palette present
  constructor
  · rintro ⟨e, hv, rfl⟩
    exact mem_image.2 ⟨e.1, mem_incidenceFinset.2 ⟨e.2, hv⟩, (hC e).symm⟩
  · intro h
    obtain ⟨e, he, rfl⟩ := mem_image.1 h
    obtain ⟨he1, he2⟩ := mem_incidenceFinset.1 he
    exact ⟨⟨e, he1⟩, he2, hC _⟩

/-- Colour-class sizes agree. -/
theorem ncard_colorClass_eq (C : G.lineGraph.Coloring (Fin k)) (χ : Sym2 V → Fin k)
    (hC : ∀ e : G.edgeSet, C e = χ e.1) (θ : Fin k) :
    (C.colorClass θ).ncard = (colourClass G.edgeFinset χ θ).card := by
  rw [← Set.ncard_coe_finset, ← Set.ncard_image_of_injective _ Subtype.val_injective]
  congr 1
  ext e
  simp only [Set.mem_image, Coloring.colorClass, Set.mem_ofPred_eq, colourClass, coe_filter,
    mem_edgeFinset]
  constructor
  · rintro ⟨e, h, rfl⟩
    exact ⟨e.2, (hC e).symm.trans h⟩
  · rintro ⟨he, h⟩
    exact ⟨⟨e, he⟩, (hC _).trans h, rfl⟩

/-- **Rudašová–Soták, Theorem 3.1**, in the literal form `Master.RS_Theorem_3_1`, from the Palomar
formalization. -/
theorem rs_theorem_3_1 : Master.RS_Theorem_3_1.{0} := by
  intro V _ _ G _ k hvdc
  obtain ⟨χ, hχ, hvd⟩ := hvdc
  have hstr : Balanced.IsStrong (lgColoring χ hχ) := by
    intro u v h
    by_contra hne
    apply hvd u v hne
    ext θ
    rw [← mem_palette_iff (lgColoring χ hχ) χ (fun _ => rfl),
      ← mem_palette_iff (lgColoring χ hχ) χ (fun _ => rfl), h]
  obtain ⟨C', hs, he⟩ := Balanced.exists_equitable_strong le_rfl (lgColoring χ hχ) hstr
  let χ' : Sym2 V → Fin k := fun e => if h : e ∈ G.edgeSet then C' ⟨e, h⟩ else χ e
  have hC' : ∀ e : G.edgeSet, C' e = χ' e.1 := fun e => by
    simp [χ', e.2]
  refine ⟨χ', ?_, ?_, ?_⟩
  · intro e he f hf hne hc
    rw [mem_edgeFinset] at he hf
    by_contra hd
    obtain ⟨v, hve, hvf⟩ := share_of_not_disjoint hd
    have hadj : G.lineGraph.Adj ⟨e, he⟩ ⟨f, hf⟩ := by
      rw [lineGraph_adj_iff_exists]
      exact ⟨fun h => hne (congrArg Subtype.val h), v, hve, hvf⟩
    exact C'.valid hadj ((hC' ⟨e, he⟩).trans (hc.trans (hC' ⟨f, hf⟩).symm))
  · intro u v hne h
    apply hne
    apply hs
    ext θ
    rw [mem_palette_iff C' χ' hC', mem_palette_iff C' χ' hC', h]
  · intro x y
    rw [← ncard_colorClass_eq C' χ' hC', ← ncard_colorClass_eq C' χ' hC']
    exact he x y

end CDRBicolour.Palomar
