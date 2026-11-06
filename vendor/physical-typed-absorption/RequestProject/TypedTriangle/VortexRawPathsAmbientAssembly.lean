/-
Copyright (c) 2026 Juan Pablo Traverso Gianini.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module
public import RequestProject.TypedTriangle.VortexRawPathsPaidAssembly
set_option maxHeartbeats 4000000 -- build option (original: -DmaxHeartbeats=1600000; raised)
set_option maxRecDepth 16384 -- build option (original: -DmaxRecDepth=8192; raised)
@[expose] public section
open Finset Classical
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1600000
namespace TypedTriangle.Vortex
open IntrinsicRawPathsPreparedVortex

private theorem embeddedEdges_comp {X Y Z : Type} (ι : X ↪ Y) (κ : Y ↪ Z)
    (E : Finset (Sym2 X)) :
    embeddedEdges (ι.trans κ) E = embeddedEdges κ (embeddedEdges ι E) := by
  simp only [embeddedEdges,Finset.image_image]
  congr 1
  funext e
  induction e using Sym2.ind with
  | _ u v => rfl

private theorem embeddedEdges_union {X Y : Type} (ι : X ↪ Y)
    (E E' : Finset (Sym2 X)) :
    embeddedEdges ι (E ∪ E') = embeddedEdges ι E ∪ embeddedEdges ι E' := by
  simp only [embeddedEdges,Finset.image_union]

private theorem embeddedEdges_disjoint {X Y : Type} (ι : X ↪ Y)
    {E E' : Finset (Sym2 X)} (hDis : Disjoint E E') :
    Disjoint (embeddedEdges ι E) (embeddedEdges ι E') := by
  apply disjoint_left.mpr
  intro f hf hf'
  obtain ⟨e,he,hef⟩ := mem_image.mp hf
  obtain ⟨e',he',hef'⟩ := mem_image.mp hf'
  have hEq : e = e' := (Sym2.map.injective ι.injective) (hef.trans hef'.symm)
  exact disjoint_left.mp hDis he (hEq ▸ he')

/-- The reserved absorber is retained explicitly. Basal layers glue in the
original host, whereas terminal physicality pushes into the distinct
absorption host, which is not assumed to satisfy H2.
LocalLayers and the exact outer partition must come from the real bank. -/
theorem raw_paths_reserved_assembly_in_ambient_hosts {I V Orig Abs : Type}
    [Fintype V] [Fintype Orig] [Fintype Abs]
    {F : Set (Multiset I)} {α₀ q C : ℝ} {β : ℕ → ℝ}
    {h N M d T m : ℕ} {a εRoute t : ℝ} {H : Host V I} {μ : Finset V → ℝ}
    (chain : IntrinsicRawPathsPreparedVortex F α₀ q C β h N M d T m a εRoute t H μ)
    (Cactual αactual ζState : ℝ) (hLayers : LocalLayers chain Cactual αactual ζState)
    (state : ActualState chain Cactual αactual ζState) (HOrig : Host Orig I) (HAbs : Host Abs I)
    (ιAbs : Survivors chain.head.trim ↪ Abs) (ιOut : Abs ↪ Orig)
    (hAdjOrig : ∀ u v, state.host.G.Adj u v →
      HOrig.G.Adj (ιOut (ιAbs u)) (ιOut (ιAbs v)))
    (hLabOrig : ∀ u, state.host.lab u = HOrig.lab (ιOut (ιAbs u)))
    (hAdjAbs : ∀ u v, state.host.G.Adj u v → HAbs.G.Adj (ιAbs u) (ιAbs v))
    (hLabAbs : ∀ u, state.host.lab u = HAbs.lab (ιAbs u))
    (Pouter : Finset (Sym2 Orig)) (R : Finset (Sym2 Abs))
    (hPouter : Basal HOrig F Pouter)
    (hOuter : edges HOrig = (Pouter ∪ embeddedEdges ιOut R) ∪
      embeddedEdges (ιAbs.trans ιOut) (edges state.host))
    (hOuterDisjoint : Disjoint Pouter (embeddedEdges ιOut R ∪
      embeddedEdges (ιAbs.trans ιOut) (edges state.host)))
    (hReservedDisjoint : Disjoint (embeddedEdges ιOut R)
      (embeddedEdges (ιAbs.trans ιOut) (edges state.host))) :
    let Uterminal := chain.terminalWindow.map ιAbs
    ∃ (P : Finset (Sym2 Orig)) (L : Finset (Sym2 Abs)),
      Basal HOrig F P ∧ Disjoint P (embeddedEdges ιOut (R ∪ L)) ∧
      edges HOrig = P ∪ embeddedEdges ιOut (R ∪ L) ∧ Disjoint R L ∧
      IsPhysical HAbs F L ∧ (∀ e ∈ L, ∀ v ∈ e, v ∈ Uterminal) ∧
      M ≤ Uterminal.card ∧ (Uterminal.card : ℝ) ≤ t := by
  letI : DecidableEq (Survivors chain.head.trim) := Classical.decEq _
  dsimp only
  obtain ⟨Ptail,Ltail,hPtail,hTailDisjoint,hTail,hPhysicalTail,hSupport⟩ :=
    chain.assemble Cactual αactual ζState hLayers state
  let ι := ιAbs.trans ιOut
  let L := embeddedEdges ιAbs Ltail
  have hComposition : embeddedEdges ι Ltail = embeddedEdges ιOut L :=
    embeddedEdges_comp ιAbs ιOut Ltail
  have hChildSplit : embeddedEdges ι (edges state.host) =
      embeddedEdges ι Ptail ∪ embeddedEdges ιOut L := by
    rw [hTail,embeddedEdges_union,hComposition]
  have hPsub : embeddedEdges ι Ptail ⊆ embeddedEdges ι (edges state.host) := by
    rw [hChildSplit]
    exact subset_union_left
  have hLsub : embeddedEdges ιOut L ⊆ embeddedEdges ι (edges state.host) := by
    rw [hChildSplit]
    exact subset_union_right
  have hOuterR : Disjoint Pouter (embeddedEdges ιOut R) :=
    hOuterDisjoint.mono_right subset_union_left
  have hOuterChild : Disjoint Pouter (embeddedEdges ι (edges state.host)) :=
    hOuterDisjoint.mono_right subset_union_right
  have hInnerL : Disjoint (embeddedEdges ι Ptail) (embeddedEdges ιOut L) := by
    have hLift := embeddedEdges_disjoint ι hTailDisjoint
    rw [hComposition] at hLift
    exact hLift
  have hPacked := hPouter.union (basal_embedding state.host HOrig F ι hAdjOrig hLabOrig hPtail)
    (hOuterChild.mono_right hPsub)
  have hDisR : Disjoint (Pouter ∪ embeddedEdges ι Ptail) (embeddedEdges ιOut R) :=
    disjoint_union_left.mpr ⟨hOuterR,(hReservedDisjoint.mono_right hPsub).symm⟩
  have hDisL : Disjoint (Pouter ∪ embeddedEdges ι Ptail) (embeddedEdges ιOut L) :=
    disjoint_union_left.mpr ⟨hOuterChild.mono_right hLsub,hInnerL⟩
  have hDis : Disjoint (Pouter ∪ embeddedEdges ι Ptail) (embeddedEdges ιOut (R ∪ L)) := by
    rw [embeddedEdges_union]
    exact disjoint_union_right.mpr ⟨hDisR,hDisL⟩
  have hPartition : edges HOrig =
      (Pouter ∪ embeddedEdges ι Ptail) ∪ embeddedEdges ιOut (R ∪ L) := by
    rw [hOuter,hChildSplit,embeddedEdges_union]
    ac_rfl
  have hRL : Disjoint R L := by
    apply disjoint_left.mpr
    intro e heR heL
    have heR' : Sym2.map ιOut e ∈ embeddedEdges ιOut R := mem_image.mpr ⟨e,heR,rfl⟩
    have heL' : Sym2.map ιOut e ∈ embeddedEdges ιOut L := mem_image.mpr ⟨e,heL,rfl⟩
    exact disjoint_left.mp hReservedDisjoint heR' (hLsub heL')
  have hPhysicalAbs : IsPhysical HAbs F L :=
    physical_embedding state.host HAbs F ιAbs hAdjAbs hLabAbs hPhysicalTail
  have hUcard : (chain.terminalWindow.map ιAbs).card = chain.terminalOrder := by
    rw [Finset.card_map,chain.card_terminalWindow]
  refine ⟨Pouter ∪ embeddedEdges ι Ptail,L,hPacked,hDis,hPartition,hRL,hPhysicalAbs,?_,?_,?_⟩
  · intro e he v hv
    obtain ⟨f,hf,rfl⟩ := mem_image.mp he
    obtain ⟨u,hu,rfl⟩ := Sym2.mem_map.mp hv
    exact mem_map.mpr ⟨u,hSupport f hf u hu,rfl⟩
  · rw [hUcard]
    exact chain.terminalOrder_bounds.1
  · rw [hUcard]
    exact chain.terminalOrder_bounds.2

/-- Final exact glue once the actual G2 absorber has decomposed R ∪ L in
its own absorption host. This lemma is not a construction of that absorber. -/
theorem decomposition_of_reserved_absorption {Orig Abs I : Type}
    [Fintype Orig] [Fintype Abs] (HOrig : Host Orig I) (HAbs : Host Abs I)
    (F : Set (Multiset I)) (ιOut : Abs ↪ Orig)
    (hAdj : ∀ u v, HAbs.G.Adj u v → HOrig.G.Adj (ιOut u) (ιOut v))
    (hLab : ∀ u, HAbs.lab u = HOrig.lab (ιOut u))
    (P : Finset (Sym2 Orig)) (R L : Finset (Sym2 Abs))
    (hP : Basal HOrig F P) (hDis : Disjoint P (embeddedEdges ιOut (R ∪ L)))
    (hPartition : edges HOrig = P ∪ embeddedEdges ιOut (R ∪ L))
    (hAbsorbed : Basal HAbs F (R ∪ L)) : Basal HOrig F (edges HOrig) := by
  rw [hPartition]
  exact hP.union (basal_embedding HAbs HOrig F ιOut hAdj hLab hAbsorbed) hDis

#print axioms raw_paths_reserved_assembly_in_ambient_hosts
#print axioms decomposition_of_reserved_absorption
end TypedTriangle.Vortex
