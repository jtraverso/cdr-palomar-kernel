module
public import RequestProject.TypedTriangle.PaschAdaptiveAssemblyCore
public import RequestProject.TypedTriangle.VortexRawPathsWindowSizeData
set_option maxHeartbeats 4000000 -- build option (original: -DmaxHeartbeats=1600000; raised)
set_option maxRecDepth 16384 -- build option (original: -DmaxRecDepth=8192; raised)
@[expose] public section
-- Source segment: PaschAdaptiveVortexAssembly.lean
open Finset Classical
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 500000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace TypedTriangle.Pasch
open Vortex Vortex.IntrinsicRawPathsPreparedVortex

private theorem child_edges_change_fintype {X I : Type}
    (J : Host X I) (f₁ f₂ : Fintype X) :
    @edges X I f₁ J = @edges X I f₂ J := by
  cases Subsingleton.elim f₁ f₂
  rfl

variable {I Orig Abs : Type} [Fintype Orig] [Fintype Abs]
  {F : Set (Multiset I)} {α₀ q C : ℝ} {β : ℕ → ℝ}
  {h N M d T m : ℕ} {a εRoute t : ℝ}

/-- Assembly interface only: the concrete bank/resource/packing theorem must
discharge AdaptivePaidLayers. Given that construction, every tracked step
uses the actual prepared child and the terminal suffix is the existing exact
assembly. No arbitrary completion is substituted for a paid layer. -/
theorem adaptive_reserved_completion {V : Type} [Fintype V]
    {H : Host V I} {μ : Finset V → ℝ}
    (chain : IntrinsicRawPathsPreparedVortex F α₀ q C β h N M d T m a εRoute t H μ)
    (Cactual αactual ζState : ℝ) (HOrig : Host Orig I) (HAbs : Host Abs I)
    (eOut : Abs ↪ Orig) (R : Finset (Sym2 Abs)) (base : Finset (Finset Orig))
    (Uterminal : Finset Abs) (cost τ σ targetValue : ℝ) (Lbase stepCodegree K : ℕ)
    (hAdjOut : ∀ u v, HAbs.G.Adj u v → HOrig.G.Adj (eOut u) (eOut v))
    (hLabOut : ∀ u, HAbs.lab u = HOrig.lab (eOut u))
    (hAbsorb : ∀ L : Finset (Sym2 Abs), Disjoint R L → IsPhysical HAbs F L →
      (∀ e ∈ L, ∀ v ∈ e, v ∈ Uterminal) → Basal HAbs F (R ∪ L))
    (hCost : 0 ≤ cost) (hτ : 0 < τ) (hn : 0 < Fintype.card Orig)
    (hK : R.card ≤ K) (hReserve : ⌈(K : ℝ)/τ⌉₊ ≤ Fintype.card Orig)
    (hSqrt : ⌈1/τ^2⌉₊ ≤ Fintype.card Orig)
    (hTerminalSize : t ≤ (Nat.sqrt (Nat.sqrt (Fintype.card Orig)) : ℝ))
    (hTarget : |(count base : ℝ)-targetValue| ≤ σ*(Fintype.card Orig : ℝ)^2) :
    LocalLayers chain Cactual αactual ζState →
    AdaptivePaidLayers chain Cactual αactual ζState HOrig cost Lbase stepCodegree
      (Nat.sqrt (Nat.sqrt (Fintype.card Orig))) →
    ∀ s : TrackingState chain Cactual αactual ζState HOrig HAbs eOut R base Uterminal cost τ Lbase stepCodegree,
      ∃ D : Finset (Finset Orig), IsDecomposition HOrig F (edges HOrig) D ∧ base ⊆ D ∧
        |(count D : ℝ)-targetValue| ≤ (σ+3*τ)*(Fintype.card Orig : ℝ)^2 := by
  induction chain with
  | terminal node upper =>
    intro hLayers hRich s
    have hCut : Fintype.card (Survivors node.trim) ≤ Nat.sqrt (Nat.sqrt (Fintype.card Orig)) := by
      exact_mod_cast upper.trans hTerminalSize
    exact TrackingState.complete_at_cutoff _ Cactual αactual ζState HOrig HAbs eOut R base Uterminal
      cost τ σ targetValue Lbase stepCodegree K s hLayers hAdjOut hLabOut hAbsorb
      hCost hτ hn hK hReserve hSqrt hCut hTarget
  | descend node W lower shrink route paths intermediate next_index tail ih =>
    letI : DecidableEq (Survivors node.trim) := Classical.decEq _
    intro hLayers hRich s
    let current := IntrinsicRawPathsPreparedVortex.descend node W lower shrink route paths intermediate next_index tail
    by_cases hCut : Fintype.card (Survivors node.trim) ≤ Nat.sqrt (Nat.sqrt (Fintype.card Orig))
    · exact TrackingState.complete_at_cutoff _ Cactual αactual ζState HOrig HAbs eOut R base Uterminal
        cost τ σ targetValue Lbase stepCodegree K s hLayers hAdjOut hLabOut hAbsorb
        hCost hτ hn hK hReserve hSqrt hCut hTarget
    · have hAdjOrig : ∀ u v, s.actual.host.G.Adj u v →
          HOrig.G.Adj ((s.eAbs.trans eOut) u) ((s.eAbs.trans eOut) v) :=
        fun u v huv => hAdjOut _ _ (s.map_adj u v huv)
      have hLabOrig : ∀ u, s.actual.host.lab u = HOrig.lab ((s.eAbs.trans eOut) u) :=
        fun u => (s.map_lab u).trans (hLabOut _)
      obtain ⟨child,E,D,Rnext,hD,hDisjoint,hPartition,hOldNew,hPaidNew,hPair,hTriples,hStep⟩ :=
        hRich.1 s.actual (s.eAbs.trans eOut) s.available s.codegree s.depth
          (by omega) s.depth_bound s.codegree_bound hAdjOrig hLabOrig s.pair_bound s.triples
      let canonicalFintype : ULift.{0} (Fintype (Survivors tail.head.trim)) := ⟨inferInstance⟩
      let f : Survivors tail.head.trim ↪ Survivors node.trim := nextPreparedEmbedding W tail.head.trim
      have hProtected := s.actual.next_edges
      rw [nextPreparedEdges.eq_2 node W lower shrink route paths intermediate next_index tail] at hProtected
      have hProtected' : embeddedEdges f (edges tail.preparedHost) ⊆ edges s.actual.host := by
        convert hProtected using 1 <;> simp only [head.eq_2,f]
      have hAdj : ∀ u v, child.host.G.Adj u v → s.actual.host.G.Adj (f u) (f v) := by
        intro u v huv
        have heRaw : s(u,v) ∈ edges tail.preparedHost := SparseEdge.mem_edges.mpr (child.graph_le huv)
        have heMap : Sym2.map f s(u,v) ∈ embeddedEdges f (edges tail.preparedHost) :=
          mem_image.mpr ⟨s(u,v),heRaw,rfl⟩
        exact SparseEdge.mem_edges.mp (hProtected' heMap)
      have hLab : ∀ u, child.host.lab u = s.actual.host.lab (f u) := by
        intro u
        have hRaw : tail.preparedHost.lab u = current.preparedHost.lab (f u) := rfl
        exact (congrFun child.labels u).trans (hRaw.trans (congrFun s.actual.labels (f u)).symm)
      have hNextCard : Fintype.card (Survivors tail.head.trim) ≤ W.card := by
        obtain ⟨hEq,hSub,hCard,hSize,hReal⟩ := next_prepared_window_card_data W tail.head.trim
        have hc := card_embeddingWindow f
        have hs : (embeddingWindow f).card ≤ W.card := by
          change (embeddingWindow (nextPreparedEmbedding W tail.head.trim)).card ≤ W.card
          rw [hSize]
          exact Nat.sub_le _ _
        exact hc ▸ hs
      have hShrinkOld : 16*Fintype.card (Survivors tail.head.trim) ≤ Fintype.card (Survivors node.trim) :=
        (Nat.mul_le_mul_left 16 hNextCard).trans shrink
      have hTerminal :
          current.terminalWindow = tail.terminalWindow.map f := by
        dsimp only [current]
        rw [terminalWindow.eq_2 node W lower shrink route paths intermediate next_index tail] <;> rfl
      letI : DecidableEq (Survivors (univ \ W)) := Classical.decEq _
      letI : DecidableEq (Survivors tail.head.trim) := Classical.decEq _
      have hChildEdges := child_edges_change_fintype child.host canonicalFintype.down inferInstance
      have hPartitionCanonical : edges s.actual.host = E ∪ AmbientBank.liftEdges f (edges child.host) := by
        rw [←hChildEdges]
        exact hPartition
      have hDisjointCanonical : Disjoint E (AmbientBank.liftEdges f (edges child.host)) := by
        rw [←hChildEdges]
        exact hDisjoint
      have hShrink : 16*Fintype.card (Survivors tail.head.trim) ≤ Fintype.card (Survivors node.trim) := by
        simpa only [←Nat.card_eq_fintype_card] using hShrinkOld
      let p : PaidPrefix HOrig F (embeddedEdges eOut R) child.host ((f.trans s.eAbs).trans eOut) :=
        PaidPrefix.append (H := HOrig) (F := F) (reserved := embeddedEdges eOut R)
          (J := s.actual.host) (e := s.eAbs.trans eOut) s.prefixData child.host f
          hAdjOrig hLabOrig E D hD hPartitionCanonical hDisjointCanonical
      have hBasePaid : base ⊆ p.paid := by
        change base ⊆ s.prefixData.paid ∪ mapConfiguration (s.eAbs.trans eOut) D
        exact s.base_paid.trans subset_union_left
      have hPaidAvailable : p.paid ⊆ Rnext := by
        change s.prefixData.paid ∪ mapConfiguration (s.eAbs.trans eOut) D ⊆ Rnext
        exact union_subset (s.paid_available.trans hOldNew) hPaidNew
      have hCodegree : s.codegree+stepCodegree ≤ Lbase+stepCodegree*(s.depth+1) := by
        have hh := s.codegree_bound
        nlinarith only [hh]
      have hDepth : 2^(s.depth+1)*Fintype.card (Survivors tail.head.trim) ≤ Fintype.card Orig := by
        have hTwo : 2*Fintype.card (Survivors tail.head.trim) ≤ Fintype.card (Survivors node.trim) := by omega
        calc
          _ = 2^s.depth*(2*Fintype.card (Survivors tail.head.trim)) := by rw [pow_succ]; ring
          _ ≤ 2^s.depth*Fintype.card (Survivors node.trim) := Nat.mul_le_mul_left _ hTwo
          _ ≤ Fintype.card Orig := s.depth_bound
      have hBudget : (count Rnext : ℝ)+remainingPaschBudget cost (Fintype.card Orig)
          (s.depth+1) (Fintype.card (Survivors tail.head.trim)) ≤ count base+τ*(Fintype.card Orig : ℝ)^2 := by
        have hShrinkR : 16*(Fintype.card (Survivors tail.head.trim) : ℝ) ≤
            (Fintype.card (Survivors node.trim) : ℝ) := by exact_mod_cast hShrink
        exact count_budget_preserved_by_paid_step cost (Fintype.card Orig)
          (Fintype.card (Survivors node.trim)) (Fintype.card (Survivors tail.head.trim))
          s.depth (count s.available) (count Rnext) (count base+τ*(Fintype.card Orig : ℝ)^2)
          hCost (by positivity) (by positivity) hShrinkR hStep s.budget
      have hTerminalSubset : tail.terminalWindow.map (f.trans s.eAbs) ⊆ Uterminal := by
        have hEq : tail.terminalWindow.map (f.trans s.eAbs) = current.terminalWindow.map s.eAbs := by
          rw [hTerminal,map_map]
        rw [hEq]
        exact s.terminal_subset
      let sNext : TrackingState tail Cactual αactual ζState HOrig HAbs eOut R base Uterminal
          cost τ Lbase stepCodegree := {
        actual := child
        eAbs := f.trans s.eAbs
        prefixData := p
        available := Rnext
        codegree := s.codegree+stepCodegree
        depth := s.depth+1
        pair_bound := hPair
        triples := hTriples
        base_paid := hBasePaid
        paid_available := hPaidAvailable
        codegree_bound := hCodegree
        depth_bound := hDepth
        budget := hBudget
        map_adj := fun u v huv => s.map_adj (f u) (f v) (hAdj u v huv)
        map_lab := fun u => (hLab u).trans (s.map_lab (f u))
        terminal_subset := hTerminalSubset
      }
      exact ih hLayers.2 hRich.2 sNext

#print axioms adaptive_reserved_completion
end TypedTriangle.Pasch

