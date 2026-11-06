module
public import RequestProject.TypedTriangle.PaschRichBankHistory
set_option maxHeartbeats 4000000 -- build option (original: -DmaxHeartbeats=1600000; raised)
set_option maxRecDepth 16384 -- build option (original: -DmaxRecDepth=8192; raised)
@[expose] public section
open Finset Classical
noncomputable section
set_option autoImplicit false
namespace TypedTriangle.Pasch.AmbientBank
open S07V40
variable {X V Q C : Type*} [Fintype X] [Fintype V] [AddCommGroup Q] [Fintype C]

def edgeEmbedding (ι : X ↪ V) : Sym2 X ↪ Sym2 V :=
  ⟨Sym2.map ι, Sym2.map.injective ι.injective⟩

def liftEdges (ι : X ↪ V) (E : Finset (Sym2 X)) : Finset (Sym2 V) := E.map (edgeEmbedding ι)

def pullEdges (ι : X ↪ V) (B : Finset (Sym2 V)) : Finset (Sym2 X) :=
  B.preimage (edgeEmbedding ι) (edgeEmbedding ι).injective.injOn

def pullVertices (ι : X ↪ V) (Z : Finset V) : Finset X := Z.preimage ι ι.injective.injOn

def zeroCharge (ι : X ↪ V) (w : Sym2 X → Q) (f : Sym2 V) : Q :=
  if h : ∃ g, edgeEmbedding ι g=f then w h.choose else 0

theorem zeroCharge_apply (ι : X ↪ V) (w : Sym2 X → Q) (f : Sym2 X) :
    zeroCharge ι w (edgeEmbedding ι f)=w f := by
  unfold zeroCharge
  rw [dif_pos (show ∃ g, edgeEmbedding ι g=edgeEmbedding ι f from ⟨f,rfl⟩)]
  congr 1
  exact (edgeEmbedding ι).injective (Classical.choose_spec (show ∃ g, edgeEmbedding ι g=edgeEmbedding ι f from ⟨f,rfl⟩))

/-- S is instantiated with the local order |X| before this operation. Its
q, zmax, E and P are copied exactly; card V is never used to rescale them. -/
def liftSetting (ι : X ↪ V) (S : MacroSetting X Q C) : MacroSetting V Q C where
  w := zeroCharge ι S.w
  g := S.g
  K Z := S.K (pullVertices ι Z)
  basal E := ∃ D, E=liftEdges ι D ∧ S.basal D
  P := S.P
  q := S.q
  E := S.E
  zmax := S.zmax

def liftCell (ι : X ↪ V) (c : Cell X) : Cell V := ⟨liftEdges ι c.A, liftEdges ι c.Y⟩

theorem liftCell_total (ι : X ↪ V) (c : Cell X) :
    (liftCell ι c).tot=liftEdges ι c.tot := by
  exact (Finset.map_union c.A c.Y).symm

theorem pull_degree_le (ι : X ↪ V) (B : Finset (Sym2 V)) (x : X) :
    deg (pullEdges ι B) x ≤ deg B (ι x) := by
  change ((pullEdges ι B).filter (fun f => x∈f)).card ≤ (B.filter (fun f => ι x∈f)).card
  rw [←card_map (s := (pullEdges ι B).filter (fun f => x∈f)) (edgeEmbedding ι)]
  apply card_le_card
  intro f hf
  obtain ⟨g,hg,rfl⟩ := mem_map.mp hf
  obtain ⟨hg,hx⟩ := mem_filter.mp hg
  exact mem_filter.mpr ⟨mem_preimage.mp hg, Sym2.mem_map.mpr ⟨x,hx,rfl⟩⟩

theorem charge_lift (ι : X ↪ V) (w : Sym2 X → Q) (D : Finset (Sym2 X)) :
    charge (zeroCharge ι w) (liftEdges ι D)=charge w D := by
  unfold charge liftEdges
  rw [sum_map]
  exact sum_congr rfl (fun f _ => zeroCharge_apply ι w f)

/-- Ordinary GoodCell transports from the real local forbidden edges and
deleted vertices. No previous Pasch universe is pulled back here. -/
theorem goodCell_lift (ι : X ↪ V) (S : MacroSetting X Q C)
    (B : Finset (Sym2 V)) (Z : Finset V) (l : Lab C S.P) (c : Cell X)
    (hc : GoodCell S (pullEdges ι B) (pullVertices ι Z) l c) :
    GoodCell (liftSetting ι S) B Z l (liftCell ι c) := by
  obtain ⟨hAY,hBasalA,hBasalT,hDis,hAvoid,hSize,hCharge⟩ := hc
  refine ⟨?_, ⟨c.A,rfl,hBasalA⟩, ⟨c.tot,liftCell_total ι c,hBasalT⟩, ?_, ?_, ?_, ?_⟩
  · rw [disjoint_left]
    intro f hfA hfY
    obtain ⟨a,ha,hae⟩ := mem_map.mp hfA
    obtain ⟨b,hb,hbe⟩ := mem_map.mp hfY
    have hab := (edgeEmbedding ι).injective (hae.trans hbe.symm)
    exact disjoint_left.mp hAY ha (hab ▸ hb)
  · rw [liftCell_total, disjoint_left]
    intro f hf hfB
    obtain ⟨g,hg,rfl⟩ := mem_map.mp hf
    exact disjoint_left.mp hDis hg (mem_preimage.mpr hfB)
  · rw [liftCell_total]
    intro f hf v hv hvf
    obtain ⟨g,hg,rfl⟩ := mem_map.mp hf
    obtain ⟨x,hx,rfl⟩ := Sym2.mem_map.mp hvf
    exact hAvoid g hg x (mem_preimage.mpr hv) hx
  · rw [liftCell_total, liftEdges, card_map]
    exact hSize
  · change charge (zeroCharge ι S.w) (liftEdges ι c.Y)=sgnQ l.1 (S.g l.2.1)
    rw [charge_lift]
    exact hCharge

theorem degree_zero_outside_image (ι : X ↪ V) (D : Finset (Sym2 X)) (v : V)
    (hv : ¬ ∃ x, ι x=v) : deg (liftEdges ι D) v=0 := by
  apply card_eq_zero.mpr
  apply eq_empty_iff_forall_notMem.mpr
  intro f hf
  obtain ⟨hf,hvf⟩ := mem_filter.mp hf
  obtain ⟨g,_,rfl⟩ := mem_map.mp hf
  obtain ⟨x,_,hxv⟩ := Sym2.mem_map.mp hvf
  exact hv ⟨x,hxv⟩

/-- Positivity of the LOCAL saturation threshold excludes every vertex
outside the image, irrespective of the larger ambient order. -/
theorem saturated_subset_image (ι : X ↪ V) (D : Finset (Sym2 X)) (q : ℕ) (hq : 0<q) :
    satSet q (liftEdges ι D) ⊆ (univ : Finset X).map ι := by
  intro v hv
  have hDegree := mem_satSet.mp hv
  by_contra hNot
  have hNotRange : ¬ ∃ x, ι x=v := by
    rintro ⟨x,rfl⟩
    exact hNot (mem_map.mpr ⟨x,mem_univ _,rfl⟩)
  rw [degree_zero_outside_image ι D v hNotRange] at hDegree
  omega

theorem pull_vertices_card (ι : X ↪ V) (Z : Finset V)
    (hZ : Z ⊆ (univ : Finset X).map ι) : (pullVertices ι Z).card=Z.card := by
  apply card_bij (fun x _ => ι x)
  · intro x hx
    exact mem_preimage.mp hx
  · intro x _ y _ hxy
    exact ι.injective hxy
  · intro v hv
    obtain ⟨x,_,rfl⟩ := mem_map.mp (hZ hv)
    exact ⟨x,mem_preimage.mpr hv,rfl⟩

theorem pull_vertices_card_le (ι : X ↪ V) (Z : Finset V) :
    (pullVertices ι Z).card ≤ Z.card := by
  rw [pullVertices, card_preimage]
  exact card_filter_le _ _

theorem liftSetting_chainBound (ι : X ↪ V) (S : MacroSetting X Q C) (L : ℕ)
    (hBound : ChainBound S L) : ChainBound (liftSetting ι S) L := by
  intro n Z hMono hSmall
  have hMonoPull : Monotone (fun i => pullVertices ι (Z i)) := by
    intro i j hij x hx
    exact mem_preimage.mpr (hMono hij (mem_preimage.mp hx))
  exact hBound n (fun i => pullVertices ι (Z i)) hMonoPull
    (fun i hi => (pull_vertices_card_le ι (Z i)).trans (hSmall i hi))

theorem liftSetting_basalInherit (ι : X ↪ V) (S : MacroSetting X Q C)
    (h : BasalInherit S) : BasalInherit (liftSetting ι S) := by
  refine ⟨⟨∅,by simp [liftEdges],h.1⟩, ?_⟩
  intro E F hDis hE hF
  obtain ⟨D,rfl,hD⟩ := hE
  obtain ⟨G,rfl,hG⟩ := hF
  have hDG : Disjoint D G := by
    rw [disjoint_left]
    intro f hfD hfG
    exact disjoint_left.mp hDis (mem_map.mpr ⟨f,hfD,rfl⟩) (mem_map.mpr ⟨f,hfG,rfl⟩)
  exact ⟨D∪G,(map_union D G).symm,h.2 D G hDG hD hG⟩

private theorem history_used_is_lift (ι : X ↪ V) {P : ℕ}
    (es : List (RichBank.Entry V C P))
    (h : ∀ e ∈ es, ∃ D : Finset (Sym2 X), e.cell.tot=liftEdges ι D) :
    ∃ D : Finset (Sym2 X), RichBank.usedEdges es=liftEdges ι D := by
  induction es with
  | nil => exact ⟨∅,by simp [RichBank.usedEdges,liftEdges]⟩
  | cons e es ih =>
    obtain ⟨D,hD⟩ := h e (by simp)
    obtain ⟨G,hG⟩ := ih (fun f hf => h f (List.mem_cons_of_mem _ hf))
    refine ⟨D∪G, ?_⟩
    change e.cell.tot∪RichBank.usedEdges es=liftEdges ι (D∪G)
    rw [hD,hG]
    exact (map_union D G).symm

/-- The lifted basal predicate itself supplies the image invariant for every
actual history; it is not an extra premise on the final host. -/
theorem valid_history_saturated_subset_image {I : Type*} (ι : X ↪ V) (S : MacroSetting X Q C)
    {H : Host V I} {F : Set (Multiset I)} {Ub : ℕ} {pay : ℝ}
    {es : List (RichBank.Entry V C S.P)}
    (h : RichBank.ValidHistory H F (liftSetting ι S) Ub pay es) (hq : 0<S.q) :
    satSet S.q (RichBank.usedEdges es) ⊆ (univ : Finset X).map ι := by
  have hImage : ∀ e ∈ es, ∃ D : Finset (Sym2 X), e.cell.tot=liftEdges ι D := by
    intro e he
    obtain ⟨D,hD,_⟩ := (h.good e he).good.2.2.1
    exact ⟨D,hD⟩
  obtain ⟨D,hD⟩ := history_used_is_lift ι es hImage
  rw [hD]
  exact saturated_subset_image ι D S.q hq

theorem valid_history_saturated_pull_card {I : Type*} (ι : X ↪ V) (S : MacroSetting X Q C)
    {H : Host V I} {F : Set (Multiset I)} {Ub : ℕ} {pay : ℝ}
    {es : List (RichBank.Entry V C S.P)}
    (h : RichBank.ValidHistory H F (liftSetting ι S) Ub pay es) (hq : 0<S.q) :
    (pullVertices ι (satSet S.q (RichBank.usedEdges es))).card =
      (satSet S.q (RichBank.usedEdges es)).card :=
  pull_vertices_card ι _ (valid_history_saturated_subset_image ι S h hq)

/-- The local order, not the ambient order, pays positivity of saturation. -/
theorem local_floor_threshold_pos (rate : ℝ) (nX : ℕ) (hRate : 0<rate)
    (hn : ⌈1/rate⌉₊ ≤ nX) : 0 < ⌊rate*nX⌋₊ := by
  have hRatio : 1/rate ≤ (nX:ℝ) :=
    (Nat.le_ceil _).trans (by exact_mod_cast hn)
  have hProduct : (1:ℝ) ≤ rate*nX := by
    simpa only [mul_comm] using (div_le_iff₀ hRate).mp hRatio
  have hh : 1 ≤ ⌊rate*nX⌋₊ := Nat.le_floor (by simpa only [Nat.cast_one] using hProduct)
  omega

end TypedTriangle.Pasch.AmbientBank
#print axioms TypedTriangle.Pasch.AmbientBank.goodCell_lift
#print axioms TypedTriangle.Pasch.AmbientBank.pull_degree_le
#print axioms TypedTriangle.Pasch.AmbientBank.saturated_subset_image
#print axioms TypedTriangle.Pasch.AmbientBank.pull_vertices_card
#print axioms TypedTriangle.Pasch.AmbientBank.liftSetting_chainBound
#print axioms TypedTriangle.Pasch.AmbientBank.liftSetting_basalInherit
#print axioms TypedTriangle.Pasch.AmbientBank.valid_history_saturated_subset_image
#print axioms TypedTriangle.Pasch.AmbientBank.valid_history_saturated_pull_card
#print axioms TypedTriangle.Pasch.AmbientBank.local_floor_threshold_pos
