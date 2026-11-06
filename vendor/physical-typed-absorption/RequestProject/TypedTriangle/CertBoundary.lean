/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import RequestProject.TypedTriangle.CertKernel
set_option maxHeartbeats 4000000 -- build option (original: -DmaxHeartbeats=1600000; raised)
set_option maxRecDepth 16384 -- build option (original: -DmaxRecDepth=8192; raised)

@[expose] public section

/-!
# P06 — Borde del núcleo de certificados de dos niveles

* `badQ_inter`: un triángulo del primer modo que toca `B` contiene exactamente UNA arista
  borrada, y está en la cuña `W_a` (la bisagra evita `B` y `uv`);
* `bdry_Rfun`: `∂R_T = 1_T − ∂p_{uv} − ⟨Σ_{Q retirado} 1_Q⟩`;
* `bdry_RQ`: para un triángulo retirado `Q`, `∂R_Q = 1_Q − Σ_{f ∈ E(Q) ∩ B} ∂p_f`;
* `bdry_kcert`: `∂cert_T = 1_T − Σ_{f ∈ B} 1_{E(T)}(f) ∂p_f` para TODO triángulo permitido,
  con 0, 1, 2 o 3 aristas en `B` (incluido `T ∈ Q`).
-/

open Finset

noncomputable section
open Classical

namespace TypedTriangle

variable {V I : Type*} [Fintype V]

omit [Fintype V] in
lemma tri_eq_insert_toFinset (u v b : V) :
    ({u, v, b} : Finset V) = insert b (s(u, v)).toFinset := by
  ext x; simp only [mem_insert, mem_singleton, Sym2.mem_toFinset, Sym2.mem_iff]; tauto

/-- Borde del pivote global. -/
lemma bdry_pivK {H : Host V I} {F : Set (Multiset I)} {B : Finset (Sym2 V)} {K : KData V}
    (hK : KHyp H F B K) {f : Sym2 V} (hf : f ∈ B) (e : Sym2 V) :
    bdry H F (pivK K f) e =
      avgOver (K.Piv f) (fun b => indR (triEdges (insert b f.toFinset)) e) := by
  rw [show pivK K f = fun S => avgOver (K.Piv f)
      (fun b => (fun b S => if S = insert b f.toFinset then (1 : ℝ) else 0) b S) from rfl,
    bdry_avgOver]
  exact avgOver_congr fun b hb => bdry_delta (hK.piv_ok f hf b hb).1 e

omit [Fintype V] in
/-- `Σ_{f ∈ B} 1_{E(T)}(f) g f = Σ_{f ∈ E(T) ∩ B} g f`. -/
lemma pivotTermW_eq {H : Host V I} {F : Set (Multiset I)} [Fintype V] (B : Finset (Sym2 V))
    (p : Sym2 V → Finset V → ℝ) (T : Finset V) (e : Sym2 V) :
    pivotTermW H F B p T e = ∑ f ∈ (triEdges T).filter (· ∈ B), bdry H F (p f) e := by
  unfold pivotTermW indR
  simp only [ite_mul, one_mul, zero_mul]
  rw [← sum_filter]
  congr 1; ext f; simp [and_comm]

/-! ### Triángulos retirados -/

section badQ

variable {H : Host V I} {F : Set (Multiset I)} {B : Finset (Sym2 V)} {u v a c : V}
  {J : Finset (Sym2 V)}

lemma badQ_subset : badQ H F B u v a c J ⊆ hdec1 H F u v a c J := filter_subset _ _

/-- Las aristas borradas de un triángulo del primer modo están en `W_a`, y no puede haber dos. -/
lemma badQ_edges {Q : Finset V} (hJ : IsHinge H F u v a c J) (hJB : Disjoint J B)
    (hTa : IsAllowed H F {u, v, a}) (hQ : Q ∈ hdec1 H F u v a c J) :
    (triEdges Q).filter (· ∈ B) ⊆ wedge u v a ∧ ((triEdges Q).filter (· ∈ B)).card ≤ 1 := by
  obtain ⟨huv, hua, hva⟩ := distinct_of_card_three hTa.1
  have hD := hdec1_spec hJ
  have hsub := hD.subset hQ
  have h1 : (triEdges Q).filter (· ∈ B) ⊆ wedge u v a := by
    intro f hf
    rw [mem_filter] at hf
    rcases mem_union.1 (hsub hf.1) with h | h
    · exact absurd hf.2 (disjoint_left.1 hJB h)
    · exact h
  refine ⟨h1, ?_⟩
  by_contra hc
  push_neg at hc
  have hW : (wedge u v a).card ≤ 2 := card_le_two
  have heq : (triEdges Q).filter (· ∈ B) = wedge u v a :=
    eq_of_subset_of_card_le h1 (by omega)
  have hua' : s(u, a) ∈ triEdges Q := by
    have : s(u, a) ∈ (triEdges Q).filter (· ∈ B) := by rw [heq]; simp [wedge]
    exact (mem_filter.1 this).1
  have hva' : s(v, a) ∈ triEdges Q := by
    have : s(v, a) ∈ (triEdges Q).filter (· ∈ B) := by rw [heq]; simp [wedge]
    exact (mem_filter.1 this).1
  rw [mem_triEdges] at hua' hva'
  have huvQ : s(u, v) ∈ triEdges Q := mem_triEdges.2 ⟨hua'.1, hva'.1, huv⟩
  rcases mem_union.1 (hsub huvQ) with h | h
  · exact disjoint_left.1 hJ.2.1 h (mem_union_left _ (mem_triEdges.2 (by simp [huv])))
  · exact not_mem_wedge huv hua hva h

/-- Un triángulo retirado contiene exactamente una arista borrada, situada en `W_a`. -/
lemma badQ_inter {Q : Finset V} (hJ : IsHinge H F u v a c J) (hJB : Disjoint J B)
    (hTa : IsAllowed H F {u, v, a}) (hQ : Q ∈ badQ H F B u v a c J) :
    ∃ f, (triEdges Q).filter (· ∈ B) = {f} ∧ f ∈ wedge u v a := by
  obtain ⟨hQ1, hQ2⟩ := mem_filter.1 hQ
  obtain ⟨h1, h2⟩ := badQ_edges hJ hJB hTa hQ1
  obtain ⟨f, hf⟩ : ((triEdges Q).filter (· ∈ B)).Nonempty := by
    rw [not_disjoint_iff] at hQ2
    obtain ⟨f, hfQ, hfB⟩ := hQ2
    exact ⟨f, mem_filter.2 ⟨hfQ, hfB⟩⟩
  refine ⟨f, ?_, h1 hf⟩
  exact eq_singleton_iff_unique_mem.2 ⟨hf, fun g hg => card_le_one.1 h2 g hg f hf⟩

end badQ

omit [Fintype V] in
/-- Un triángulo permitido con una arista en `B` tiene un dato de toque con esa arista. -/
lemma isTouch_of_mem {H : Host V I} {F : Set (Multiset I)} {B : Finset (Sym2 V)}
    {Q : Finset V} (hQ : IsAllowed H F Q) {f : Sym2 V} (hfQ : f ∈ triEdges Q) (hfB : f ∈ B) :
    ∃ x, IsTouch B Q x ∧ s(x.1, x.2.1) = f := by
  obtain ⟨w, hw⟩ := eq_insert_of_mem_triEdges hQ.1 hfQ
  induction f using Sym2.ind with
  | _ p q =>
    have hQeq : Q = {p, q, w} := by
      rw [hw]; ext x; simp only [mem_insert, mem_singleton, Sym2.mem_toFinset, Sym2.mem_iff]
      tauto
    have h3 := hQ.1
    rw [hQeq] at h3
    obtain ⟨hpq, hpw, hqw⟩ := distinct_of_card_three h3
    exact ⟨(p, q, w), ⟨hQeq, hpq, hpw, hqw, hfB⟩, rfl⟩

omit [Fintype V] in
/-- Aristas de un triángulo con dato de toque. -/
lemma triEdges_touch {B : Finset (Sym2 V)} {T : Finset V} {x : V × V × V}
    (hx : IsTouch B T x) :
    triEdges T = insert s(x.1, x.2.1) (wedge x.1 x.2.1 x.2.2) ∧
      s(x.1, x.2.1) ∉ wedge x.1 x.2.1 x.2.2 := by
  obtain ⟨hT, h1, h2, h3, -⟩ := hx
  rw [hT]
  exact ⟨triEdges_eq_insert_wedge h1 h2 h3, not_mem_wedge h1 h2 h3⟩

/-! ### Borde de `Rfun` -/

section bdryR

variable {H : Host V I} {F : Set (Multiset I)} {B : Finset (Sym2 V)} {K : KData V}

lemma bdry_hcQ {u v a c : V} {J : Finset (Sym2 V)} (hJ : IsHinge H F u v a c J)
    (hTa : IsAllowed H F {u, v, a}) (hTc : IsAllowed H F {u, v, c}) (e : Sym2 V) :
    bdry H F (hcQ H F B u v a c J) e =
      indR (triEdges ({u, v, a} : Finset V)) e - indR (triEdges ({u, v, c} : Finset V)) e -
        ∑ Q ∈ badQ H F B u v a c J, indR (triEdges Q) e := by
  unfold hcQ
  rw [bdry_sub', bdry_hingeCert hJ hTa hTc]
  congr 1
  exact bdry_indSet (fun Q hQ => (hdec1_spec hJ).1 Q (badQ_subset hQ)) e

/-- **Borde del certificado de dos niveles.** -/
theorem bdry_Rfun (hK : KHyp H F B K) {u v a : V} (huvB : s(u, v) ∈ B)
    (hTa : IsAllowed H F {u, v, a}) (e : Sym2 V) :
    bdry H F (Rfun H F B K u v a) e =
      indR (triEdges ({u, v, a} : Finset V)) e - bdry H F (pivK K s(u, v)) e -
        avgOver (K.Piv s(u, v)) (fun b => avgOver (K.Cs u v a b) fun c =>
          avgOver (K.fam u v a c) fun J =>
            ∑ Q ∈ badQ H F B u v a c J, indR (triEdges Q) e) := by
  rw [bdry_pivK hK huvB]
  have step : ∀ b ∈ K.Piv s(u, v), bdry H F (fun S => avgOver (K.Cs u v a b) fun c =>
      avgOver (K.fam u v a c) (fun J => hcQ H F B u v a c J S) +
        avgOver (K.fam u v c b) (fun J => hingeCert H F u v c b J S)) e =
      indR (triEdges ({u, v, a} : Finset V)) e -
        indR (triEdges (insert b (s(u, v)).toFinset)) e -
        avgOver (K.Cs u v a b) (fun c => avgOver (K.fam u v a c) fun J =>
          ∑ Q ∈ badQ H F B u v a c J, indR (triEdges Q) e) := by
    intro b hb
    rw [bdry_avgOver (K.Cs u v a b) (fun c S => avgOver (K.fam u v a c)
      (fun J => hcQ H F B u v a c J S) + avgOver (K.fam u v c b)
        (fun J => hingeCert H F u v c b J S)) e]
    rw [← avgOver_const (hK.cs_ne u v a huvB hTa b hb)
      (indR (triEdges ({u, v, a} : Finset V)) e - indR (triEdges (insert b (s(u, v)).toFinset)) e),
      ← avgOver_sub]
    refine avgOver_congr fun c hc => ?_
    obtain ⟨hTc, hca, hcb, -, -⟩ := hK.cs_ok u v a huvB hTa b hb c hc
    have hTb : IsAllowed H F {u, v, b} := by
      rw [tri_eq_insert_toFinset]; exact (hK.piv_ok _ huvB b hb).1
    rw [bdry_add' (fun S => avgOver (K.fam u v a c) (fun J => hcQ H F B u v a c J S))
      (fun S => avgOver (K.fam u v c b) (fun J => hingeCert H F u v c b J S)) e,
      bdry_avgOver (K.fam u v a c) (fun J S => hcQ H F B u v a c J S) e,
      bdry_avgOver (K.fam u v c b) (fun J S => hingeCert H F u v c b J S) e]
    rw [avgOver_congr (fun J hJ => bdry_hcQ (hK.fam1_ok u v a huvB hTa b hb c hc J hJ).1
      hTa hTc e)]
    rw [avgOver_congr (fun J hJ => bdry_hingeCert (hK.fam2_ok u v a huvB hTa b hb c hc J hJ).1
      hTc hTb e)]
    rw [avgOver_sub, avgOver_sub, avgOver_const (hK.fam1_ne u v a huvB hTa b hb c hc),
      avgOver_const (hK.fam1_ne u v a huvB hTa b hb c hc),
      avgOver_const (hK.fam2_ne u v a huvB hTa b hb c hc), ← tri_eq_insert_toFinset]
    ring
  rw [show Rfun H F B K u v a = fun S => avgOver (K.Piv s(u, v)) (fun b =>
      (fun b S => avgOver (K.Cs u v a b) fun c =>
        avgOver (K.fam u v a c) (fun J => hcQ H F B u v a c J S) +
          avgOver (K.fam u v c b) (fun J => hingeCert H F u v c b J S)) b S) from rfl,
    bdry_avgOver, avgOver_congr step, avgOver_sub, avgOver_sub,
    avgOver_const (hK.piv_ne _ huvB)]

end bdryR

/-! ### Borde de la corrección y del certificado final -/

section bdryK

variable {H : Host V I} {F : Set (Multiset I)} {B : Finset (Sym2 V)} {K : KData V}

/-- Si la cuña evita `B`, el primer modo no tiene triángulos retirados. -/
lemma badQ_eq_empty {u v a c : V} {J : Finset (Sym2 V)} (hJ : IsHinge H F u v a c J)
    (hJB : Disjoint J B) (hTa : IsAllowed H F {u, v, a}) (hW : Disjoint (wedge u v a) B) :
    badQ H F B u v a c J = ∅ := by
  rw [eq_empty_iff_forall_notMem]
  intro Q hQ
  obtain ⟨f, hf, hfW⟩ := badQ_inter hJ hJB hTa hQ
  have : f ∈ (triEdges Q).filter (· ∈ B) := by rw [hf]; exact mem_singleton_self f
  exact disjoint_left.1 hW hfW (mem_filter.1 this).2

lemma RQ_eq {Q : Finset V} (h : ∃ x, IsTouch B Q x) :
    RQ H F B K Q = Rfun H F B K (Classical.choose h).1 (Classical.choose h).2.1
      (Classical.choose h).2.2 := by
  funext S; unfold RQ; rw [dif_pos h]

/-- **Borde del certificado de una arista** de un triángulo con exactamente una arista en
`B`: `∂R_Q = 1_Q − Σ_{f ∈ E(Q) ∩ B} ∂p_f`. -/
theorem bdry_RQ (hK : KHyp H F B K) {Q : Finset V} (hQ : IsAllowed H F Q)
    (hsingle : ((triEdges Q).filter (· ∈ B)).card = 1) (e : Sym2 V) :
    bdry H F (RQ H F B K Q) e = indR (triEdges Q) e -
      ∑ f ∈ (triEdges Q).filter (· ∈ B), bdry H F (pivK K f) e := by
  obtain ⟨f, hf⟩ := card_eq_one.1 hsingle
  have hfm : f ∈ (triEdges Q).filter (· ∈ B) := by rw [hf]; exact mem_singleton_self f
  obtain ⟨x0, hx0, -⟩ := isTouch_of_mem hQ (mem_filter.1 hfm).1 (mem_filter.1 hfm).2
  have h : ∃ x, IsTouch B Q x := ⟨x0, hx0⟩
  rw [RQ_eq h]
  set x := Classical.choose h
  have hx : IsTouch B Q x := Classical.choose_spec h
  obtain ⟨hTe, hnw⟩ := triEdges_touch hx
  have hTa : IsAllowed H F {x.1, x.2.1, x.2.2} := hx.1 ▸ hQ
  have huvB : s(x.1, x.2.1) ∈ B := hx.2.2.2.2
  have huvf : s(x.1, x.2.1) = f := by
    have : s(x.1, x.2.1) ∈ (triEdges Q).filter (· ∈ B) :=
      mem_filter.2 ⟨by rw [hTe]; exact mem_insert_self _ _, huvB⟩
    rw [hf] at this; exact mem_singleton.1 this
  have hW : Disjoint (wedge x.1 x.2.1 x.2.2) B := by
    rw [disjoint_left]
    intro g hg hgB
    have : g ∈ (triEdges Q).filter (· ∈ B) :=
      mem_filter.2 ⟨by rw [hTe]; exact mem_insert_of_mem hg, hgB⟩
    rw [hf] at this
    rw [mem_singleton] at this
    exact hnw (huvf ▸ this ▸ hg)
  rw [bdry_Rfun hK huvB hTa e, hf, sum_singleton, ← huvf, ← hx.1]
  have hz : avgOver (K.Piv s(x.1, x.2.1)) (fun b => avgOver (K.Cs x.1 x.2.1 x.2.2 b) fun c =>
      avgOver (K.fam x.1 x.2.1 x.2.2 c) fun J =>
        ∑ Q ∈ badQ H F B x.1 x.2.1 x.2.2 c J, indR (triEdges Q) e) = 0 := by
    refine avgOver_eq_zero fun b hb => avgOver_eq_zero fun c hc => avgOver_eq_zero fun J hJ => ?_
    obtain ⟨hJh, hJB⟩ := hK.fam1_ok _ _ _ huvB hTa b hb c hc J hJ
    rw [badQ_eq_empty hJh hJB hTa hW, sum_empty]
  rw [hz, sub_zero]

/-- Doble cuenta: las aristas borradas de los triángulos retirados son exactamente las de
`W_a ∩ B`. -/
lemma sum_badQ_edges {u v a c : V} {J : Finset (Sym2 V)} (hJ : IsHinge H F u v a c J)
    (hJB : Disjoint J B) (g : Sym2 V → ℝ) :
    ∑ Q ∈ badQ H F B u v a c J, ∑ f ∈ (triEdges Q).filter (· ∈ B), g f =
      ∑ f ∈ (wedge u v a).filter (· ∈ B), g f := by
  have hD := hdec1_spec hJ
  have h1 : ∑ Q ∈ badQ H F B u v a c J, ∑ f ∈ (triEdges Q).filter (· ∈ B), g f =
      ∑ Q ∈ hdec1 H F u v a c J, ∑ f ∈ (triEdges Q).filter (· ∈ B), g f := by
    refine sum_subset badQ_subset fun Q hQ hQn => ?_
    have hdis : Disjoint (triEdges Q) B := by
      by_contra hc; exact hQn (mem_filter.2 ⟨hQ, hc⟩)
    rw [show (triEdges Q).filter (· ∈ B) = ∅ from
      filter_eq_empty_iff.2 fun f hf hfB => disjoint_left.1 hdis hf hfB, sum_empty]
  rw [h1, ← sum_biUnion]
  · congr 1
    ext f
    simp only [mem_biUnion, mem_filter]
    constructor
    · rintro ⟨Q, hQ, hfQ, hfB⟩
      refine ⟨?_, hfB⟩
      rcases mem_union.1 (hD.subset hQ hfQ) with h | h
      · exact absurd hfB (disjoint_left.1 hJB h)
      · exact h
    · rintro ⟨hfW, hfB⟩
      obtain ⟨Q, hQ, hfQ⟩ := hD.exists_mem (mem_union_right _ hfW)
      exact ⟨Q, hQ, hfQ, hfB⟩
  · intro Q hQ Q' hQ' hne
    exact disjoint_filter_filter (hD.2.1 hQ hQ' hne)

/-- **Ecuación de borde del certificado final (P06, identidad para 0–3 aristas borradas).**
Para todo triángulo permitido `T`, `∂cert_T = 1_{E(T)} − Σ_{f∈B} 1_{E(T)}(f) ∂p_f` con los
pivotes GLOBALES `p_f = pivK K f`. -/
theorem bdry_kcert (hK : KHyp H F B K) {T : Finset V} (hT : IsAllowed H F T) (e : Sym2 V) :
    bdry H F (kcert H F B K T) e = indR (triEdges T) e - pivotTermW H F B (pivK K) T e := by
  rw [pivotTermW_eq]
  by_cases h : ∃ x, IsTouch B T x
  · set x := Classical.choose h
    have hx : IsTouch B T x := Classical.choose_spec h
    obtain ⟨hTe, hnw⟩ := triEdges_touch hx
    have hTa : IsAllowed H F {x.1, x.2.1, x.2.2} := hx.1 ▸ hT
    have huvB : s(x.1, x.2.1) ∈ B := hx.2.2.2.2
    have hkc : kcert H F B K T = fun S => Rfun H F B K x.1 x.2.1 x.2.2 S +
        corrK H F B K x.1 x.2.1 x.2.2 S := by
      funext S; unfold kcert; rw [dif_pos h]
    rw [hkc, bdry_add' _ _ e, bdry_Rfun hK huvB hTa e, ← hx.1]
    -- borde de la corrección
    have hcorr : bdry H F (corrK H F B K x.1 x.2.1 x.2.2) e =
        avgOver (K.Piv s(x.1, x.2.1)) (fun b => avgOver (K.Cs x.1 x.2.1 x.2.2 b) fun c =>
          avgOver (K.fam x.1 x.2.1 x.2.2 c) fun J =>
            ∑ Q ∈ badQ H F B x.1 x.2.1 x.2.2 c J, indR (triEdges Q) e) -
        ∑ f ∈ (wedge x.1 x.2.1 x.2.2).filter (· ∈ B), bdry H F (pivK K f) e := by
      rw [show corrK H F B K x.1 x.2.1 x.2.2 = fun S => avgOver (K.Piv s(x.1, x.2.1)) (fun b =>
          (fun b S => avgOver (K.Cs x.1 x.2.1 x.2.2 b) fun c =>
            avgOver (K.fam x.1 x.2.1 x.2.2 c) fun J =>
              ∑ Q ∈ badQ H F B x.1 x.2.1 x.2.2 c J, RQ H F B K Q S) b S) from rfl,
        bdry_avgOver]
      rw [← avgOver_const (hK.piv_ne _ huvB)
        (∑ f ∈ (wedge x.1 x.2.1 x.2.2).filter (· ∈ B), bdry H F (pivK K f) e), ← avgOver_sub]
      refine avgOver_congr fun b hb => ?_
      rw [bdry_avgOver (K.Cs x.1 x.2.1 x.2.2 b) (fun c S => avgOver (K.fam x.1 x.2.1 x.2.2 c)
        fun J => ∑ Q ∈ badQ H F B x.1 x.2.1 x.2.2 c J, RQ H F B K Q S) e]
      rw [← avgOver_const (hK.cs_ne _ _ _ huvB hTa b hb)
        (∑ f ∈ (wedge x.1 x.2.1 x.2.2).filter (· ∈ B), bdry H F (pivK K f) e), ← avgOver_sub]
      refine avgOver_congr fun c hc => ?_
      rw [bdry_avgOver (K.fam x.1 x.2.1 x.2.2 c) (fun J S =>
        ∑ Q ∈ badQ H F B x.1 x.2.1 x.2.2 c J, RQ H F B K Q S) e]
      rw [← avgOver_const (hK.fam1_ne _ _ _ huvB hTa b hb c hc)
        (∑ f ∈ (wedge x.1 x.2.1 x.2.2).filter (· ∈ B), bdry H F (pivK K f) e), ← avgOver_sub]
      refine avgOver_congr fun J hJ => ?_
      obtain ⟨hJh, hJB⟩ := hK.fam1_ok _ _ _ huvB hTa b hb c hc J hJ
      rw [bdry_finsum, ← sum_badQ_edges hJh hJB, ← sum_sub_distrib]
      refine sum_congr rfl fun Q hQ => ?_
      have hQA : IsAllowed H F Q := (hdec1_spec hJh).1 Q (badQ_subset hQ)
      obtain ⟨f, hf, -⟩ := badQ_inter hJh hJB hTa hQ
      exact bdry_RQ hK hQA (by rw [hf, card_singleton]) e
    rw [hcorr]
    have hsplit : (triEdges T).filter (· ∈ B) =
        insert s(x.1, x.2.1) ((wedge x.1 x.2.1 x.2.2).filter (· ∈ B)) := by
      rw [hTe, filter_insert, if_pos huvB]
    rw [hsplit, sum_insert (fun hm => hnw (mem_filter.1 hm).1)]
    ring
  · have hdis : (triEdges T).filter (· ∈ B) = ∅ := by
      rw [filter_eq_empty_iff]
      intro f hf hfB
      obtain ⟨x, hx, -⟩ := isTouch_of_mem hT hf hfB
      exact h ⟨x, hx⟩
    have hkc : kcert H F B K T = fun S => if S = T then 1 else 0 := by
      funext S; unfold kcert; rw [dif_neg h]
    rw [hkc, bdry_delta hT, hdis, sum_empty, sub_zero]

end bdryK

end TypedTriangle
