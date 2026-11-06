/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import RequestProject.TypedTriangle.Monitor
set_option maxHeartbeats 4000000 -- build option (original: -DmaxHeartbeats=1600000; raised)
set_option maxRecDepth 16384 -- build option (original: -DmaxRecDepth=8192; raised)

@[expose] public section

/-!
# Cover-down con consumo sublineal (S15 §3, desigualdad (3.1); paso (L18) de P07)

Sea `U` un grafo residual de grado `≤ d` y `X` una reserva disjunta. Cada arista `e ∈ U`
tiene un conjunto `Cand e` de centros legales `w` (el triángulo `e + w` es permitido y sus
dos alas están en `X`). Si `|U|/q + 2d + 4q < |Cand e|` para cada `e` (escrito sin
divisiones: `|U| + q(2d + 4q) < q |Cand e|`), entonces existe un packing que cubre cada
arista de `U` exactamente una vez, con alas en `X`, y cuyo grafo de aristas tiene grado
`≤ 2d + 2q` (`cover_down`). Con `q = ⌈√(nd)⌉` y oferta `βn` se obtiene (3.1)–(3.2) de S15.

La demostración es el algoritmo voraz del texto: se procesan las aristas de `U` una a una,
prohibiendo usar más de `q` veces un vértice como centro (`exists_center_choice`).
-/

open Finset

noncomputable section
open Classical

namespace TypedTriangle

variable {V I : Type*} [Fintype V]

/-! ## Elección voraz de centros (combinatoria pura) -/

/-- Centros que producirían un ala ya usada por alguna arista de `S`. -/
def badWing (S : Finset (Sym2 V)) (c : Sym2 V → V) (e : Sym2 V) : Finset V :=
  univ.filter fun w => ∃ e' ∈ S, ∃ x y, x ∈ e ∧ y ∈ e' ∧ s(x, w) = s(y, c e')

/-- Centros saturados: ya usados `q` veces. -/
def saturated (S : Finset (Sym2 V)) (c : Sym2 V → V) (q : ℕ) : Finset V :=
  univ.filter fun w => q ≤ (S.filter (c · = w)).card

lemma badWing_subset (S : Finset (Sym2 V)) (c : Sym2 V → V) (e : Sym2 V) :
    badWing S c e ⊆ e.toFinset.biUnion (fun x => (S.filter (x ∈ ·)).image c ∪
        (S.filter (c · = x)).biUnion Sym2.toFinset) := by
  intro w hw
  simp only [badWing, Finset.mem_filter, Finset.mem_univ, true_and] at hw
  obtain ⟨e', he', x, y, hx, hy, h⟩ := hw
  rw [Finset.mem_biUnion]
  refine ⟨x, Sym2.mem_toFinset.2 hx, ?_⟩
  rw [Sym2.eq_iff] at h
  rcases h with ⟨rfl, rfl⟩ | ⟨h1, rfl⟩
  · exact Finset.mem_union_left _ (Finset.mem_image.2 ⟨e', Finset.mem_filter.2 ⟨he', hy⟩, rfl⟩)
  · refine Finset.mem_union_right _ (Finset.mem_biUnion.2 ⟨e', ?_, Sym2.mem_toFinset.2 hy⟩)
    exact Finset.mem_filter.2 ⟨he', h1.symm⟩

lemma card_badWing_le {U S : Finset (Sym2 V)} (hSU : S ⊆ U) (c : Sym2 V → V) {d q : ℕ}
    (hdeg : ∀ x, (U.filter (x ∈ ·)).card ≤ d) (hsat : ∀ w, (S.filter (c · = w)).card ≤ q)
    (e : Sym2 V) : (badWing S c e).card ≤ 2 * (d + 2 * q) := by
  refine (Finset.card_le_card (badWing_subset S c e)).trans ?_
  refine (Finset.card_biUnion_le).trans ?_
  have hx : ∀ x ∈ e.toFinset, ((S.filter (x ∈ ·)).image c ∪
      (S.filter (c · = x)).biUnion Sym2.toFinset).card ≤ d + 2 * q := by
    intro x _
    refine (Finset.card_union_le _ _).trans (add_le_add ?_ ?_)
    · refine Finset.card_image_le.trans ((Finset.card_le_card ?_).trans (hdeg x))
      exact Finset.filter_subset_filter _ hSU
    · refine Finset.card_biUnion_le.trans ?_
      calc ∑ e' ∈ S.filter (c · = x), (Sym2.toFinset e').card
          ≤ ∑ _e' ∈ S.filter (c · = x), 2 := by
            refine Finset.sum_le_sum fun e' _ => ?_
            rw [Sym2.card_toFinset]; split_ifs <;> omega
        _ = 2 * (S.filter (c · = x)).card := by rw [Finset.sum_const, smul_eq_mul, mul_comm]
        _ ≤ 2 * q := Nat.mul_le_mul_left 2 (hsat x)
  calc ∑ x ∈ e.toFinset, _ ≤ ∑ _x ∈ e.toFinset, (d + 2 * q) := Finset.sum_le_sum hx
    _ = e.toFinset.card * (d + 2 * q) := by rw [Finset.sum_const, smul_eq_mul]
    _ ≤ 2 * (d + 2 * q) := by
        apply Nat.mul_le_mul_right
        rw [Sym2.card_toFinset]; split_ifs <;> omega

lemma card_saturated_mul_le (S : Finset (Sym2 V)) (c : Sym2 V → V) (q : ℕ) :
    q * (saturated S c q).card ≤ S.card := by
  have hS : S.card = ∑ w ∈ (univ : Finset V), (S.filter (c · = w)).card :=
    Finset.card_eq_sum_card_fiberwise (fun _ _ => Finset.mem_univ _)
  rw [hS]
  calc q * (saturated S c q).card = ∑ _w ∈ saturated S c q, q := by
        rw [Finset.sum_const, smul_eq_mul, mul_comm]
    _ ≤ ∑ w ∈ saturated S c q, (S.filter (c · = w)).card := by
        refine Finset.sum_le_sum fun w hw => ?_
        simpa [saturated] using hw
    _ ≤ ∑ w ∈ (univ : Finset V), (S.filter (c · = w)).card :=
        Finset.sum_le_sum_of_subset (Finset.subset_univ _)

/-- **Elección voraz de centros.** Bajo la condición de oferta, existe una elección de
centros legales `c e ∈ Cand e`, cada vértice usado como centro a lo sumo `q` veces, y
cuyas alas `s(x, c e)` (`x ∈ e`) son distintas para aristas distintas. -/
theorem exists_center_choice (U : Finset (Sym2 V)) (Cand : Sym2 V → Finset V) {d q : ℕ}
    (hdeg : ∀ x, (U.filter (x ∈ ·)).card ≤ d)
    (hcand : ∀ e ∈ U, U.card + q * (2 * (d + 2 * q)) < q * (Cand e).card) :
    ∃ c : Sym2 V → V, (∀ e ∈ U, c e ∈ Cand e) ∧ (∀ w, (U.filter (c · = w)).card ≤ q) ∧
      ∀ e ∈ U, ∀ e' ∈ U, ∀ x y, x ∈ e → y ∈ e' → s(x, c e) = s(y, c e') → e = e' := by
  suffices key : ∀ S ⊆ U, ∃ c : Sym2 V → V, (∀ e ∈ S, c e ∈ Cand e) ∧
      (∀ w, (S.filter (c · = w)).card ≤ q) ∧
      ∀ e ∈ S, ∀ e' ∈ S, ∀ x y, x ∈ e → y ∈ e' → s(x, c e) = s(y, c e') → e = e' from
    key U (subset_refl _)
  intro S
  induction S using Finset.induction_on with
  | empty =>
    intro _
    exact ⟨fun e => (Quot.out e).1, by simp, by simp, by simp⟩
  | insert e S he ih =>
    intro hsub
    have heU : e ∈ U := hsub (Finset.mem_insert_self e S)
    have hSU : S ⊆ U := (Finset.subset_insert e S).trans hsub
    obtain ⟨c, hc1, hc2, hc3⟩ := ih hSU
    -- existencia de un centro bueno
    have hcard : (saturated S c q ∪ badWing S c e).card < (Cand e).card := by
      have h1 := card_saturated_mul_le S c q
      have h2 := card_badWing_le hSU c hdeg hc2 e
      have h3 : S.card ≤ U.card := Finset.card_le_card hSU
      have h4 := hcand e heU
      have h5 := Finset.card_union_le (saturated S c q) (badWing S c e)
      by_contra hcon
      push_neg at hcon
      have : q * (Cand e).card ≤ q * (saturated S c q).card + q * (badWing S c e).card := by
        rw [← mul_add]; exact Nat.mul_le_mul_left q (hcon.trans h5)
      have : q * (badWing S c e).card ≤ q * (2 * (d + 2 * q)) := Nat.mul_le_mul_left q h2
      omega
    obtain ⟨w, hwC, hwbad⟩ : ∃ w ∈ Cand e, w ∉ saturated S c q ∪ badWing S c e := by
      by_contra hcon
      push_neg at hcon
      exact absurd (Finset.card_le_card hcon) (not_le.2 hcard)
    simp only [Finset.mem_union, not_or] at hwbad
    obtain ⟨hwsat, hwwing⟩ := hwbad
    have hwsat' : (S.filter (c · = w)).card < q := by
      simpa [saturated] using hwsat
    have hwwing' : ∀ e' ∈ S, ∀ x y, x ∈ e → y ∈ e' → s(x, w) ≠ s(y, c e') := by
      intro e' he' x y hx hy h
      exact hwwing (by simp only [badWing, Finset.mem_filter, Finset.mem_univ, true_and];
                       exact ⟨e', he', x, y, hx, hy, h⟩)
    let c' := Function.update c e w
    have hc'e : c' e = w := Function.update_self e w c
    have hc'S : ∀ e' ∈ S, c' e' = c e' := fun e' he' =>
      Function.update_of_ne (by rintro rfl; exact he he') w c
    have hfilt : ∀ w', S.filter (c' · = w') = S.filter (c · = w') := fun w' =>
      Finset.filter_congr fun e' he' => by rw [hc'S e' he']
    refine ⟨c', ?_, ?_, ?_⟩
    · intro e' he'
      rcases Finset.mem_insert.1 he' with rfl | he'
      · rw [hc'e]; exact hwC
      · rw [hc'S e' he']; exact hc1 e' he'
    · intro w'
      rw [Finset.filter_insert]
      by_cases hw' : c' e = w'
      · rw [if_pos hw', Finset.card_insert_of_notMem (fun h => he (Finset.mem_filter.1 h).1),
          hfilt]
        rw [hc'e] at hw'; subst hw'; omega
      · rw [if_neg hw', hfilt]; exact hc2 w'
    · intro e₁ he₁ e₂ he₂ x y hx hy h
      rcases Finset.mem_insert.1 he₁ with h1 | h1
      · rcases Finset.mem_insert.1 he₂ with h2 | h2
        · rw [h1, h2]
        · subst h1
          rw [hc'e, hc'S e₂ h2] at h; exact absurd h (hwwing' e₂ h2 x y hx hy)
      · rcases Finset.mem_insert.1 he₂ with h2 | h2
        · subst h2
          rw [hc'e, hc'S e₁ h1] at h; exact absurd h.symm (hwwing' e₁ h1 y x hy hx)
        · rw [hc'S e₁ h1, hc'S e₂ h2] at h; exact hc3 e₁ h1 e₂ h2 x y hx hy h

/-! ## El packing de cover-down -/

omit [Fintype V] in
lemma mem_triEdges_insert {e f : Sym2 V} {w : V} (he : ¬ e.IsDiag) (hw : w ∉ e) :
    f ∈ triEdges (insert w e.toFinset) ↔ f = e ∨ ∃ x ∈ e, f = s(x, w) := by
  induction e using Sym2.ind with
  | _ a b =>
  induction f using Sym2.ind with
  | _ x y =>
  simp only [Sym2.mk_isDiag_iff] at he
  simp only [Sym2.mem_iff, not_or] at hw
  rw [mem_triEdges]
  simp only [Finset.mem_insert, Sym2.mem_toFinset, Sym2.mem_iff, Sym2.eq_iff,
    exists_eq_or_imp, exists_eq_left]
  constructor
  · rintro ⟨hx, hy, hxy⟩
    rcases hx with rfl | rfl | rfl <;> rcases hy with rfl | rfl | rfl <;> tauto
  · rintro ((⟨rfl, rfl⟩ | ⟨rfl, rfl⟩) | (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩) | (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)) <;>
      exact ⟨by tauto, by tauto, by tauto⟩

omit [Fintype V] in
lemma mem_triEdges_insert_self {e : Sym2 V} {w : V} (he : ¬ e.IsDiag) (hw : w ∉ e) :
    e ∈ triEdges (insert w e.toFinset) :=
  (mem_triEdges_insert he hw).2 (Or.inl rfl)

/-- **Cover-down (S15 §3).** Bajo la condición de oferta, existe un packing `C` de
triángulos permitidos que cubre todas las aristas de `U` (cada una exactamente una vez, por
ser un packing), cuyas otras aristas están en la reserva `X`, y con
`d_{E(C)}(v) ≤ 2d + 2q` para todo vértice `v`. -/
theorem cover_down (H : Host V I) (F : Set (Multiset I)) (U X : Finset (Sym2 V))
    (hUX : Disjoint U X) (hU : ∀ e ∈ U, ¬ e.IsDiag) (Cand : Sym2 V → Finset V)
    (hCand : ∀ e ∈ U, ∀ w ∈ Cand e,
      w ∉ e ∧ IsAllowed H F (insert w e.toFinset) ∧ ∀ x ∈ e, s(x, w) ∈ X)
    {d q : ℕ} (hdeg : ∀ x, (U.filter (x ∈ ·)).card ≤ d)
    (hcand : ∀ e ∈ U, U.card + q * (2 * (d + 2 * q)) < q * (Cand e).card) :
    ∃ C : Finset (Finset V), IsPacking H F C ∧ U ⊆ C.biUnion triEdges ∧
      C.biUnion triEdges ⊆ U ∪ X ∧
      ∀ v, ((C.biUnion triEdges).filter (v ∈ ·)).card ≤ 2 * d + 2 * q := by
  obtain ⟨c, hc1, hc2, hc3⟩ := exists_center_choice U Cand hdeg hcand
  let tri : Sym2 V → Finset V := fun e => insert (c e) e.toFinset
  have hcw : ∀ e ∈ U, c e ∉ e := fun e he => (hCand e he (c e) (hc1 e he)).1
  have hmem : ∀ e ∈ U, ∀ f, f ∈ triEdges (tri e) ↔ f = e ∨ ∃ x ∈ e, f = s(x, c e) :=
    fun e he f => mem_triEdges_insert (hU e he) (hcw e he)
  have hwingX : ∀ e ∈ U, ∀ x ∈ e, s(x, c e) ∈ X :=
    fun e he => (hCand e he (c e) (hc1 e he)).2.2
  have hcommon : ∀ e ∈ U, ∀ e' ∈ U, ∀ f, f ∈ triEdges (tri e) → f ∈ triEdges (tri e') →
      e = e' := by
    intro e he e' he' f hf hf'
    rw [hmem e he] at hf
    rw [hmem e' he'] at hf'
    rcases hf with rfl | ⟨x, hx, rfl⟩ <;> rcases hf' with h' | ⟨y, hy, h'⟩
    · exact h'
    · exact absurd (h' ▸ hwingX e' he' y hy) (Finset.disjoint_left.1 hUX he)
    · exact absurd (h' ▸ he') (Finset.disjoint_left.1 hUX |> fun h => fun h2 =>
        h h2 (hwingX e he x hx))
    · exact hc3 e he e' he' x y hx hy h'
  refine ⟨U.image tri, ⟨?_, ?_⟩, ?_, ?_, ?_⟩
  · intro T hT
    obtain ⟨e, he, rfl⟩ := Finset.mem_image.1 hT
    exact (hCand e he (c e) (hc1 e he)).2.1
  · intro T hT T' hT' hne
    obtain ⟨e, he, rfl⟩ := Finset.mem_image.1 (Finset.mem_coe.1 hT)
    obtain ⟨e', he', rfl⟩ := Finset.mem_image.1 (Finset.mem_coe.1 hT')
    rw [Function.onFun, Finset.disjoint_left]
    intro f hf hf'
    exact hne (by rw [hcommon e he e' he' f hf hf'])
  · intro e he
    exact Finset.mem_biUnion.2 ⟨tri e, Finset.mem_image_of_mem _ he,
      mem_triEdges_insert_self (hU e he) (hcw e he)⟩
  · intro f hf
    obtain ⟨T, hT, hfT⟩ := Finset.mem_biUnion.1 hf
    obtain ⟨e, he, rfl⟩ := Finset.mem_image.1 hT
    rcases (hmem e he f).1 hfT with rfl | ⟨x, hx, rfl⟩
    · exact Finset.mem_union_left _ he
    · exact Finset.mem_union_right _ (hwingX e he x hx)
  · intro v
    have hsub : ((U.image tri).biUnion triEdges).filter (v ∈ ·) ⊆
        U.filter (v ∈ ·) ∪ (U.filter (v ∈ ·)).image (fun e => s(v, c e)) ∪
          (U.filter (c · = v)).biUnion (fun e => e.toFinset.image (fun x => s(x, c e))) := by
      intro f hf
      obtain ⟨hf, hvf⟩ := Finset.mem_filter.1 hf
      obtain ⟨T, hT, hfT⟩ := Finset.mem_biUnion.1 hf
      obtain ⟨e, he, rfl⟩ := Finset.mem_image.1 hT
      rcases (hmem e he f).1 hfT with rfl | ⟨x, hx, rfl⟩
      · exact Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_filter.2 ⟨he, hvf⟩))
      · rw [Sym2.mem_iff] at hvf
        rcases hvf with rfl | hv
        · exact Finset.mem_union_left _ (Finset.mem_union_right _
            (Finset.mem_image.2 ⟨e, Finset.mem_filter.2 ⟨he, hx⟩, rfl⟩))
        · exact Finset.mem_union_right _ (Finset.mem_biUnion.2 ⟨e,
            Finset.mem_filter.2 ⟨he, hv.symm⟩,
            Finset.mem_image.2 ⟨x, Sym2.mem_toFinset.2 hx, rfl⟩⟩)
    refine (Finset.card_le_card hsub).trans ?_
    refine (Finset.card_union_le _ _).trans ?_
    have h1 := hdeg v
    have h2 : ((U.filter (v ∈ ·)).image (fun e => s(v, c e))).card ≤ d :=
      Finset.card_image_le.trans h1
    have h3 : ((U.filter (c · = v)).biUnion
        (fun e => e.toFinset.image (fun x => s(x, c e)))).card ≤ 2 * q := by
      refine Finset.card_biUnion_le.trans ?_
      calc ∑ e ∈ U.filter (c · = v), (e.toFinset.image (fun x => s(x, c e))).card
          ≤ ∑ _e ∈ U.filter (c · = v), 2 := by
            refine Finset.sum_le_sum fun e _ => Finset.card_image_le.trans ?_
            rw [Sym2.card_toFinset]; split_ifs <;> omega
        _ = 2 * (U.filter (c · = v)).card := by rw [Finset.sum_const, smul_eq_mul, mul_comm]
        _ ≤ 2 * q := Nat.mul_le_mul_left 2 (hc2 v)
    have := Finset.card_union_le (U.filter (v ∈ ·))
      ((U.filter (v ∈ ·)).image (fun e => s(v, c e)))
    omega

end TypedTriangle
