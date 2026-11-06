/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import RequestProject.TypedTriangle.CertSupport
set_option maxHeartbeats 4000000 -- build option (original: -DmaxHeartbeats=1600000; raised)
set_option maxRecDepth 16384 -- build option (original: -DmaxRecDepth=8192; raised)

@[expose] public section

/-!
# P06 — Dispersión del núcleo de dos niveles

Con `pw n S X = (1/n)^{|S ∖ X|}`:

* `avg_pw_insert`: promediar un vértice nuevo `c` sobre un conjunto de tamaño `≥ n/κ`
  cuesta un factor `1 + 3κ` (para `|S| ≤ 3`);
* `avg_cover`: la fracción de bisagras de una familia abundante (`≥ β n^{i−4}`) que cubren
  `S` es `≤ (2^{C(h,2)}/β) (1/n)^{|S ∖ raíces|}`;
* `Rfun_disp`: `|R_T(S)| ≤ L₁ (1/n)^{|S ∖ T|}`;
* `corrK_disp`: la corrección (≤ 2 triángulos retirados, terceros vértices en la bisagra)
  cuesta un factor `2 (1 + 3κ + 3M/β)`;
* `kcert_disp`: `|cert_T(S)| ≤ L (1/n)^{3 − |S ∩ T|}` para todo `S`, con
  `L = L₁ (1 + 2 (1 + 3κ + 3M/β))`, `L₁ = (M/β)((1+3κ) + (1+3κ)²)`, `M = 2^{C(h,2)}`.

Las cuentas usan sólo la linealidad del promedio (sin independencia entre fuentes).
-/

open Finset

noncomputable section
open Classical

namespace TypedTriangle

variable {V I : Type*} [Fintype V]

/-- Peso de dispersión `(1/n)^{|S ∖ X|}`. -/
def pw (n : ℝ) (S X : Finset V) : ℝ := (1 / n) ^ (S \ X).card

omit [Fintype V] in
lemma pw_nonneg {n : ℝ} (hn : 0 ≤ n) (S X : Finset V) : 0 ≤ pw n S X := by
  unfold pw; positivity

omit [Fintype V] in
lemma pw_mono {n : ℝ} (hn : 1 ≤ n) {S X Y : Finset V} (h : X ⊆ Y) : pw n S X ≤ pw n S Y := by
  unfold pw
  have h1 : 1 / n ≤ 1 := by rw [div_le_one (by linarith)]; exact hn
  exact pow_le_pow_of_le_one (by positivity) h1 (card_le_card (sdiff_subset_sdiff (subset_refl _) h))

omit [Fintype V] in
lemma pw_insert_le {n : ℝ} (hn : 1 ≤ n) (S X : Finset V) (c : V) :
    pw n S (insert c X) ≤ pw n S X * (1 + n * (if c ∈ S then 1 else 0)) := by
  have hp := pw_nonneg (by linarith : (0 : ℝ) ≤ n) S X
  by_cases hc : c ∈ S ∧ c ∉ X
  · have hcS : c ∈ S \ X := mem_sdiff.2 hc
    have heq : S \ insert c X = (S \ X).erase c := by
      ext x; simp only [mem_sdiff, mem_insert, mem_erase]; tauto
    have hk : (S \ insert c X).card + 1 = (S \ X).card := by
      rw [heq, card_erase_of_mem hcS]
      have : 0 < (S \ X).card := card_pos.2 ⟨c, hcS⟩
      omega
    have hval : pw n S (insert c X) = pw n S X * n := by
      unfold pw; rw [← hk, pow_succ]; field_simp
    rw [hval, if_pos hc.1]; nlinarith
  · have heq : S \ insert c X = S \ X := by
      ext x; simp only [mem_sdiff, mem_insert]
      constructor
      · rintro ⟨h1, h2⟩; exact ⟨h1, fun h => h2 (Or.inr h)⟩
      · rintro ⟨h1, h2⟩
        refine ⟨h1, fun h => h.elim (fun h' => ?_) h2⟩
        subst h'; exact hc ⟨h1, h2⟩
    have : pw n S (insert c X) = pw n S X := by unfold pw; rw [heq]
    rw [this]
    have : 0 ≤ n * (if c ∈ S then (1 : ℝ) else 0) := by split_ifs <;> nlinarith
    nlinarith

omit [Fintype V] in
/-- **Promedio sobre un vértice nuevo.** -/
lemma avg_pw_insert {n κ : ℝ} (hn : 1 ≤ n) {P : Finset V} (hP : P.Nonempty)
    (hPk : n ≤ κ * P.card) {S : Finset V} (hS : S.card ≤ 3) (X : Finset V) :
    avgOver P (fun c => pw n S (insert c X)) ≤ (1 + 3 * κ) * pw n S X := by
  have hp := pw_nonneg (by linarith : (0 : ℝ) ≤ n) S X
  have hP0 : (0 : ℝ) < P.card := by exact_mod_cast card_pos.2 hP
  refine (avgOver_le fun c _ => pw_insert_le hn S X c).trans ?_
  rw [avgOver_const_mul, avgOver_add, avgOver_const hP, avgOver_const_mul, avgOver_ite]
  have hcnt : ((P.filter (· ∈ S)).card : ℝ) ≤ 3 := by
    have := card_le_card (show P.filter (· ∈ S) ⊆ S from fun x hx => (mem_filter.1 hx).2)
    exact_mod_cast this.trans hS
  have h1 : n * (((P.filter (· ∈ S)).card : ℝ) / P.card) ≤ 3 * κ := by
    rw [mul_div_assoc', div_le_iff₀ hP0]
    have hn0 : 0 ≤ n := by linarith
    nlinarith
  nlinarith

/-- **Fracción de bisagras que cubren `S`.** -/
lemma avg_cover {H : Host V I} {F : Set (Multiset I)} {u v a b : V} {i hh : ℕ} {β : ℝ}
    (hβ : 0 < β) (hab : a ≠ b) (hTa : IsAllowed H F {u, v, a}) (hTb : IsAllowed H F {u, v, b})
    {fam : Finset (Finset (Sym2 V))} (hfam : fam ⊆ hinges H F u v a b i)
    (hsize : β * (Fintype.card V : ℝ) ^ (i - 4) ≤ fam.card) (hi : i ≤ hh)
    (hn : 1 ≤ (Fintype.card V : ℝ)) (S : Finset V) :
    avgOver fam (fun J => if S ⊆ support J ∪ {u, v, a, b} then 1 else 0) ≤
      2 ^ Nat.choose hh 2 / β * pw (Fintype.card V) S {u, v, a, b} := by
  set n := (Fintype.card V : ℝ)
  have hfpos : 0 < (fam.card : ℝ) := lt_of_lt_of_le (by positivity) hsize
  rw [avgOver_ite]
  have hc := hinges_cover_count hab hTa hTb i S hn
  have hsub : fam.filter (fun J => S ⊆ support J ∪ {u, v, a, b}) ⊆
      (hinges H F u v a b i).filter (fun J => S ⊆ support J ∪ {u, v, a, b}) :=
    filter_subset_filter _ hfam
  have hc' : ((fam.filter (fun J => S ⊆ support J ∪ {u, v, a, b})).card : ℝ) ≤
      2 ^ Nat.choose i 2 * n ^ (i - 4) * (1 / n) ^ (S \ {u, v, a, b}).card :=
    le_trans (by exact_mod_cast card_le_card hsub) hc
  have hM : (2 : ℝ) ^ Nat.choose i 2 ≤ 2 ^ Nat.choose hh 2 :=
    pow_le_pow_right₀ (by norm_num) (Nat.choose_le_choose 2 hi)
  rw [div_le_iff₀ hfpos]
  unfold pw
  have hq : 0 ≤ (1 / n) ^ (S \ {u, v, a, b}).card := by positivity
  calc _ ≤ 2 ^ Nat.choose i 2 * n ^ (i - 4) * (1 / n) ^ (S \ {u, v, a, b}).card := hc'
    _ ≤ 2 ^ Nat.choose hh 2 * n ^ (i - 4) * (1 / n) ^ (S \ {u, v, a, b}).card := by gcongr
    _ = 2 ^ Nat.choose hh 2 / β * (1 / n) ^ (S \ {u, v, a, b}).card * (β * n ^ (i - 4)) := by
        field_simp
    _ ≤ 2 ^ Nat.choose hh 2 / β * (1 / n) ^ (S \ {u, v, a, b}).card * fam.card := by
        gcongr

lemma abs_avgOver_le_of {α : Type*} {s : Finset α} {g k : α → ℝ} (h : ∀ x ∈ s, |g x| ≤ k x) :
    |avgOver s g| ≤ avgOver s k :=
  (abs_avgOver_le s g).trans (avgOver_le h)

lemma avgOver_finsum {α β : Type*} (s : Finset α) (t : Finset β) (g : α → β → ℝ) :
    avgOver s (fun x => ∑ y ∈ t, g x y) = ∑ y ∈ t, avgOver s (fun x => g x y) := by
  unfold avgOver; simp_rw [mul_sum]; rw [sum_comm]

section disp

variable {H : Host V I} {F : Set (Multiset I)} {B : Finset (Sym2 V)} {K : KData V}

/-- Hipótesis cuantitativas (tamaños y órdenes) para la dispersión. -/
structure KDisp (H : Host V I) (F : Set (Multiset I)) (B : Finset (Sym2 V)) (K : KData V)
    (hh : ℕ) (β κ : ℝ) : Prop where
  piv_size : ∀ f ∈ B, (Fintype.card V : ℝ) ≤ κ * (K.Piv f).card
  cs_size : ∀ u v a, s(u, v) ∈ B → IsAllowed H F {u, v, a} → ∀ b ∈ K.Piv s(u, v),
    (Fintype.card V : ℝ) ≤ κ * (K.Cs u v a b).card
  fam1_ord : ∀ u v a, s(u, v) ∈ B → IsAllowed H F {u, v, a} → ∀ b ∈ K.Piv s(u, v),
    ∀ c ∈ K.Cs u v a b, ∃ i ≤ hh, K.fam u v a c ⊆ hinges H F u v a c i ∧
      β * (Fintype.card V : ℝ) ^ (i - 4) ≤ (K.fam u v a c).card
  fam2_ord : ∀ u v a, s(u, v) ∈ B → IsAllowed H F {u, v, a} → ∀ b ∈ K.Piv s(u, v),
    ∀ c ∈ K.Cs u v a b, ∃ i ≤ hh, K.fam u v c b ⊆ hinges H F u v c b i ∧
      β * (Fintype.card V : ℝ) ^ (i - 4) ≤ (K.fam u v c b).card

lemma abs_hcQ_le {u v a c : V} {J : Finset (Sym2 V)} (hJ : IsHinge H F u v a c J)
    (S : Finset V) :
    |hcQ H F B u v a c J S| ≤ if S ⊆ support J ∪ {u, v, a, c} then 1 else 0 := by
  by_cases h0 : hcQ H F B u v a c J S = 0
  · rw [h0, abs_zero]; split_ifs <;> norm_num
  · have hsub : S ⊆ support J ∪ {u, v, a, c} := by
      rcases hcQ_ne_zero h0 with ⟨h, -⟩ | h
      · refine (subset_support_of_mem_dec (hdec1_spec hJ) h).trans ?_
        intro x hx; simp only [mem_union, mem_insert, mem_singleton] at hx ⊢; tauto
      · refine (subset_support_of_mem_dec (hdec2_spec hJ) h).trans ?_
        intro x hx; simp only [mem_union, mem_insert, mem_singleton] at hx ⊢; tauto
    rw [if_pos hsub]
    unfold hcQ hingeCert
    by_cases hb : S ∈ badQ H F B u v a c J
    · have h1 : S ∈ hdec1 H F u v a c J := badQ_subset hb
      rw [if_pos h1, if_pos hb]; split_ifs <;> norm_num
    · rw [if_neg hb]; split_ifs <;> norm_num

omit [Fintype V] in
lemma roots_eq_insert (u v a c : V) : ({u, v, a, c} : Finset V) = insert c {u, v, a} := by
  ext x; simp only [mem_insert, mem_singleton]; tauto

omit [Fintype V] in
lemma roots2_subset (u v a b c : V) :
    ({u, v, c, b} : Finset V) ⊆ insert c (insert b {u, v, a}) := by
  intro x; simp only [mem_insert, mem_singleton]; tauto

/-- **Dispersión del certificado de dos niveles.** -/
theorem Rfun_disp {hh : ℕ} {β κ : ℝ} (hβ : 0 < β) (hκ : 0 ≤ κ) (hK : KHyp H F B K)
    (hD : KDisp H F B K hh β κ) (hn : 1 ≤ (Fintype.card V : ℝ)) {u v a : V}
    (huvB : s(u, v) ∈ B) (hTa : IsAllowed H F {u, v, a}) {S : Finset V} (hS : S.card = 3) :
    |Rfun H F B K u v a S| ≤ 2 ^ Nat.choose hh 2 / β * ((1 + 3 * κ) + (1 + 3 * κ) ^ 2) *
      pw (Fintype.card V) S {u, v, a} := by
  set n := (Fintype.card V : ℝ)
  set M := (2 : ℝ) ^ Nat.choose hh 2 / β
  have hM : 0 ≤ M := by positivity
  set T : Finset V := {u, v, a}
  have hS3 : S.card ≤ 3 := hS.le
  have hpT := pw_nonneg (by linarith : (0 : ℝ) ≤ n) S T
  unfold Rfun
  refine (abs_avgOver_le_of (k := fun b => avgOver (K.Cs u v a b) fun c =>
    M * pw n S (insert c T) + M * pw n S (insert c (insert b T))) fun b hb => ?_).trans ?_
  · refine abs_avgOver_le_of fun c hc => (abs_add_le _ _).trans (add_le_add ?_ ?_)
    · obtain ⟨i, hi, hsub, hsz⟩ := hD.fam1_ord u v a huvB hTa b hb c hc
      obtain ⟨hTc, hca, -, -, -⟩ := hK.cs_ok u v a huvB hTa b hb c hc
      refine (abs_avgOver_le_of fun J hJ =>
        abs_hcQ_le (hK.fam1_ok u v a huvB hTa b hb c hc J hJ).1 S).trans ?_
      exact (avg_cover hβ hca.symm hTa hTc hsub hsz hi hn S).trans
        (le_of_eq (by rw [roots_eq_insert]))
    · obtain ⟨i, hi, hsub, hsz⟩ := hD.fam2_ord u v a huvB hTa b hb c hc
      obtain ⟨hTc, -, hcb, -, -⟩ := hK.cs_ok u v a huvB hTa b hb c hc
      have hTb : IsAllowed H F {u, v, b} := by
        rw [tri_eq_insert_toFinset]; exact (hK.piv_ok _ huvB b hb).1
      refine (abs_avgOver_le_of fun J hJ =>
        abs_hingeCert_le (hK.fam2_ok u v a huvB hTa b hb c hc J hJ).1 S).trans ?_
      refine (avg_cover hβ hcb hTc hTb hsub hsz hi hn S).trans ?_
      exact mul_le_mul_of_nonneg_left (pw_mono hn (roots2_subset u v a b c)) hM
  · refine (avgOver_le (g := fun b => M * ((1 + 3 * κ) * pw n S T) +
      M * ((1 + 3 * κ) * pw n S (insert b T))) fun b hb => ?_).trans ?_
    · rw [avgOver_add, avgOver_const_mul, avgOver_const_mul]
      have hne := hK.cs_ne u v a huvB hTa b hb
      have hsz := hD.cs_size u v a huvB hTa b hb
      exact add_le_add (mul_le_mul_of_nonneg_left (avg_pw_insert hn hne hsz hS3 T) hM)
        (mul_le_mul_of_nonneg_left (avg_pw_insert hn hne hsz hS3 _) hM)
    · rw [avgOver_add, avgOver_const (hK.piv_ne _ huvB), avgOver_const_mul,
        avgOver_const_mul]
      have h2 := avg_pw_insert hn (hK.piv_ne _ huvB) (hD.piv_size _ huvB) hS3 T
      have h3 : M * ((1 + 3 * κ) * avgOver (K.Piv s(u, v)) fun b => pw n S (insert b T)) ≤
          M * ((1 + 3 * κ) * ((1 + 3 * κ) * pw n S T)) := by gcongr
      nlinarith

/-- Dispersión del certificado de una arista vía su dato de toque. -/
theorem RQ_disp {hh : ℕ} {β κ : ℝ} (hβ : 0 < β) (hκ : 0 ≤ κ) (hK : KHyp H F B K)
    (hD : KDisp H F B K hh β κ) (hn : 1 ≤ (Fintype.card V : ℝ)) {Q : Finset V}
    (hQ : IsAllowed H F Q) {S : Finset V} (hS : S.card = 3) :
    |RQ H F B K Q S| ≤ 2 ^ Nat.choose hh 2 / β * ((1 + 3 * κ) + (1 + 3 * κ) ^ 2) *
      pw (Fintype.card V) S Q := by
  by_cases h : ∃ x, IsTouch B Q x
  · rw [RQ_eq h]
    have hx : IsTouch B Q (Classical.choose h) := Classical.choose_spec h
    have := Rfun_disp hβ hκ hK hD hn hx.2.2.2.2 (hx.1 ▸ hQ) hS
    rwa [← hx.1] at this
  · have h0 : RQ H F B K Q S = 0 := by unfold RQ; rw [dif_neg h]
    rw [h0, abs_zero]
    exact mul_nonneg (by positivity) (pw_nonneg (by linarith) S Q)

end disp

/-! ### Dispersión de la corrección y del certificado final -/

section dispK

variable {H : Host V I} {F : Set (Multiset I)} {B : Finset (Sym2 V)} {K : KData V}

/-- Un triángulo retirado tiene a lo sumo un vértice fuera de `T`, y ese vértice está en la
bisagra. -/
lemma pw_badQ_le {n : ℝ} (hn : 1 ≤ n) {u v a c : V} {J : Finset (Sym2 V)}
    (hJ : IsHinge H F u v a c J) (hJB : Disjoint J B) (hTa : IsAllowed H F {u, v, a})
    {Q : Finset V} (hQ : Q ∈ badQ H F B u v a c J) (S : Finset V) :
    pw n S Q ≤ pw n S {u, v, a} *
      (1 + n * (((S \ {u, v, a}).filter (· ∈ support J)).card : ℝ)) := by
  set T : Finset V := {u, v, a}
  obtain ⟨huv, hua, hva⟩ := distinct_of_card_three hTa.1
  have hQD := badQ_subset hQ
  have hQsub : Q ⊆ support J ∪ T := subset_support_of_mem_dec (hdec1_spec hJ) hQD
  have hQ3 : Q.card = 3 := ((hdec1_spec hJ).1 Q hQD).1
  obtain ⟨f, hf, hfW⟩ := badQ_inter hJ hJB hTa hQ
  have hfQE : f ∈ triEdges Q := by
    have : f ∈ (triEdges Q).filter (· ∈ B) := by rw [hf]; exact mem_singleton_self f
    exact (mem_filter.1 this).1
  have hfQ : f.toFinset ⊆ Q := toFinset_subset_of_mem_triEdges hfQE
  have hfT : f.toFinset ⊆ T :=
    toFinset_subset_of_mem_triEdges (wedge_subset_triEdges huv hua hva hfW)
  have hf2 := Sym2.card_toFinset_of_not_isDiag f (not_isDiag_of_mem_triEdges hfQE)
  have hQT1 : (Q \ T).card ≤ 1 := by
    have h1 : Q \ T ⊆ Q \ f.toFinset := sdiff_subset_sdiff (subset_refl _) hfT
    have h2 : (Q \ f.toFinset).card = 1 := by rw [card_sdiff_of_subset hfQ]; omega
    exact (card_le_card h1).trans h2.le
  have hn0 : (0 : ℝ) < n := by linarith
  have hpT := pw_nonneg hn0.le S T
  have hcnt0 : (0 : ℝ) ≤ (((S \ T).filter (· ∈ support J)).card : ℝ) := by positivity
  have h1n : 1 / n ≤ 1 := by rw [div_le_one hn0]; exact hn
  by_cases hY : ∃ y ∈ Q \ T, y ∈ S
  · obtain ⟨y, hyQ, hyS⟩ := hY
    have hQTy : Q \ T ⊆ {y} := fun x hx => mem_singleton.2 (card_le_one.1 hQT1 x hx y hyQ)
    have hyT : y ∉ T := (mem_sdiff.1 hyQ).2
    have hysupp : y ∈ support J := by
      rcases mem_union.1 (hQsub (mem_sdiff.1 hyQ).1) with h | h
      · exact h
      · exact absurd h hyT
    have hcnt : (1 : ℝ) ≤ (((S \ T).filter (· ∈ support J)).card : ℝ) := by
      have : 0 < ((S \ T).filter (· ∈ support J)).card :=
        card_pos.2 ⟨y, mem_filter.2 ⟨mem_sdiff.2 ⟨hyS, hyT⟩, hysupp⟩⟩
      exact_mod_cast this
    have hcard : (S \ T).card ≤ (S \ Q).card + 1 := by
      have : S \ T ⊆ insert y (S \ Q) := by
        intro x hx
        rw [mem_insert]
        by_cases hxQ : x ∈ Q
        · left; exact mem_singleton.1 (hQTy (mem_sdiff.2 ⟨hxQ, (mem_sdiff.1 hx).2⟩))
        · right; exact mem_sdiff.2 ⟨(mem_sdiff.1 hx).1, hxQ⟩
      exact (card_le_card this).trans (card_insert_le _ _)
    have hle : pw n S Q ≤ n * pw n S T := by
      unfold pw
      have : (1 / n) ^ ((S \ Q).card + 1) ≤ (1 / n) ^ (S \ T).card :=
        pow_le_pow_of_le_one (by positivity) h1n hcard
      rw [pow_succ] at this
      have hq : 0 ≤ (1 / n) ^ (S \ Q).card := by positivity
      calc (1 / n) ^ (S \ Q).card = n * ((1 / n) ^ (S \ Q).card * (1 / n)) := by
            field_simp
        _ ≤ n * (1 / n) ^ (S \ T).card := mul_le_mul_of_nonneg_left this hn0.le
    nlinarith [mul_le_mul_of_nonneg_left hcnt (mul_nonneg hn0.le hpT)]
  · push_neg at hY
    have hsub : S \ T ⊆ S \ Q := by
      intro x hx
      refine mem_sdiff.2 ⟨(mem_sdiff.1 hx).1, fun hxQ => ?_⟩
      exact hY x (mem_sdiff.2 ⟨hxQ, (mem_sdiff.1 hx).2⟩) (mem_sdiff.1 hx).1
    have : pw n S Q ≤ pw n S T := by
      unfold pw; exact pow_le_pow_of_le_one (by positivity) h1n (card_le_card hsub)
    nlinarith [mul_nonneg hpT (mul_nonneg hn0.le hcnt0)]

/-- A lo sumo dos triángulos retirados (uno por arista borrada de `W_a`). -/
lemma card_badQ_le_two {u v a c : V} {J : Finset (Sym2 V)} (hJ : IsHinge H F u v a c J)
    (hJB : Disjoint J B) (hTa : IsAllowed H F {u, v, a}) :
    (badQ H F B u v a c J).card ≤ 2 := by
  have h := sum_badQ_edges (H := H) (F := F) (B := B) hJ hJB (fun _ => (1 : ℝ))
  simp only [sum_const, nsmul_eq_mul, mul_one] at h
  have h1 : ∑ Q ∈ badQ H F B u v a c J, (((triEdges Q).filter (· ∈ B)).card : ℝ) =
      (badQ H F B u v a c J).card := by
    rw [card_eq_sum_ones, Nat.cast_sum]
    refine sum_congr rfl fun Q hQ => ?_
    obtain ⟨f, hf, -⟩ := badQ_inter hJ hJB hTa hQ
    rw [hf, card_singleton]
  rw [h1] at h
  have h' : (badQ H F B u v a c J).card = ((wedge u v a).filter (· ∈ B)).card := by
    exact_mod_cast h
  have h2 : ((wedge u v a).filter (· ∈ B)).card ≤ 2 :=
    (card_le_card (filter_subset _ _)).trans card_le_two
  omega

/-- Promedio del número de vértices de `S ∖ T` que caen en la bisagra. -/
lemma avg_cnt_le {u v a c : V} {i hh : ℕ} {β : ℝ} (hβ : 0 < β) (hac : a ≠ c)
    (hTa : IsAllowed H F {u, v, a}) (hTc : IsAllowed H F {u, v, c})
    {fam : Finset (Finset (Sym2 V))} (hfam : fam ⊆ hinges H F u v a c i)
    (hsize : β * (Fintype.card V : ℝ) ^ (i - 4) ≤ fam.card) (hi : i ≤ hh)
    (hn : 1 ≤ (Fintype.card V : ℝ)) {S : Finset V} (hS : S.card ≤ 3) :
    avgOver fam (fun J => (((S \ {u, v, a}).filter (· ∈ support J)).card : ℝ)) ≤
      (if c ∈ S then 1 else 0) + 3 * (2 ^ Nat.choose hh 2 / β) / Fintype.card V := by
  set n := (Fintype.card V : ℝ)
  set M := (2 : ℝ) ^ Nat.choose hh 2 / β
  set T : Finset V := {u, v, a}
  have hn0 : (0 : ℝ) < n := by linarith
  have hfne : fam.Nonempty := by
    rw [← card_pos]
    have : (0 : ℝ) < fam.card := lt_of_lt_of_le (mul_pos hβ (pow_pos hn0 _)) hsize
    exact_mod_cast this
  have hcard : ∀ J : Finset (Sym2 V), (((S \ T).filter (· ∈ support J)).card : ℝ) =
      ∑ y ∈ S \ T, (if y ∈ support J then (1 : ℝ) else 0) := by
    intro J; rw [sum_boole]
  rw [avgOver_congr (fun J _ => hcard J), avgOver_finsum]
  have hy : ∀ y ∈ S \ T, avgOver fam (fun J => if y ∈ support J then (1 : ℝ) else 0) ≤
      (if y = c then 1 else 0) + M / n := by
    intro y hyST
    have hMn : 0 ≤ M / n := by positivity
    by_cases hyc : y = c
    · rw [if_pos hyc]
      have : avgOver fam (fun J => if y ∈ support J then (1 : ℝ) else 0) ≤ 1 := by
        refine (avgOver_le (g := fun _ => (1 : ℝ)) fun J _ => ?_).trans
          (le_of_eq (avgOver_const hfne 1))
        split_ifs <;> norm_num
      linarith
    · rw [if_neg hyc, zero_add]
      have hyR : y ∉ ({u, v, a, c} : Finset V) := by
        have hyT := (mem_sdiff.1 hyST).2
        simp only [T, mem_insert, mem_singleton] at hyT ⊢
        tauto
      have heq : ∀ J : Finset (Sym2 V), (if y ∈ support J then (1 : ℝ) else 0) =
          if ({y} : Finset V) ⊆ support J ∪ {u, v, a, c} then 1 else 0 := by
        intro J
        congr 1
        apply propext
        rw [singleton_subset_iff, mem_union]
        exact ⟨Or.inl, fun h => h.resolve_right hyR⟩
      rw [avgOver_congr (fun J _ => heq J)]
      refine (avg_cover hβ hac hTa hTc hfam hsize hi hn {y}).trans (le_of_eq ?_)
      unfold pw
      rw [show ({y} : Finset V) \ {u, v, a, c} = {y} from sdiff_eq_self_of_disjoint
        (disjoint_singleton_left.2 hyR), card_singleton, pow_one]
      ring
  refine (sum_le_sum hy).trans ?_
  rw [sum_add_distrib, sum_const, nsmul_eq_mul]
  have h1 : ∑ y ∈ S \ T, (if y = c then (1 : ℝ) else 0) ≤ if c ∈ S then 1 else 0 := by
    rw [sum_ite_eq']
    by_cases hc : c ∈ S \ T
    · rw [if_pos hc, if_pos (mem_sdiff.1 hc).1]
    · rw [if_neg hc]; split_ifs <;> norm_num
  have h2 : ((S \ T).card : ℝ) * (M / n) ≤ 3 * M / n := by
    have : ((S \ T).card : ℝ) ≤ 3 := by
      exact_mod_cast (card_le_card (sdiff_subset (s := S) (t := T))).trans hS
    rw [mul_div_assoc]
    exact mul_le_mul_of_nonneg_right this (by positivity)
  linarith

/-- **Dispersión de la corrección.** -/
theorem corrK_disp {hh : ℕ} {β κ : ℝ} (hβ : 0 < β) (hκ : 0 ≤ κ) (hK : KHyp H F B K)
    (hD : KDisp H F B K hh β κ) (hn : 1 ≤ (Fintype.card V : ℝ)) {u v a : V}
    (huvB : s(u, v) ∈ B) (hTa : IsAllowed H F {u, v, a}) {S : Finset V} (hS : S.card = 3) :
    |corrK H F B K u v a S| ≤ 2 ^ Nat.choose hh 2 / β * ((1 + 3 * κ) + (1 + 3 * κ) ^ 2) *
      (2 * (1 + 3 * κ + 3 * (2 ^ Nat.choose hh 2 / β))) * pw (Fintype.card V) S {u, v, a} := by
  set n := (Fintype.card V : ℝ)
  set M := (2 : ℝ) ^ Nat.choose hh 2 / β
  set L1 := M * ((1 + 3 * κ) + (1 + 3 * κ) ^ 2)
  set T : Finset V := {u, v, a}
  have hn0 : (0 : ℝ) < n := by linarith
  have hM : 0 ≤ M := by positivity
  have hL1 : 0 ≤ L1 := by positivity
  have hpT := pw_nonneg hn0.le S T
  set cnt : Finset (Sym2 V) → ℝ := fun J => (((S \ T).filter (· ∈ support J)).card : ℝ)
  -- cota por bisagra
  have hJb : ∀ b ∈ K.Piv s(u, v), ∀ c ∈ K.Cs u v a b, ∀ J ∈ K.fam u v a c,
      |∑ Q ∈ badQ H F B u v a c J, RQ H F B K Q S| ≤ 2 * L1 * pw n S T * (1 + n * cnt J) := by
    intro b hb c hc J hJ
    obtain ⟨hJh, hJB⟩ := hK.fam1_ok u v a huvB hTa b hb c hc J hJ
    have hc0 : 0 ≤ 1 + n * cnt J := by positivity
    refine (abs_sum_le_sum_abs _ _).trans ?_
    calc ∑ Q ∈ badQ H F B u v a c J, |RQ H F B K Q S|
        ≤ ∑ Q ∈ badQ H F B u v a c J, L1 * (pw n S T * (1 + n * cnt J)) := by
          refine sum_le_sum fun Q hQ => ?_
          have hQA := (hdec1_spec hJh).1 Q (badQ_subset hQ)
          exact (RQ_disp hβ hκ hK hD hn hQA hS).trans
            (mul_le_mul_of_nonneg_left (pw_badQ_le hn hJh hJB hTa hQ S) hL1)
      _ = (badQ H F B u v a c J).card * (L1 * (pw n S T * (1 + n * cnt J))) := by
          rw [sum_const, nsmul_eq_mul]
      _ ≤ 2 * (L1 * (pw n S T * (1 + n * cnt J))) := by
          refine mul_le_mul_of_nonneg_right ?_ (by positivity)
          exact_mod_cast card_badQ_le_two hJh hJB hTa
      _ = 2 * L1 * pw n S T * (1 + n * cnt J) := by ring
  -- promedio sobre bisagras
  have hJavg : ∀ b ∈ K.Piv s(u, v), ∀ c ∈ K.Cs u v a b,
      avgOver (K.fam u v a c) (fun J => 2 * L1 * pw n S T * (1 + n * cnt J)) ≤
        2 * L1 * pw n S T * (1 + 3 * M + n * (if c ∈ S then 1 else 0)) := by
    intro b hb c hc
    obtain ⟨i, hi, hsub, hsz⟩ := hD.fam1_ord u v a huvB hTa b hb c hc
    obtain ⟨hTc, hca, -, -, -⟩ := hK.cs_ok u v a huvB hTa b hb c hc
    have hfne := hK.fam1_ne u v a huvB hTa b hb c hc
    have hcnt := avg_cnt_le hβ hca.symm hTa hTc hsub hsz hi hn hS.le
    rw [avgOver_const_mul, avgOver_add, avgOver_const hfne, avgOver_const_mul]
    have hk : 0 ≤ 2 * L1 * pw n S T := by positivity
    refine mul_le_mul_of_nonneg_left ?_ hk
    have : n * avgOver (K.fam u v a c) cnt ≤
        n * ((if c ∈ S then 1 else 0) + 3 * M / n) := mul_le_mul_of_nonneg_left hcnt hn0.le
    have e : n * ((if c ∈ S then (1 : ℝ) else 0) + 3 * M / n) =
        n * (if c ∈ S then 1 else 0) + 3 * M := by field_simp
    linarith
  -- promedio sobre ápices intermedios
  have hCavg : ∀ b ∈ K.Piv s(u, v),
      avgOver (K.Cs u v a b) (fun c => 2 * L1 * pw n S T *
        (1 + 3 * M + n * (if c ∈ S then 1 else 0))) ≤
        2 * L1 * pw n S T * (1 + 3 * κ + 3 * M) := by
    intro b hb
    have hne := hK.cs_ne u v a huvB hTa b hb
    have hsz := hD.cs_size u v a huvB hTa b hb
    have hP0 : (0 : ℝ) < (K.Cs u v a b).card := by exact_mod_cast card_pos.2 hne
    rw [avgOver_const_mul, avgOver_add, avgOver_const hne, avgOver_const_mul, avgOver_ite]
    have hk : 0 ≤ 2 * L1 * pw n S T := by positivity
    refine mul_le_mul_of_nonneg_left ?_ hk
    have hcntS : (((K.Cs u v a b).filter (· ∈ S)).card : ℝ) ≤ 3 := by
      have := card_le_card (show (K.Cs u v a b).filter (· ∈ S) ⊆ S from
        fun x hx => (mem_filter.1 hx).2)
      exact_mod_cast this.trans hS.le
    have : n * ((((K.Cs u v a b).filter (· ∈ S)).card : ℝ) / (K.Cs u v a b).card) ≤ 3 * κ := by
      rw [mul_div_assoc', div_le_iff₀ hP0]; nlinarith
    linarith
  unfold corrK
  refine (abs_avgOver_le_of (k := fun b => avgOver (K.Cs u v a b) fun c =>
    avgOver (K.fam u v a c) fun J => 2 * L1 * pw n S T * (1 + n * cnt J)) fun b hb =>
      abs_avgOver_le_of fun c hc => abs_avgOver_le_of fun J hJ => hJb b hb c hc J hJ).trans ?_
  refine (avgOver_le (g := fun _ => 2 * L1 * pw n S T * (1 + 3 * κ + 3 * M)) fun b hb =>
    (avgOver_le fun c hc => hJavg b hb c hc).trans (hCavg b hb)).trans ?_
  rw [avgOver_const (hK.piv_ne _ huvB)]
  ring_nf
  exact le_refl _

/-- **Dispersión del certificado final** para `T` que toca `B` y `|S| = 3`. -/
theorem kcert_disp {hh : ℕ} {β κ : ℝ} (hβ : 0 < β) (hκ : 0 ≤ κ) (hK : KHyp H F B K)
    (hD : KDisp H F B K hh β κ) (hn : 1 ≤ (Fintype.card V : ℝ)) {T : Finset V}
    (hT : IsAllowed H F T) (hTB : ¬ Disjoint (triEdges T) B) {S : Finset V} (hS : S.card = 3) :
    |kcert H F B K T S| ≤ 2 ^ Nat.choose hh 2 / β * ((1 + 3 * κ) + (1 + 3 * κ) ^ 2) *
      (1 + 2 * (1 + 3 * κ + 3 * (2 ^ Nat.choose hh 2 / β))) * pw (Fintype.card V) S T := by
  have h : ∃ x, IsTouch B T x := by
    rw [not_disjoint_iff] at hTB
    obtain ⟨f, hfT, hfB⟩ := hTB
    obtain ⟨x, hx, -⟩ := isTouch_of_mem hT hfT hfB
    exact ⟨x, hx⟩
  set x := Classical.choose h
  have hx : IsTouch B T x := Classical.choose_spec h
  have hTa : IsAllowed H F {x.1, x.2.1, x.2.2} := hx.1 ▸ hT
  have huvB : s(x.1, x.2.1) ∈ B := hx.2.2.2.2
  have hkc : kcert H F B K T S = Rfun H F B K x.1 x.2.1 x.2.2 S +
      corrK H F B K x.1 x.2.1 x.2.2 S := by
    unfold kcert; rw [dif_pos h]
  rw [hkc]
  have h1 := Rfun_disp hβ hκ hK hD hn huvB hTa hS
  have h2 := corrK_disp hβ hκ hK hD hn huvB hTa hS
  rw [← hx.1] at h1 h2
  refine (abs_add_le _ _).trans ?_
  linarith

/-- **Hipótesis `hL` de `seed_perturbation_scaled` con `D = 1`.** -/
theorem kcert_hL {hh : ℕ} {β κ : ℝ} (hβ : 0 < β) (hκ : 0 ≤ κ) (hK : KHyp H F B K)
    (hD : KDisp H F B K hh β κ) (hn : 1 ≤ (Fintype.card V : ℝ)) {T : Finset V}
    (hT : IsAllowed H F T) (hTB : ¬ Disjoint (triEdges T) B) (S : Finset V) :
    |kcert H F B K T S| ≤ 2 ^ Nat.choose hh 2 / β * ((1 + 3 * κ) + (1 + 3 * κ) ^ 2) *
      (1 + 2 * (1 + 3 * κ + 3 * (2 ^ Nat.choose hh 2 / β))) *
        ptw S (1 / Fintype.card V) T := by
  by_cases h0 : kcert H F B K T S = 0
  · rw [h0, abs_zero]
    exact mul_nonneg (by positivity) (ptw_nonneg (by positivity) T)
  · have hS3 : S.card = 3 := (kcert_support hK hT h0).1
    have hT3 : T.card = 3 := hT.1
    refine (kcert_disp hβ hκ hK hD hn hT hTB hS3).trans (le_of_eq ?_)
    congr 1
    unfold pw ptw
    congr 1
    have := card_sdiff_add_card_inter S T
    omega

end dispK

end TypedTriangle
