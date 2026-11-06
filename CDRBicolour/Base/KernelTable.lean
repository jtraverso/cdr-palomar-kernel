module

public import CDRBicolour.Base.Table

/-! Natural-number tables for kernel-reduced finite certificates.
The entries are data, not assumptions. Every witness proves all table laws.
-/

@[expose] public section
namespace CDRBicolour.Base

/-- A data-only search tree, with thresholds stored in the certificate. -/
inductive LookupTree (α : Type) where
  | leaf : α → LookupTree α
  | branch : Nat → LookupTree α → LookupTree α → LookupTree α

def LookupTree.get {α : Type} : LookupTree α → Nat → α
  | .leaf value, _ => value
  | .branch pivot left right, index =>
    if index < pivot then left.get index else right.get index

def natTable (rows : Array (Array Nat)) (n : Nat) (hn : 0 < n)
    (x y : Fin n) : Fin n :=
  ⟨((rows[x.val]?.getD #[])[y.val]?.getD 0) % n, Nat.mod_lt _ hn⟩

/-- One row of the table laws, so reduction caches can be released between rows. -/
def rowValid (a b c : Nat) (rows : Array (Array Nat)) (hn : 0 < a+b+c)
    (x : Fin (a+b+c)) : Prop :=
  ∀ y, x ≠ y →
    natTable rows (a+b+c) hn x y ≠ x ∧
    natTable rows (a+b+c) hn x y ≠ y ∧
    natTable rows (a+b+c) hn y x = natTable rows (a+b+c) hn x y ∧
    natTable rows (a+b+c) hn x (natTable rows (a+b+c) hn x y) = y ∧
    Prefix.col3 a b c x + Prefix.col3 a b c y +
      Prefix.col3 a b c (natTable rows (a+b+c) hn x y) ≠ 0

/-- A lookup function represented by balanced comparisons on natural numbers. -/
def functionTable (lookup : Nat → Nat → Nat) (n : Nat) (hn : 0 < n)
    (x y : Fin n) : Fin n :=
  ⟨lookup x.val y.val % n, Nat.mod_lt _ hn⟩

def functionRowValid (a b c : Nat) (lookup : Nat → Nat → Nat) (hn : 0 < a+b+c)
    (x : Fin (a+b+c)) : Prop :=
  ∀ y, x ≠ y →
    functionTable lookup (a+b+c) hn x y ≠ x ∧
    functionTable lookup (a+b+c) hn x y ≠ y ∧
    functionTable lookup (a+b+c) hn y x = functionTable lookup (a+b+c) hn x y ∧
    functionTable lookup (a+b+c) hn x (functionTable lookup (a+b+c) hn x y) = y ∧
    Prefix.col3 a b c x + Prefix.col3 a b c y +
      Prefix.col3 a b c (functionTable lookup (a+b+c) hn x y) ≠ 0

def colorNat (a b x : Nat) : Nat :=
  if x < a then 0 else if x < a+b then 1 else 2

/-- A first-order Boolean check; the bound is checked before using an entry as a vertex. -/
def entryCheck (a b c : Nat) (lookup : Nat → Nat → Nat) (x y : Nat) : Bool :=
  x == y ||
    (decide (lookup x y < a+b+c) &&
    lookup x y != x && lookup x y != y &&
    lookup y x == lookup x y && lookup x (lookup x y) == y &&
    (colorNat a b x + colorNat a b y + colorNat a b (lookup x y)) % 3 != 0)

def rowCheck (a b c : Nat) (lookup : Nat → Nat → Nat) (x : Nat) : Bool :=
  (List.range (a+b+c)).all (entryCheck a b c lookup x)

/-- Assemble consecutive row proofs without enumerating dependent Fin goals. -/
theorem bounded_zero {P : Nat → Prop} : ∀ x, x < 0 → P x := by
  intro x hx
  exact (Nat.not_lt_zero x hx).elim

theorem bounded_step {P : Nat → Prop} (n : Nat)
    (previous : ∀ x, x < n → P x) (last : P n) : ∀ x, x < n+1 → P x := by
  intro x hx
  by_cases h : x < n
  · exact previous x h
  · have heq : x = n := by omega
    subst x
    exact last

/-- Boolean row certificates imply exactly the table laws required above. -/
theorem realises_of_row_checks (a b c : Nat) (lookup : Nat → Nat → Nat)
    (hn : 0 < a+b+c)
    (h : ∀ x : Fin (a+b+c), rowCheck a b c lookup x.val = true) : Realises a b c := by
  apply realises_of_table a b c (functionTable lookup (a+b+c) hn)
  intro x y hxy
  have hh := List.all_eq_true.1 (h x) y.val (List.mem_range.2 y.isLt)
  simp only [entryCheck, Bool.or_eq_true, beq_iff_eq, Bool.and_eq_true,
    decide_eq_true_eq, bne_iff_ne] at hh
  rcases hh with heq | ⟨⟨⟨⟨⟨hz, hzx⟩, hzy⟩, hsym⟩, hinv⟩, hcol⟩
  · exact (hxy (Fin.ext heq)).elim
  have hv : (functionTable lookup (a+b+c) hn x y).val = lookup x.val y.val := by
    simp only [functionTable, Nat.mod_eq_of_lt hz]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro heq; exact hzx (hv.symm.trans (congrArg Fin.val heq))
  · intro heq; exact hzy (hv.symm.trans (congrArg Fin.val heq))
  · apply Fin.ext
    simp only [functionTable, hsym]
  · apply Fin.ext
    change lookup x.val (functionTable lookup (a+b+c) hn x y).val % (a+b+c) = y.val
    rw [hv, hinv, Nat.mod_eq_of_lt y.isLt]
  · have hcval : ∀ v : Fin (a+b+c), (Prefix.col3 a b c v).val = colorNat a b v.val := by
      intro v
      unfold Prefix.col3 colorNat
      split_ifs <;> rfl
    intro heq
    have he := congrArg Fin.val heq
    simp only [Fin.val_add, Fin.val_zero, hcval, hv] at he
    apply hcol
    simpa only [Nat.add_mod, Nat.mod_mod] using he

end CDRBicolour.Base
