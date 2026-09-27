import SparseDivComplexity.StringArith.Add

/-!
# Truncated binary subtraction and comparisons in Cobham's algebra

`subBits a b` denotes `decNat a - decNat b` (truncated at `0`). From it we derive the comparison
flags `ltBits`, `leBits`, `eqBits` and the zero test `isZeroBits`, all returning the one-bit flags
`[true]`/`[false]` used throughout complexitylib's Cobham toolkit (`Complexity.Cobham.caseBit₀`).

## Implementation

Borrows travel from the least-significant bit upwards, i.e. *against* the direction of recursion
on notation (which peels the least-significant bit and recurses on the higher ones). The
subtractor is therefore a bounded recursion on notation over the *counter* `a ++ b`, of which only
the length matters. After `i` steps the recursive value `subCore a b c` (with `|c| = i`) is the
record `digits ++ [borrow]`: the low `i` digits of `a - b` followed by the borrow into position
`i`. One step reads bit `i` of `a`, of `b` and of the record itself with `Complexity.bitAt` (the
tail of the counter processed so far has length exactly `i`) and appends the new digit and borrow.
The invariant is

`decNat (a.take i) + borrowᵢ · 2^i = decNat (b.take i) + decNat digitsᵢ`,

so at `i = |a ++ b|` the final borrow is set iff `decNat a < decNat b`, and otherwise the digits
denote `decNat a - decNat b`.
-/

open Complexity

namespace SparseDiv.StringArith

/-- Ripple subtraction with borrow (reference definition, not used by the Cobham implementation
below); the result is meaningful when `decNat b ≤ decNat a`. -/
def subBorrow : List Bool → List Bool → Bool → List Bool
  | [], _, _ => []
  | a :: as, [], c => (xor a c) :: subBorrow as [] ((!a) && c)
  | a :: as, b :: bs, c =>
    (xor (xor a b) c) :: subBorrow as bs (((!a) && (b || c)) || (b && c))

/-! ### Decoding lemmas -/

/-- Decoding a concatenation: the second block is weighted by `2 ^ |first block|`. -/
theorem decNat_append_eq_add_mul (x y : List Bool) :
    decNat (x ++ y) = decNat x + 2 ^ x.length * decNat y := by
  induction x with
  | nil => simp
  | cons b x ih =>
    rw [List.cons_append, decNat_cons, decNat_cons, ih, List.length_cons, pow_succ]
    ring

/-- One more bit of a prefix adds the next bit at its weight (`false` past the end). -/
theorem decNat_take_add_one_eq (x : List Bool) (n : ℕ) :
    decNat (x.take (n + 1)) = decNat (x.take n) + 2 ^ n * (x.getD n false).toNat := by
  by_cases h : n < x.length
  · rw [List.take_succ_eq_append_getElem h, decNat_append_eq_add_mul, List.length_take,
      Nat.min_eq_left h.le, List.getD_eq_getElem x false h]
    cases x[n] <;> simp [decNat_cons]
  · have h' : x.length ≤ n := Nat.le_of_not_lt h
    rw [List.take_of_length_le h', List.take_of_length_le (by omega),
      List.getD_eq_default x false h']
    simp

/-- A numeral is zero iff all its bits are `false`. -/
theorem decNat_eq_zero_iff_all_false (x : List Bool) : decNat x = 0 ↔ ∀ b ∈ x, b = false := by
  induction x with
  | nil => simp
  | cons b x ih =>
    rw [decNat_cons]
    cases b <;> simp [ih]

/-! ### Flag lemmas -/

/-- `bitAt r x` is the flag for the bit of `x` at position `|r|` (`false` past the end). -/
theorem bitAt_eq_getD_single (r x : List Bool) : bitAt r x = [x.getD r.length false] := by
  rw [bitAt]
  by_cases h : r.length < x.length
  · rw [List.drop_eq_getElem_cons h, caseBit₀_cons, List.getD_eq_getElem x false h]
    cases x[r.length] <;> rfl
  · have h' : x.length ≤ r.length := Nat.le_of_not_lt h
    rw [List.drop_eq_nil_of_le h', caseBit₀_nil, List.getD_eq_default x false h']

/-- Exclusive-or of two flags. -/
def xorFlag (x y : List Bool) : List Bool := caseBit₀ x (notBit y) (caseBit₀ y [true] [false])

/-- Exclusive-or of flags is in Cobham's algebra. -/
theorem cobham_xorFlag_comp {n : ℕ} {g₀ g₁ : (Fin n → List Bool) → List Bool}
    (h₀ : Cobham g₀) (h₁ : Cobham g₁) :
    Cobham fun v : Fin n → List Bool ↦ xorFlag (g₀ v) (g₁ v) :=
  (Cobham.iteFn h₀ (Cobham.notFn h₁)
    (Cobham.iteFn h₁ (Cobham.const [true]) (Cobham.const [false]))).of_eq fun _ ↦ rfl

/-- Negation of a one-bit flag. -/
@[simp] theorem notBit_single (x : Bool) : notBit [x] = [!x] := by cases x <;> rfl

/-- Conjunction of one-bit flags. -/
@[simp] theorem andBit_single (x y : Bool) : andBit [x] [y] = [x && y] := by
  cases x <;> cases y <;> rfl

/-- Disjunction of one-bit flags. -/
@[simp] theorem orBit_single (x y : Bool) : orBit [x] [y] = [x || y] := by
  cases x <;> cases y <;> rfl

/-- Exclusive-or of one-bit flags. -/
@[simp] theorem xorFlag_single (x y : Bool) : xorFlag [x] [y] = [xor x y] := by
  cases x <;> cases y <;> rfl

/-! ### The borrow recursion -/

/-- Digit of the full subtractor `x - y - z`. -/
def subDigit (x y z : Bool) : Bool := xor x (xor y z)

/-- Borrow of the full subtractor `x - y - z`. -/
def subBorrowBit (x y z : Bool) : Bool := ((!x) && (y || z)) || (y && z)

/-- One step of the subtractor at position `i`: the record `r = digits ++ [borrow]` (of length
`i + 1`) becomes `digits ++ [digit, borrow']` with the full-subtractor digit and borrow at
position `i`. -/
def subStep (a b : List Bool) (i : ℕ) (r : List Bool) : List Bool :=
  r.take i ++ [subDigit (a.getD i false) (b.getD i false) (r.getD i false),
    subBorrowBit (a.getD i false) (b.getD i false) (r.getD i false)]

/-- The subtraction record after `|c|` steps: the low `|c|` digits of `a - b` followed by the
borrow into position `|c|`. -/
def subCore (a b : List Bool) : List Bool → List Bool
  | [] => [false]
  | _ :: c => subStep a b c.length (subCore a b c)

/-- The step of `subCore` written with the Cobham string primitives, on the argument vector
`⟨counter tail, record, a, b⟩` of a recursion on notation. -/
def subStepFn (w : Fin 4 → List Bool) : List Bool :=
  (w 1).take (w 0).length ++
    xorFlag (bitAt (w 0) (w 2)) (xorFlag (bitAt (w 0) (w 3)) (bitAt (w 0) (w 1))) ++
    orBit (andBit (notBit (bitAt (w 0) (w 2))) (orBit (bitAt (w 0) (w 3)) (bitAt (w 0) (w 1))))
      (andBit (bitAt (w 0) (w 3)) (bitAt (w 0) (w 1)))

/-- The Cobham step computes `subStep`. -/
theorem subStepFn_eq (w : Fin 4 → List Bool) :
    subStepFn w = subStep (w 2) (w 3) (w 0).length (w 1) := by
  simp only [subStepFn, subStep, subDigit, subBorrowBit, bitAt_eq_getD_single, xorFlag_single,
    notBit_single, andBit_single, orBit_single, List.append_assoc,
    List.singleton_append]

/-- The step function is in Cobham's algebra. -/
theorem subStepFn_mem : Cobham subStepFn := by
  have hbit : ∀ k : Fin 4, Cobham fun w : Fin 4 → List Bool ↦ bitAt (w 0) (w k) := fun k ↦
    (Cobham.comp₂ Cobham.bitAtFn (.proj 0) (.proj k)).of_eq fun _ ↦ by simp
  refine (Cobham.appendFn (Cobham.appendFn (Cobham.takeFn (.proj 0) (.proj 1))
    (cobham_xorFlag_comp (hbit 2) (cobham_xorFlag_comp (hbit 3) (hbit 1))))
    (Cobham.orFn (Cobham.andFn (Cobham.notFn (hbit 2)) (Cobham.orFn (hbit 3) (hbit 1)))
      (Cobham.andFn (hbit 3) (hbit 1)))).of_eq fun _ ↦ rfl

/-- `subCore` as a recursion on notation over the counter, with parameters `⟨a, b⟩`. -/
theorem recNotation_subCore (c : List Bool) (v : Fin 2 → List Bool) :
    recNotation (fun _ : Fin 2 → List Bool ↦ ([false] : List Bool)) subStepFn subStepFn c v =
      subCore (v 0) (v 1) c := by
  induction c with
  | nil => rfl
  | cons b c ih =>
    rw [recNotation_cons, Bool.cond_self, subStepFn_eq, ih]
    rfl

/-- The record has one more bit than the counter. -/
@[simp] theorem subCore_length (a b c : List Bool) : (subCore a b c).length = c.length + 1 := by
  induction c with
  | nil => rfl
  | cons _ c ih =>
    simp only [subCore, subStep, List.length_append, List.length_take, ih, List.length_cons,
      List.length_nil]
    omega

/-- The position just past a block of known length in `l ++ [d, e]` holds `e`. -/
theorem getD_append_pair {l : List Bool} {i : ℕ} (d e x : Bool) (hl : l.length = i) :
    (l ++ [d, e]).getD (i + 1) x = e := by
  rw [List.getD_append_right _ _ _ _ (by omega), hl, Nat.add_sub_cancel_left]
  rfl

/-- Taking one bit past a block of known length in `l ++ [d, e]` yields `l ++ [d]`. -/
theorem take_append_pair {l : List Bool} {i : ℕ} (d e : Bool) (hl : l.length = i) :
    (l ++ [d, e]).take (i + 1) = l ++ [d] := by
  rw [show l ++ [d, e] = (l ++ [d]) ++ [e] by simp]
  exact List.take_left' (by simp [hl])

/-- The invariant of the borrow recursion at position `i = |c|`:
`decNat (a.take i) + borrowᵢ · 2^i = decNat (b.take i) + decNat digitsᵢ`. -/
theorem subCore_spec (a b c : List Bool) :
    decNat (a.take c.length) + 2 ^ c.length * ((subCore a b c).getD c.length false).toNat =
      decNat (b.take c.length) + decNat ((subCore a b c).take c.length) := by
  induction c with
  | nil => simp [subCore]
  | cons x c ih =>
    have hl : ((subCore a b c).take c.length).length = c.length := by
      rw [List.length_take, subCore_length]
      omega
    simp only [List.length_cons, subCore, subStep]
    rw [getD_append_pair _ _ _ hl, take_append_pair _ _ hl, decNat_append_eq_add_mul, hl,
      decNat_take_add_one_eq a, decNat_take_add_one_eq b, pow_succ]
    generalize a.getD c.length false = ai
    generalize b.getD c.length false = bi
    generalize (subCore a b c).getD c.length false = bo at ih ⊢
    generalize 2 ^ c.length = P at ih ⊢
    cases ai <;> cases bi <;> cases bo <;> simp [subDigit, subBorrowBit, decNat_cons] at ih ⊢ <;>
      omega

/-- The final record of the subtractor over the counter `a ++ b`. -/
theorem subCore_final (a b : List Bool) :
    decNat a + 2 ^ (a ++ b).length * ((subCore a b (a ++ b)).getD (a ++ b).length false).toNat =
      decNat b + decNat ((subCore a b (a ++ b)).take (a ++ b).length) := by
  have h := subCore_spec a b (a ++ b)
  rwa [List.take_of_length_le (by simp), List.take_of_length_le (by simp)] at h

/-- The digits of the final record denote less than `2 ^ |a ++ b|`. -/
theorem decNat_subCore_take_lt (a b : List Bool) :
    decNat ((subCore a b (a ++ b)).take (a ++ b).length) < 2 ^ (a ++ b).length := by
  have h := decNat_lt_two_pow_length ((subCore a b (a ++ b)).take (a ++ b).length)
  rwa [List.length_take, subCore_length, Nat.min_eq_left (by omega)] at h

/-- The borrow recursion is in Cobham's algebra (counter first, then `a`, `b`). -/
theorem cobham_subCore : Cobham fun v : Fin 3 → List Bool ↦ subCore (v 1) (v 2) (v 0) := by
  have hj : Cobham fun w : Fin 3 → List Bool ↦ false :: w 0 :=
    (Cobham.comp (.bit false) fun _ : Fin 1 ↦ .proj 0).of_eq fun _ ↦ rfl
  refine (Cobham.boundedRec (Cobham.const [false]) subStepFn_mem subStepFn_mem hj ?_).of_eq
    fun v ↦ ?_
  · intro c v
    rw [recNotation_subCore, subCore_length, Fin.cons_zero, List.length_cons]
  · rw [recNotation_subCore]
    rfl

/-- Composition form of `cobham_subCore`. -/
theorem cobham_subCore_comp {n : ℕ} {gc ga gb : (Fin n → List Bool) → List Bool}
    (hc : Cobham gc) (ha : Cobham ga) (hb : Cobham gb) :
    Cobham fun v : Fin n → List Bool ↦ subCore (ga v) (gb v) (gc v) :=
  (Cobham.comp₃ cobham_subCore hc ha hb).of_eq fun _ ↦ by simp

/-! ### Subtraction and comparisons -/

/-- Strict comparison flag: `[true]` iff `decNat a < decNat b` (the final borrow of the
subtractor run over the counter `a ++ b`). -/
def ltBits (a b : List Bool) : List Bool := bitAt (a ++ b) (subCore a b (a ++ b))

/-- Truncated subtraction of LSB-first numerals: denotes `decNat a - decNat b` (the digits of the
subtractor, or `[]` when the final borrow is set). -/
def subBits (a b : List Bool) : List Bool :=
  caseBit₀ (ltBits a b) [] ((subCore a b (a ++ b)).take (a ++ b).length)

/-- Non-strict comparison flag: `[true]` iff `decNat a ≤ decNat b`. -/
def leBits (a b : List Bool) : List Bool := notBit (ltBits b a)

/-- Equality flag on values: `[true]` iff `decNat a = decNat b`. -/
def eqBits (a b : List Bool) : List Bool := andBit (leBits a b) (leBits b a)

/-- Zero test as a one-bit flag: every bit is `false`. -/
def isZeroBits (a : List Bool) : List Bool := Cobham.allZeroFlag a

/-- `ltBits` is the final borrow bit. -/
theorem ltBits_eq (a b : List Bool) :
    ltBits a b = [(subCore a b (a ++ b)).getD (a ++ b).length false] :=
  bitAt_eq_getD_single _ _

theorem ltBits_eq_true_iff (a b : List Bool) : ltBits a b = [true] ↔ decNat a < decNat b := by
  have h := subCore_final a b
  have hD := decNat_subCore_take_lt a b
  rw [ltBits_eq]
  generalize (subCore a b (a ++ b)).getD (a ++ b).length false = bo at h
  generalize 2 ^ (a ++ b).length = P at h hD
  generalize decNat ((subCore a b (a ++ b)).take (a ++ b).length) = D at h hD
  cases bo <;> simp only [Bool.toNat_true, Bool.toNat_false, mul_one, mul_zero, add_zero] at h <;>
    simp <;> omega

theorem ltBits_flag (a b : List Bool) : ltBits a b = [true] ∨ ltBits a b = [false] := by
  rw [ltBits_eq]
  cases (subCore a b (a ++ b)).getD (a ++ b).length false <;> simp

/-- The complementary reading of the strict comparison flag. -/
theorem ltBits_eq_false_iff (a b : List Bool) : ltBits a b = [false] ↔ decNat b ≤ decNat a := by
  rw [← Nat.not_lt, ← ltBits_eq_true_iff]
  rcases ltBits_flag a b with h | h <;> simp [h]

theorem decNat_subBits (a b : List Bool) : decNat (subBits a b) = decNat a - decNat b := by
  have h := subCore_final a b
  have hD := decNat_subCore_take_lt a b
  rw [subBits, ltBits_eq]
  generalize (subCore a b (a ++ b)).getD (a ++ b).length false = bo at h
  generalize 2 ^ (a ++ b).length = P at h hD
  generalize (subCore a b (a ++ b)).take (a ++ b).length = D at h hD ⊢
  cases bo
  · rw [caseBit₀_cons, Bool.cond_false]
    simp only [Bool.toNat_false, mul_zero, add_zero] at h
    omega
  · rw [caseBit₀_cons, Bool.cond_true, decNat_nil]
    simp only [Bool.toNat_true, mul_one] at h
    omega

theorem length_subBits_le (a b : List Bool) : (subBits a b).length ≤ a.length + b.length + 2 := by
  rw [subBits]
  refine (caseBit₀_length_le _ _ _).trans ?_
  simp only [List.nil_append, List.length_take, subCore_length, List.length_append]
  omega

theorem cobham_ltBits_comp {n : ℕ} {g₀ g₁ : (Fin n → List Bool) → List Bool}
    (h₀ : Cobham g₀) (h₁ : Cobham g₁) :
    Cobham fun v : Fin n → List Bool ↦ ltBits (g₀ v) (g₁ v) :=
  (Cobham.comp₂ Cobham.bitAtFn (Cobham.appendFn h₀ h₁)
    (cobham_subCore_comp (Cobham.appendFn h₀ h₁) h₀ h₁)).of_eq fun _ ↦ by simp [ltBits]

theorem cobham_subBits_comp {n : ℕ} {g₀ g₁ : (Fin n → List Bool) → List Bool}
    (h₀ : Cobham g₀) (h₁ : Cobham g₁) :
    Cobham fun v : Fin n → List Bool ↦ subBits (g₀ v) (g₁ v) :=
  (Cobham.iteFn (cobham_ltBits_comp h₀ h₁) (Cobham.const [])
    (Cobham.takeFn (Cobham.appendFn h₀ h₁)
      (cobham_subCore_comp (Cobham.appendFn h₀ h₁) h₀ h₁))).of_eq fun _ ↦ rfl

/-- Truncated subtraction is in Cobham's algebra. -/
theorem cobham_subBits : Cobham fun v : Fin 2 → List Bool ↦ subBits (v 0) (v 1) :=
  cobham_subBits_comp (.proj 0) (.proj 1)

theorem isZeroBits_eq_true_iff (a : List Bool) : isZeroBits a = [true] ↔ decNat a = 0 := by
  rw [isZeroBits, Cobham.allZeroFlag_eq_true_iff, decNat_eq_zero_iff_all_false]

theorem isZeroBits_flag (a : List Bool) : isZeroBits a = [true] ∨ isZeroBits a = [false] :=
  Cobham.allZeroFlag_flag a

theorem cobham_isZeroBits_comp {n : ℕ} {g : (Fin n → List Bool) → List Bool} (hg : Cobham g) :
    Cobham fun v : Fin n → List Bool ↦ isZeroBits (g v) :=
  (Cobham.allZeroFlag_mem hg).of_eq fun _ ↦ rfl

theorem leBits_eq_true_iff (a b : List Bool) : leBits a b = [true] ↔ decNat a ≤ decNat b := by
  rw [leBits, Cobham.notBit_eq_true_iff (ltBits_flag b a), ltBits_eq_false_iff]

theorem leBits_flag (a b : List Bool) : leBits a b = [true] ∨ leBits a b = [false] := by
  rw [leBits]
  rcases ltBits_flag b a with h | h <;> simp [h, notBit]

theorem eqBits_eq_true_iff (a b : List Bool) : eqBits a b = [true] ↔ decNat a = decNat b := by
  rw [eqBits, Cobham.andBit_eq_true_iff (leBits_flag a b) (leBits_flag b a), leBits_eq_true_iff,
    leBits_eq_true_iff]
  exact ⟨fun h ↦ le_antisymm h.1 h.2, fun h ↦ ⟨h.le, h.ge⟩⟩

theorem eqBits_flag (a b : List Bool) : eqBits a b = [true] ∨ eqBits a b = [false] :=
  andBit_flag _ _

theorem cobham_leBits_comp {n : ℕ} {g₀ g₁ : (Fin n → List Bool) → List Bool}
    (h₀ : Cobham g₀) (h₁ : Cobham g₁) :
    Cobham fun v : Fin n → List Bool ↦ leBits (g₀ v) (g₁ v) :=
  (Cobham.notFn (cobham_ltBits_comp h₁ h₀)).of_eq fun _ ↦ rfl

theorem cobham_eqBits_comp {n : ℕ} {g₀ g₁ : (Fin n → List Bool) → List Bool}
    (h₀ : Cobham g₀) (h₁ : Cobham g₁) :
    Cobham fun v : Fin n → List Bool ↦ eqBits (g₀ v) (g₁ v) :=
  (Cobham.andFn (cobham_leBits_comp h₀ h₁) (cobham_leBits_comp h₁ h₀)).of_eq fun _ ↦ rfl

end SparseDiv.StringArith
