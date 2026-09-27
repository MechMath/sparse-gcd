import SparseDivComplexity.StringArith.Succ

/-!
# Binary addition in Cobham's algebra

`addBits a b` is an LSB-first numeral denoting `decNat a + decNat b`. Only the exported theorem
statements are part of the interface: the definition body may be any computable algorithm that is
convenient for the Cobham-membership proof (e.g. a bounded recursion on notation over the counter
string `a ++ b`, maintaining the partial sum together with the carry at the current position, and
reading the current bits with `Complexity.Cobham.bitAt`).

## Implementation

Carries propagate from the least significant bit upwards, whereas recursion on notation peels the
least significant bit first and recurses on the *higher* bits, so ripple addition cannot be written
as a direct recursion on one of the summands. Instead `addBits` is a limited recursion on notation
over the *counter* `a ++ b`, whose bits are ignored: after `i` steps the recursive value is the
string `s ++ [k]` consisting of the low `i` digits `s` of the sum followed by the carry `k` into
position `i`, and the step (a full adder) reads bit `i` of `a`, of `b`, and the carry through
`Complexity.bitAt` with the processed part of the counter as ruler. The bound is
`false :: counter`, whose length `|a| + |b| + 1` is exactly the length of the value.

The reference ripple algorithm `addCarry` is kept and specified separately (`decNat_addCarry`).
-/

open Complexity

namespace SparseDiv.StringArith

/-- Ripple addition with carry (reference definition). -/
def addCarry : List Bool → List Bool → Bool → List Bool
  | [], b, c => if c then succBits b else b
  | a :: as, [], c => if c then succBits (a :: as) else a :: as
  | a :: as, b :: bs, c =>
    (xor (xor a b) c) :: addCarry as bs ((a && b) || (a && c) || (b && c))

/-! ### Flag connectives for the full adder -/

/-- Exclusive-or of two flags, as one total dispatch: `x ? ¬y : y`. -/
def xorBit (x y : List Bool) : List Bool := caseBit₀ x (notBit y) y

/-- Majority of three flags, as one total dispatch: `x ? (y ∨ z) : (y ∧ z)`. -/
def majBit (x y z : List Bool) : List Bool := caseBit₀ x (orBit y z) (andBit y z)

/-- `xorBit` on one-bit flags is the Boolean exclusive-or. -/
@[simp] theorem xorBit_flag (p q : Bool) : xorBit [p] [q] = [xor p q] := by
  cases p <;> cases q <;> rfl

/-- `majBit` on one-bit flags is the Boolean majority. -/
@[simp] theorem majBit_flag (p q r : Bool) :
    majBit [p] [q] [r] = [(p && q) || (p && r) || (q && r)] := by
  cases p <;> cases q <;> cases r <;> rfl

/-- Exclusive-or of two members of the class is in the class. -/
theorem xorFn {n : ℕ} {g₀ g₁ : (Fin n → List Bool) → List Bool}
    (h₀ : Cobham g₀) (h₁ : Cobham g₁) :
    Cobham fun v : Fin n → List Bool ↦ xorBit (g₀ v) (g₁ v) :=
  (Cobham.iteFn h₀ (Cobham.notFn h₁) h₁).of_eq fun _ ↦ rfl

/-- Majority of three members of the class is in the class. -/
theorem majFn {n : ℕ} {g₀ g₁ g₂ : (Fin n → List Bool) → List Bool}
    (h₀ : Cobham g₀) (h₁ : Cobham g₁) (h₂ : Cobham g₂) :
    Cobham fun v : Fin n → List Bool ↦ majBit (g₀ v) (g₁ v) (g₂ v) :=
  (Cobham.iteFn h₀ (Cobham.orFn h₁ h₂) (Cobham.andFn h₁ h₂)).of_eq fun _ ↦ rfl

/-! ### Arithmetic of `decNat` on prefixes -/

/-- Decoding a concatenation: the second block is shifted by the length of the first. -/
theorem decNat_append (s t : List Bool) :
    decNat (s ++ t) = decNat s + 2 ^ s.length * decNat t := by
  induction s with
  | nil => simp
  | cons b s ih =>
    simp only [List.cons_append, decNat_cons, ih, List.length_cons, pow_succ]
    ring

/-- Extending a prefix by one bit adds that bit at its weight (`bitOf` is `false` past the end,
so the identity also holds beyond the length of the string). -/
theorem decNat_take_succ (a : List Bool) (i : ℕ) :
    decNat (a.take (i + 1)) = decNat (a.take i) + 2 ^ i * (if bitOf a i then 1 else 0) := by
  induction i generalizing a with
  | zero =>
    cases a with
    | nil => simp [bitOf]
    | cons x a => simp [decNat_cons, bitOf]
  | succ i ih =>
    cases a with
    | nil => simp [bitOf]
    | cons x a =>
      have hbit : bitOf (x :: a) (i + 1) = bitOf a i := rfl
      simp only [List.take_succ_cons, decNat_cons, ih, hbit, pow_succ]
      ring

/-- A string of length `i + 1` is its first `i` bits followed by its bit at position `i`. -/
theorem eq_take_append_bitOf (r : List Bool) (i : ℕ) (hr : r.length = i + 1) :
    r = r.take i ++ [bitOf r i] := by
  have hd : r.drop i = [bitOf r i] := by
    have h1 : r.drop (i + 1) = [] := List.drop_eq_nil_of_le (by omega)
    rw [bitOf, List.drop_eq_getElem_cons (by omega : i < r.length), h1, List.headD_cons]
  calc r = r.take i ++ r.drop i := (List.take_append_drop i r).symm
    _ = r.take i ++ [bitOf r i] := by rw [hd]

/-! ### The counter recursion -/

/-- One step of the addition recursion. `t` is the processed part of the counter, whose length is
the current position `i`; `r` is the state (the low `i` sum digits followed by the carry into
position `i`); `a`, `b` are the summands. The step replaces the carry by the sum digit at `i` and
the outgoing carry (a full adder on the three flags `bitAt t a`, `bitAt t b`, `bitAt t r`). -/
def addStep (t r a b : List Bool) : List Bool :=
  r.take t.length ++
    (xorBit (xorBit (bitAt t a) (bitAt t b)) (bitAt t r) ++
      majBit (bitAt t a) (bitAt t b) (bitAt t r))

/-- The base case of the addition recursion: no digits and a zero carry. -/
def addBase (_ : Fin 2 → List Bool) : List Bool := [false]

/-- The step of the addition recursion in the argument order fixed by `recNotation`:
`w 0` is the tail of the counter, `w 1` the recursive value, `w 2`, `w 3` the summands. -/
def addStepFn (w : Fin 4 → List Bool) : List Bool := addStep (w 0) (w 1) (w 2) (w 3)

/-- Binary addition of LSB-first numerals, as a limited recursion on notation over the counter
`a ++ b` (see the module docstring). The result has length `|a| + |b| + 1`. -/
def addBits (a b : List Bool) : List Bool :=
  recNotation addBase addStepFn addStepFn (a ++ b) ![a, b]

/-- The full-adder step: on a state of length `|t| + 1` it produces a state of length `|t| + 2`
whose value has grown by bit `|t|` of each summand at its weight. -/
theorem addStep_spec (t r a b : List Bool) (hr : r.length = t.length + 1) :
    (addStep t r a b).length = t.length + 2 ∧
      decNat (addStep t r a b) = decNat r + 2 ^ t.length * (if bitOf a t.length then 1 else 0) +
        2 ^ t.length * (if bitOf b t.length then 1 else 0) := by
  generalize ht : t.length = i at hr ⊢
  have hlen : (r.take i).length = i := by
    rw [List.length_take]
    omega
  have hr' := congrArg decNat (eq_take_append_bitOf r i hr)
  rw [decNat_append, hlen, decNat_cons, decNat_nil, mul_zero, add_zero] at hr'
  simp only [addStep, ht, bitAt_eq, xorBit_flag, majBit_flag]
  refine ⟨?_, ?_⟩
  · simp only [List.length_append, hlen, List.length_cons, List.length_nil]
  · rw [decNat_append, decNat_append, hlen, hr']
    simp only [List.length_cons, List.length_nil, decNat_cons, decNat_nil]
    cases bitOf a i <;> cases bitOf b i <;> cases bitOf r i <;> simp <;> omega

/-- The invariant of the addition recursion: after processing a counter `c`, the value has length
`|c| + 1` and denotes the sum of the low `|c|` bits of the two parameters. -/
theorem addRec_spec (c : List Bool) (v : Fin 2 → List Bool) :
    (recNotation addBase addStepFn addStepFn c v).length = c.length + 1 ∧
      decNat (recNotation addBase addStepFn addStepFn c v) =
        decNat ((v 0).take c.length) + decNat ((v 1).take c.length) := by
  induction c with
  | nil => simp [addBase, decNat_cons]
  | cons b c ih =>
    obtain ⟨ihl, ihv⟩ := ih
    have hstep : recNotation addBase addStepFn addStepFn (b :: c) v =
        addStep c (recNotation addBase addStepFn addStepFn c v) (v 0) (v 1) := by
      cases b <;> rfl
    obtain ⟨h1, h2⟩ := addStep_spec c _ (v 0) (v 1) ihl
    rw [hstep, List.length_cons, h1, h2, ihv, decNat_take_succ, decNat_take_succ]
    exact ⟨rfl, by ring⟩

/-- The ripple adder with carry computes the sum plus the carry. -/
theorem decNat_addCarry (a b : List Bool) (c : Bool) :
    decNat (addCarry a b c) = decNat a + decNat b + (if c then 1 else 0) := by
  induction a generalizing b c with
  | nil => cases c <;> simp [addCarry, decNat_succBits]
  | cons x as ih =>
    cases b with
    | nil => cases c <;> simp [addCarry, decNat_succBits]
    | cons y bs =>
      simp only [addCarry, decNat_cons, ih]
      cases x <;> cases y <;> cases c <;> simp <;> omega

/-- `addBits` denotes the sum. -/
theorem decNat_addBits (a b : List Bool) : decNat (addBits a b) = decNat a + decNat b := by
  rw [addBits, (addRec_spec _ _).2]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, List.length_append]
  rw [List.take_of_length_le (by omega), List.take_of_length_le (by omega)]

/-- The output of `addBits` is at most two bits longer than the two inputs together. -/
theorem length_addBits_le (a b : List Bool) : (addBits a b).length ≤ a.length + b.length + 2 := by
  rw [addBits, (addRec_spec _ _).1, List.length_append]
  omega

/-- Binary addition is in Cobham's algebra. -/
theorem cobham_addBits : Cobham fun v : Fin 2 → List Bool ↦ addBits (v 0) (v 1) := by
  have hbase : Cobham addBase := (Cobham.const [false]).of_eq fun _ ↦ rfl
  have hbitA : Cobham fun w : Fin 4 → List Bool ↦ bitAt (w 0) (w 2) :=
    (Cobham.comp₂ Cobham.bitAtFn (.proj 0) (.proj 2)).of_eq fun w ↦ by simp
  have hbitB : Cobham fun w : Fin 4 → List Bool ↦ bitAt (w 0) (w 3) :=
    (Cobham.comp₂ Cobham.bitAtFn (.proj 0) (.proj 3)).of_eq fun w ↦ by simp
  have hbitR : Cobham fun w : Fin 4 → List Bool ↦ bitAt (w 0) (w 1) :=
    (Cobham.comp₂ Cobham.bitAtFn (.proj 0) (.proj 1)).of_eq fun w ↦ by simp
  have hstep : Cobham addStepFn :=
    (Cobham.appendFn (Cobham.takeFn (.proj 0) (.proj 1))
      (Cobham.appendFn (xorFn (xorFn hbitA hbitB) hbitR) (majFn hbitA hbitB hbitR))).of_eq
      fun _ ↦ rfl
  have hj : Cobham fun u : Fin 3 → List Bool ↦ false :: u 0 :=
    (Cobham.comp (.bit false) fun _ : Fin 1 ↦ .proj 0).of_eq fun _ ↦ rfl
  have hrec : Cobham fun u : Fin 3 → List Bool ↦
      recNotation addBase addStepFn addStepFn (u 0) (Fin.tail u) := by
    refine Cobham.boundedRec hbase hstep hstep hj fun x v ↦ ?_
    rw [(addRec_spec x v).1, Fin.cons_zero, List.length_cons]
  exact (Cobham.comp₃ hrec (Cobham.appendFn (.proj 0) (.proj 1)) (.proj 0) (.proj 1)).of_eq
    fun v ↦ rfl

/-- Composition form. -/
theorem cobham_addBits_comp {n : ℕ} {g₀ g₁ : (Fin n → List Bool) → List Bool}
    (h₀ : Cobham g₀) (h₁ : Cobham g₁) :
    Cobham fun v : Fin n → List Bool ↦ addBits (g₀ v) (g₁ v) :=
  (Cobham.comp₂ cobham_addBits h₀ h₁).of_eq fun v ↦ by simp

end SparseDiv.StringArith
