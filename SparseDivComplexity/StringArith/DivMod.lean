import SparseDivComplexity.StringArith.Sub

/-!
# Binary division with remainder in Cobham's algebra

`divBits a b` and `modBits a b` denote `decNat a / decNat b` and `decNat a % decNat b` (for a
nonzero divisor), by schoolbook long division: the bits of the dividend are consumed from the most
significant one, the remainder is shifted (`bit :: r`, i.e. `2r + bit` on LSB-first numerals) and
compared with the divisor (`ltBits`), and a quotient bit is produced. Each step is a constant number
of operations already in the algebra; the loop is a bounded recursion on notation on the dividend
used as a counter.

These are the integer division and remainder operations whose sparse bit complexity Appendix A.1 of the companion divisibility paper (arXiv:2606.12130)
requires (coefficient divisibility tests and the primitive part).

## Implementation

Recursion on notation on the dividend `a` peels its least significant bit and recurses on the higher
bits, so the recursive value on the tail `x` has already processed the *more* significant bits — the
peeled bit is exactly the next bit of the schoolbook algorithm. The recursive value `divModStr b x`
is the string `q ++ r` where `q` (the low `|x|` bits) is the quotient numeral and `r` the remainder
numeral of `x` divided by `b`; a step reads `q` and `r` with `take`/`drop` at the ruler `x`, and
its decoded effect is the value-level step `divStepVal` for *every* divisor (also `0`, where
`ltBits` never fires and `subBits` subtracts nothing). The exported `divBits`/`modBits` are the
canonical numerals `encNat` of the reference values, which are `canonBits` of the parts of
`divModStr`; `canonBits` itself is `reverse ∘ dropLeadingZeros ∘ reverse`, a composition of members
of the algebra.
-/

open Complexity

namespace SparseDiv.StringArith

/-- One long-division step on values: shift in the next (more significant → less significant) bit of
the dividend, compare with the divisor, emit a quotient bit. -/
def divStepVal (b : ℕ) (qr : ℕ × ℕ) (bit : Bool) : ℕ × ℕ :=
  let r := 2 * qr.2 + (if bit then 1 else 0)
  if r < b then (2 * qr.1, r) else (2 * qr.1 + 1, r - b)

/-- Reference long division on values, processing the dividend's bits from the most significant. -/
def divModVal (a b : List Bool) : ℕ × ℕ := a.reverse.foldl (divStepVal (decNat b)) (0, 0)

/-! ### The value-level reference algorithm -/

/-- On the pair `(m / d, m % d)` the step produces the quotient and remainder of `2m + bit`. -/
theorem divStepVal_div_mod {d : ℕ} (hd : d ≠ 0) (m : ℕ) (bit : Bool) :
    divStepVal d (m / d, m % d) bit =
      ((2 * m + (if bit then 1 else 0)) / d, (2 * m + (if bit then 1 else 0)) % d) := by
  have hd' : 0 < d := Nat.pos_of_ne_zero hd
  have hdm := Nat.div_add_mod m d
  have hlt := Nat.mod_lt m hd'
  have hc : (if bit then 1 else 0 : ℕ) ≤ 1 := by split_ifs <;> omega
  simp only [divStepVal]
  generalize (if bit then 1 else 0 : ℕ) = c at hc
  generalize m / d = q at hdm
  generalize m % d = r at hdm hlt
  have h1 : d * (2 * q) = 2 * (d * q) := by ring
  have h2 : d * (2 * q + 1) = 2 * (d * q) + d := by ring
  split_ifs with h
  · have := (Nat.div_mod_unique hd').mpr
      (show 2 * r + c + d * (2 * q) = 2 * m + c ∧ 2 * r + c < d from ⟨by omega, h⟩)
    exact Prod.ext this.1.symm this.2.symm
  · have := (Nat.div_mod_unique hd').mpr
      (show 2 * r + c - d + d * (2 * q + 1) = 2 * m + c ∧ 2 * r + c - d < d from
        ⟨by omega, by omega⟩)
    exact Prod.ext this.1.symm this.2.symm

/-- Folding the step over a big-endian bit list started at `(m / d, m % d)` divides
`m · 2^|l| + fromBits l`. -/
theorem foldl_divStepVal {d : ℕ} (hd : d ≠ 0) (l : List Bool) (m : ℕ) :
    l.foldl (divStepVal d) (m / d, m % d) =
      ((m * 2 ^ l.length + Nat.fromBits l) / d, (m * 2 ^ l.length + Nat.fromBits l) % d) := by
  induction l generalizing m with
  | nil => simp [Nat.fromBits]
  | cons b l ih =>
    rw [List.foldl_cons, divStepVal_div_mod hd, ih]
    have : m * 2 ^ (b :: l).length + Nat.fromBits (b :: l) =
        (2 * m + (if b then 1 else 0)) * 2 ^ l.length + Nat.fromBits l := by
      simp only [Nat.fromBits, List.length_cons, pow_succ]
      ring
    rw [this]

theorem divModVal_spec (a b : List Bool) (hb : decNat b ≠ 0) :
    divModVal a b = (decNat a / decNat b, decNat a % decNat b) := by
  have h0 : ((0 : ℕ), (0 : ℕ)) = (0 / decNat b, 0 % decNat b) := by simp
  rw [divModVal, h0, foldl_divStepVal hb]
  simp only [zero_mul, zero_add]
  rfl

@[simp] theorem divModVal_nil (b : List Bool) : divModVal [] b = (0, 0) := rfl

/-- Peeling the least significant bit of the dividend is the last step of the reference
algorithm. -/
theorem divModVal_cons (bit : Bool) (x b : List Bool) :
    divModVal (bit :: x) b = divStepVal (decNat b) (divModVal x b) bit := by
  simp [divModVal, List.foldl_append]

/-- The reference quotient of `x` fits in `|x|` bits. -/
theorem divModVal_fst_lt (x b : List Bool) : (divModVal x b).1 < 2 ^ x.length := by
  induction x with
  | nil => simp
  | cons bit x ih =>
    rw [divModVal_cons, List.length_cons, pow_succ]
    simp only [divStepVal]
    split_ifs <;> simp <;> omega

/-- The reference remainder of `x` fits in `|x|` bits. -/
theorem divModVal_snd_lt (x b : List Bool) : (divModVal x b).2 < 2 ^ x.length := by
  induction x with
  | nil => simp
  | cons bit x ih =>
    rw [divModVal_cons, List.length_cons, pow_succ]
    simp only [divStepVal]
    split_ifs <;> simp <;> omega

/-! ### Canonical numerals -/

/-- Canonicalize a numeral: the shortest LSB-first encoding of its value (`encNat ∘ decNat`). -/
def canonBits (s : List Bool) : List Bool := encNat (decNat s)

@[simp] theorem decNat_canonBits (s : List Bool) : decNat (canonBits s) = decNat s :=
  decNat_encNat _

theorem length_canonBits_le (s : List Bool) : (canonBits s).length ≤ s.length := by
  rw [canonBits, length_encNat]
  exact Nat.size_le.mpr (decNat_lt_two_pow_length s)

/-- Drop the leading `false` bits of a string (applied to a reversed numeral, this removes the
trailing zero bits). -/
def dropLeadingZeros : List Bool → List Bool
  | [] => []
  | false :: s => dropLeadingZeros s
  | true :: s => true :: s

theorem dropLeadingZeros_length_le (s : List Bool) :
    (dropLeadingZeros s).length ≤ s.length := by
  induction s with
  | nil => simp [dropLeadingZeros]
  | cons b s ih =>
    cases b
    · simp only [dropLeadingZeros, List.length_cons]
      omega
    · simp [dropLeadingZeros]

/-- The result of `dropLeadingZeros` is empty or starts with `true`. -/
theorem dropLeadingZeros_cases (s : List Bool) :
    dropLeadingZeros s = [] ∨ ∃ t, dropLeadingZeros s = true :: t := by
  induction s with
  | nil => exact Or.inl rfl
  | cons b s ih =>
    cases b
    · exact ih
    · exact Or.inr ⟨s, rfl⟩

/-- Dropping leading zeros of the reversed string does not change the value. -/
theorem decNat_reverse_dropLeadingZeros (s : List Bool) :
    decNat (dropLeadingZeros s).reverse = decNat s.reverse := by
  induction s with
  | nil => rfl
  | cons b s ih =>
    cases b
    · rw [dropLeadingZeros, ih, List.reverse_cons, decNat_append]
      simp [decNat_cons]
    · rfl

/-- The head bit of a numeral is the low bit of its value. -/
theorem decNat_cons_eq_bit (b : Bool) (s : List Bool) : decNat (b :: s) = Nat.bit b (decNat s) := by
  rw [decNat_cons, Nat.bit_val]
  cases b <;> simp [add_comm]

/-- A string ending in `true` is the canonical numeral of its value. -/
theorem encNat_decNat_append_true (t : List Bool) :
    encNat (decNat (t ++ [true])) = t ++ [true] := by
  induction t with
  | nil => simp [encNat, decNat_cons]
  | cons b t ih =>
    have hne : decNat (t ++ [true]) ≠ 0 := by
      rw [decNat_append]
      simp [decNat_cons]
    rw [List.cons_append, decNat_cons_eq_bit, encNat, Nat.bits_append_bit _ _ fun h ↦ absurd h hne,
      ← encNat, ih]

/-- Canonicalization removes the trailing zero bits. -/
theorem canonBits_eq (s : List Bool) : canonBits s = (dropLeadingZeros s.reverse).reverse := by
  have h : decNat s = decNat (dropLeadingZeros s.reverse).reverse := by
    rw [decNat_reverse_dropLeadingZeros, List.reverse_reverse]
  rw [canonBits, h]
  rcases dropLeadingZeros_cases s.reverse with h0 | ⟨t, ht⟩
  · rw [h0]
    simp [encNat]
  · rw [ht, List.reverse_cons, encNat_decNat_append_true]

/-- `dropLeadingZeros` as a recursion on notation: a leading `0` returns the recursive value, a
leading `1` returns the argument. -/
theorem recNotation_dropLeadingZeros (x : List Bool) (v : Fin 0 → List Bool) :
    recNotation (fun _ : Fin 0 → List Bool ↦ ([] : List Bool)) (fun w : Fin 2 → List Bool ↦ w 1)
      (fun w : Fin 2 → List Bool ↦ true :: w 0) x v = dropLeadingZeros x := by
  induction x with
  | nil => rfl
  | cons b x ih => cases b <;> simp [ih, dropLeadingZeros]

/-- Dropping leading zeros is in Cobham's algebra. -/
theorem cobham_dropLeadingZeros : Cobham fun v : Fin 1 → List Bool ↦ dropLeadingZeros (v 0) := by
  have h₁ : Cobham fun w : Fin 2 → List Bool ↦ true :: w 0 :=
    (Cobham.comp (.bit true) fun _ : Fin 1 ↦ .proj 0).of_eq fun _ ↦ rfl
  refine (Cobham.boundedRec Cobham.empty (.proj 1) h₁ (.proj 0) ?_).of_eq fun v ↦ ?_
  · intro x v
    rw [recNotation_dropLeadingZeros, Fin.cons_zero]
    exact dropLeadingZeros_length_le x
  · rw [recNotation_dropLeadingZeros]

/-- Composition form of `cobham_dropLeadingZeros`. -/
theorem cobham_dropLeadingZeros_comp {n : ℕ} {g : (Fin n → List Bool) → List Bool}
    (hg : Cobham g) : Cobham fun v : Fin n → List Bool ↦ dropLeadingZeros (g v) :=
  (Cobham.comp cobham_dropLeadingZeros fun _ : Fin 1 ↦ hg).of_eq fun _ ↦ rfl

/-- String reversal of a member of the class is in the class (`reverse ∈ FP`). -/
theorem cobham_reverse_comp {n : ℕ} {g : (Fin n → List Bool) → List Bool} (hg : Cobham g) :
    Cobham fun v : Fin n → List Bool ↦ (g v).reverse :=
  (Cobham.comp (FP_subset_CobhamFP reverse_mem_FP) fun _ : Fin 1 ↦ hg).of_eq fun _ ↦ rfl

/-- Canonicalization (dropping trailing zero bits) is in Cobham's algebra. -/
theorem cobham_canonBits_comp {n : ℕ} {g : (Fin n → List Bool) → List Bool} (hg : Cobham g) :
    Cobham fun v : Fin n → List Bool ↦ canonBits (g v) :=
  (cobham_reverse_comp (cobham_dropLeadingZeros_comp (cobham_reverse_comp hg))).of_eq fun v ↦
    (canonBits_eq (g v)).symm

/-! ### The string algorithm -/

/-- The quotient part of one long-division step: the new quotient bit is `0` iff the shifted
remainder `bit :: r` is below the divisor. -/
def divStepQ (b : List Bool) (bit : Bool) (q r : List Bool) : List Bool :=
  caseBit₀ (ltBits (bit :: r) b) (false :: q) (true :: q)

/-- The remainder part of one long-division step: the shifted remainder, reduced by the divisor
when it is not below it. -/
def divStepR (b : List Bool) (bit : Bool) (r : List Bool) : List Bool :=
  caseBit₀ (ltBits (bit :: r) b) (bit :: r) (subBits (bit :: r) b)

/-- One long-division step on the state `s = q ++ r` with `|q| = |x|` (the tail `x` of the counter
is the ruler separating the two parts). -/
def divStep (b : List Bool) (bit : Bool) (x s : List Bool) : List Bool :=
  divStepQ b bit (s.take x.length) (s.drop x.length) ++ divStepR b bit (s.drop x.length)

/-- Long division of `x` by `b` on strings: the recursive value is `q ++ r` with `|q| = |x|`. -/
def divModStr (b : List Bool) : List Bool → List Bool
  | [] => []
  | bit :: x => divStep b bit x (divModStr b x)

/-- The step of the recursion on notation in the argument order of `recNotation`: `w 0` is the tail
of the counter, `w 1` the recursive value, `w 2` the divisor. -/
def divStepFn (bit : Bool) (w : Fin 3 → List Bool) : List Bool := divStep (w 2) bit (w 0) (w 1)

theorem divStepQ_length (b : List Bool) (bit : Bool) (q r : List Bool) :
    (divStepQ b bit q r).length = q.length + 1 := by
  rw [divStepQ]
  rcases ltBits_flag (bit :: r) b with h | h <;> simp [h]

theorem divStepR_length_le (b : List Bool) (bit : Bool) (r : List Bool) :
    (divStepR b bit r).length ≤ r.length + b.length + 3 := by
  rw [divStepR]
  rcases ltBits_flag (bit :: r) b with h | h
  · simp [h]
    omega
  · rw [h, caseBit₀_cons, Bool.cond_false]
    have := length_subBits_le (bit :: r) b
    simp only [List.length_cons] at this
    omega

theorem decNat_divStepQ (b : List Bool) (bit : Bool) (q r : List Bool) :
    decNat (divStepQ b bit q r) =
      if decNat (bit :: r) < decNat b then 2 * decNat q else 2 * decNat q + 1 := by
  rw [divStepQ]
  rcases ltBits_flag (bit :: r) b with h | h
  · rw [h, caseBit₀_cons, Bool.cond_true, ite_eq_left ((ltBits_eq_true_iff _ _).mp h), decNat_cons]
    simp
  · rw [h, caseBit₀_cons, Bool.cond_false,
      ite_eq_right (not_lt.mpr ((ltBits_eq_false_iff _ _).mp h)), decNat_cons]
    simp only [↓reduceIte]
    omega

theorem decNat_divStepR (b : List Bool) (bit : Bool) (r : List Bool) :
    decNat (divStepR b bit r) =
      if decNat (bit :: r) < decNat b then decNat (bit :: r) else decNat (bit :: r) - decNat b := by
  rw [divStepR]
  rcases ltBits_flag (bit :: r) b with h | h
  · rw [h, caseBit₀_cons, Bool.cond_true, ite_eq_left ((ltBits_eq_true_iff _ _).mp h)]
  · rw [h, caseBit₀_cons, Bool.cond_false,
      ite_eq_right (not_lt.mpr ((ltBits_eq_false_iff _ _).mp h)), decNat_subBits]

/-- The state has at least `|x|` bits (the quotient part) and polynomially many bits in total. -/
theorem divModStr_length (b x : List Bool) :
    x.length ≤ (divModStr b x).length ∧
      (divModStr b x).length ≤ x.length + x.length * (b.length + 3) := by
  induction x with
  | nil => simp [divModStr]
  | cons bit x ih =>
    have hR := divStepR_length_le b bit ((divModStr b x).drop x.length)
    simp only [divModStr, divStep, List.length_append, divStepQ_length, List.length_take,
      List.length_drop, List.length_cons] at hR ⊢
    have : (x.length + 1) * (b.length + 3) = x.length * (b.length + 3) + (b.length + 3) := by ring
    omega

/-- **The invariant of the string algorithm**: the two parts of the state decode to the reference
quotient and remainder (for every divisor). -/
theorem divModStr_spec (b x : List Bool) :
    decNat ((divModStr b x).take x.length) = (divModVal x b).1 ∧
      decNat ((divModStr b x).drop x.length) = (divModVal x b).2 := by
  induction x with
  | nil => simp [divModStr]
  | cons bit x ih =>
    obtain ⟨ihq, ihr⟩ := ih
    have hlen := (divModStr_length b x).1
    have hqlen : (divStepQ b bit ((divModStr b x).take x.length)
        ((divModStr b x).drop x.length)).length = x.length + 1 := by
      rw [divStepQ_length, List.length_take, Nat.min_eq_left hlen]
    rw [divModVal_cons]
    simp only [divModStr, divStep, List.length_cons]
    rw [List.take_left' hqlen, List.drop_left' hqlen, decNat_divStepQ, decNat_divStepR, decNat_cons,
      ihq, ihr]
    simp only [divStepVal]
    generalize (if bit then 1 else 0 : ℕ) = c
    constructor <;> split_ifs <;> simp <;> omega

/-- The step functions are in Cobham's algebra. -/
theorem cobham_divStepFn (bit : Bool) : Cobham (divStepFn bit) := by
  have hq : Cobham fun w : Fin 3 → List Bool ↦ (w 1).take (w 0).length :=
    Cobham.takeFn (.proj 0) (.proj 1)
  have hr : Cobham fun w : Fin 3 → List Bool ↦ bit :: (w 1).drop (w 0).length :=
    (Cobham.comp (.bit bit) fun _ : Fin 1 ↦ Cobham.dropFn (.proj 0) (.proj 1)).of_eq fun _ ↦ rfl
  have hlt := cobham_ltBits_comp hr (.proj 2)
  have hcons : ∀ c : Bool, Cobham fun w : Fin 3 → List Bool ↦ c :: (w 1).take (w 0).length :=
    fun c ↦ (Cobham.comp (.bit c) fun _ : Fin 1 ↦ hq).of_eq fun _ ↦ rfl
  exact (Cobham.appendFn (Cobham.iteFn hlt (hcons false) (hcons true))
    (Cobham.iteFn hlt hr (cobham_subBits_comp hr (.proj 2)))).of_eq fun _ ↦ rfl

/-- `divModStr` as a recursion on notation over the dividend with the divisor as parameter. -/
theorem recNotation_divModStr (x : List Bool) (v : Fin 1 → List Bool) :
    recNotation (fun _ : Fin 1 → List Bool ↦ ([] : List Bool)) (divStepFn false) (divStepFn true)
      x v = divModStr (v 0) x := by
  induction x with
  | nil => rfl
  | cons bit x ih =>
    cases bit
    · show divStep (v 0) false x (recNotation _ _ _ x v) = _
      rw [ih]
      rfl
    · show divStep (v 0) true x (recNotation _ _ _ x v) = _
      rw [ih]
      rfl

/-- The string algorithm is in Cobham's algebra (dividend first, divisor second). -/
theorem cobham_divModStr : Cobham fun v : Fin 2 → List Bool ↦ divModStr (v 1) (v 0) := by
  -- The bound `x ++ smash x (b ++ 000)`, of length `|x| + |x| * (|b| + 3)`.
  have hj : Cobham fun u : Fin 2 → List Bool ↦
      u 0 ++ Complexity.smash (u 0) (u 1 ++ [false, false, false]) :=
    Cobham.appendFn (.proj 0) ((Cobham.comp₂ .smash (.proj 0)
      (Cobham.appendFn (.proj 1) (Cobham.const [false, false, false]))).of_eq fun _ ↦ by simp)
  refine (Cobham.boundedRec (Cobham.const []) (cobham_divStepFn false) (cobham_divStepFn true) hj
    ?_).of_eq fun v ↦ ?_
  · intro x v
    rw [recNotation_divModStr]
    have h1 : (Fin.cons x v : Fin 2 → List Bool) 1 = v 0 := rfl
    simp only [Fin.cons_zero, h1, List.length_append, smash_length, List.length_cons,
      List.length_nil]
    exact (divModStr_length (v 0) x).2
  · rw [recNotation_divModStr]
    rfl

/-! ### The exported operations -/

/-- Quotient numeral (definition body free; specified below). -/
def divBits (a b : List Bool) : List Bool := encNat (divModVal a b).1

/-- Remainder numeral (definition body free; specified below). -/
def modBits (a b : List Bool) : List Bool := encNat (divModVal a b).2

/-- The quotient numeral is the canonical form of the quotient part of the string algorithm. -/
theorem divBits_eq_canonBits (a b : List Bool) :
    divBits a b = canonBits ((divModStr b a).take a.length) := by
  rw [divBits, canonBits, (divModStr_spec b a).1]

/-- The remainder numeral is the canonical form of the remainder part of the string algorithm. -/
theorem modBits_eq_canonBits (a b : List Bool) :
    modBits a b = canonBits ((divModStr b a).drop a.length) := by
  rw [modBits, canonBits, (divModStr_spec b a).2]

theorem decNat_divBits (a b : List Bool) (hb : decNat b ≠ 0) :
    decNat (divBits a b) = decNat a / decNat b := by
  rw [divBits, decNat_encNat, divModVal_spec a b hb]

theorem decNat_modBits (a b : List Bool) (hb : decNat b ≠ 0) :
    decNat (modBits a b) = decNat a % decNat b := by
  rw [modBits, decNat_encNat, divModVal_spec a b hb]

theorem length_divBits_le (a b : List Bool) : (divBits a b).length ≤ a.length + b.length + 2 := by
  rw [divBits, length_encNat]
  have := Nat.size_le.mpr (divModVal_fst_lt a b)
  omega

theorem length_modBits_le (a b : List Bool) : (modBits a b).length ≤ a.length + b.length + 2 := by
  rw [modBits, length_encNat]
  have := Nat.size_le.mpr (divModVal_snd_lt a b)
  omega

/-- Long division is in Cobham's algebra. -/
theorem cobham_divBits : Cobham fun v : Fin 2 → List Bool ↦ divBits (v 0) (v 1) :=
  (cobham_canonBits_comp (Cobham.takeFn (.proj 0) cobham_divModStr)).of_eq fun v ↦
    (divBits_eq_canonBits (v 0) (v 1)).symm

theorem cobham_modBits : Cobham fun v : Fin 2 → List Bool ↦ modBits (v 0) (v 1) :=
  (cobham_canonBits_comp (Cobham.dropFn (.proj 0) cobham_divModStr)).of_eq fun v ↦
    (modBits_eq_canonBits (v 0) (v 1)).symm

theorem cobham_divBits_comp {n : ℕ} {g₀ g₁ : (Fin n → List Bool) → List Bool}
    (h₀ : Cobham g₀) (h₁ : Cobham g₁) :
    Cobham fun v : Fin n → List Bool ↦ divBits (g₀ v) (g₁ v) :=
  (Cobham.comp₂ cobham_divBits h₀ h₁).of_eq fun v ↦ by simp

theorem cobham_modBits_comp {n : ℕ} {g₀ g₁ : (Fin n → List Bool) → List Bool}
    (h₀ : Cobham g₀) (h₁ : Cobham g₁) :
    Cobham fun v : Fin n → List Bool ↦ modBits (g₀ v) (g₁ v) :=
  (Cobham.comp₂ cobham_modBits h₀ h₁).of_eq fun v ↦ by simp

/-- Divisibility flag: `[true]` iff `decNat b ∣ decNat a` (for a nonzero divisor). -/
def dvdBits (a b : List Bool) : List Bool := isZeroBits (modBits a b)

theorem dvdBits_eq_true_iff (a b : List Bool) (hb : decNat b ≠ 0) :
    dvdBits a b = [true] ↔ decNat b ∣ decNat a := by
  rw [dvdBits, isZeroBits_eq_true_iff, decNat_modBits a b hb, Nat.dvd_iff_mod_eq_zero]

theorem cobham_dvdBits_comp {n : ℕ} {g₀ g₁ : (Fin n → List Bool) → List Bool}
    (h₀ : Cobham g₀) (h₁ : Cobham g₁) :
    Cobham fun v : Fin n → List Bool ↦ dvdBits (g₀ v) (g₁ v) :=
  cobham_isZeroBits_comp (cobham_modBits_comp h₀ h₁)

end SparseDiv.StringArith
