import Complexitylib.Encoding
import SparseDivComplexity.Terms

/-!
# Binary encodings of sparse polynomial instances

Inputs of the decision problems are bit strings (`List Bool`, complexitylib's `Language` alphabet).
This module fixes the sparse binary encoding used throughout:

* numerals are LSB-first binary strings, encoded canonically by `Nat.bits` and decoded leniently by
  `Nat.fromBitsLE` (so every string denotes a number);
* a term `(c, e)` is the self-delimiting pair `pair (encNat c) (encNat e)`;
* a term list is the concatenation of `delimit`-framed term codes;
* a `SparseRoot` instance is `pair (encNat p) (encTerms l)`;
* a divisibility instance `(p, f, g)` is `pair (encNat p) (pair (encTerms f) (encTerms g))`.

All framing primitives (`pair`, `delimit`, `unpair?`, `undelimitBlocks`) come from
`Complexitylib.Encoding`, so the decoders are the ones complexitylib's machines and Cobham functions
already know how to compute.

## Main results

Round-trip lemmas `decNat_encNat`, `decTerm_encTerm`, `decTerms_encTerms`,
`decRootInstance_encRootInstance`, `decDivInstance_encDivInstance`, and explicit length formulas
`length_encNat`, `length_encTerm`, `length_encTerms`, `length_encRootInstance`,
`length_encDivInstance`.
-/

open Complexity

namespace SparseDiv

/-- Canonical LSB-first binary encoding of a natural number (no trailing zero bits). -/
def encNat (n : ℕ) : List Bool := n.bits

/-- Lenient LSB-first decoding: every bit string denotes a natural number. -/
def decNat (s : List Bool) : ℕ := Nat.fromBitsLE s

@[simp] theorem decNat_encNat (n : ℕ) : decNat (encNat n) = n :=
  Nat.fromBitsLE_bits n

@[simp] theorem length_encNat (n : ℕ) : (encNat n).length = Nat.size n :=
  Nat.size_eq_bits_len n

theorem decNat_lt_two_pow_length (s : List Bool) : decNat s < 2 ^ s.length :=
  Nat.fromBitsLE_lt_pow_length s

@[simp] theorem decNat_nil : decNat [] = 0 := by
  simp [decNat, Nat.fromBitsLE, Nat.fromBits]

theorem decNat_cons (b : Bool) (s : List Bool) :
    decNat (b :: s) = (if b then 1 else 0) + 2 * decNat s :=
  Nat.fromBitsLE_cons b s

/-- Encode a term as the self-delimiting pair of its coefficient and exponent codes. -/
def encTerm (t : ℕ × ℕ) : List Bool := pair (encNat t.1) (encNat t.2)

/-- Decode a term block; fails only if the block is not a well-formed pair. -/
def decTerm (b : List Bool) : Option (ℕ × ℕ) :=
  (unpair? b).map fun ab ↦ (decNat ab.1, decNat ab.2)

@[simp] theorem decTerm_encTerm (t : ℕ × ℕ) : decTerm (encTerm t) = some t := by
  simp [decTerm, encTerm, pair]

@[simp] theorem length_encTerm (t : ℕ × ℕ) :
    (encTerm t).length = 2 * Nat.size t.1 + 2 + Nat.size t.2 := by
  simp [encTerm]

/-- Encode a term list as the concatenation of framed term codes. -/
def encTerms (l : Terms) : List Bool := (l.map fun t ↦ delimit (encTerm t)).flatten

/-- Decode a list of term blocks. -/
def decTermList : List (List Bool) → Option Terms
  | [] => some []
  | b :: bs => do
    let t ← decTerm b
    let ts ← decTermList bs
    pure (t :: ts)

/-- Decode a term list from its framed concatenation. -/
def decTerms (s : List Bool) : Option Terms :=
  (undelimitBlocks s).bind decTermList

@[simp] theorem decTermList_map_encTerm (l : Terms) :
    decTermList (l.map encTerm) = some l := by
  induction l with
  | nil => rfl
  | cons t l ih => simp [decTermList, ih]

@[simp] theorem decTerms_encTerms (l : Terms) : decTerms (encTerms l) = some l := by
  have h := undelimitBlocks_flatten_delimit (l.map encTerm)
  rw [List.map_map] at h
  have h' : (l.map fun t ↦ delimit (encTerm t)) = l.map (delimit ∘ encTerm) := rfl
  rw [decTerms, encTerms, h', h, Option.bind_some, decTermList_map_encTerm]

@[simp] theorem encTerms_nil : encTerms [] = [] := rfl

theorem encTerms_cons (t : ℕ × ℕ) (l : Terms) :
    encTerms (t :: l) = delimit (encTerm t) ++ encTerms l := by
  simp [encTerms]

/-- A framed term list is the nested pair `pair (encTerm t₁) (pair (encTerm t₂) (… []))`. -/
theorem encTerms_cons_eq_pair (t : ℕ × ℕ) (l : Terms) :
    encTerms (t :: l) = pair (encTerm t) (encTerms l) := by
  simp [encTerms_cons, pair]

theorem length_encTerms (l : Terms) :
    (encTerms l).length = (l.map fun t ↦ 2 * (encTerm t).length + 2).sum := by
  induction l with
  | nil => rfl
  | cons t l ih => simp [encTerms_cons, ih]

/-- Every listed term costs at least four bits, so the list length is at most a quarter of the
code length. -/
theorem length_le_length_encTerms (l : Terms) : 4 * l.length ≤ (encTerms l).length := by
  induction l with
  | nil => simp
  | cons t l ih =>
    rw [encTerms_cons, List.length_append, delimit_length, List.length_cons, length_encTerm]
    omega

/-- Encode a `SparseRoot` instance `(p, P)`. -/
def encRootInstance (p : ℕ) (l : Terms) : List Bool := pair (encNat p) (encTerms l)

/-- Decode a `SparseRoot` instance. -/
def decRootInstance (s : List Bool) : Option (ℕ × Terms) :=
  (unpair? s).bind fun ar ↦ (decTerms ar.2).map fun l ↦ (decNat ar.1, l)

@[simp] theorem decRootInstance_encRootInstance (p : ℕ) (l : Terms) :
    decRootInstance (encRootInstance p l) = some (p, l) := by
  simp [decRootInstance, encRootInstance, pair]

theorem length_encRootInstance (p : ℕ) (l : Terms) :
    (encRootInstance p l).length = 2 * Nat.size p + 2 + (encTerms l).length := by
  simp [encRootInstance]

/-- Encode a divisibility instance `(p, f, g)` (semantics: does `g` divide `f` in `𝔽_p[x]`?). -/
def encDivInstance (p : ℕ) (f g : Terms) : List Bool :=
  pair (encNat p) (pair (encTerms f) (encTerms g))

/-- Decode a divisibility instance. -/
def decDivInstance (s : List Bool) : Option (ℕ × Terms × Terms) :=
  (unpair? s).bind fun ar ↦
    (unpair? ar.2).bind fun fg ↦
      (decTerms fg.1).bind fun f ↦
        (decTerms fg.2).map fun g ↦ (decNat ar.1, f, g)

@[simp] theorem decDivInstance_encDivInstance (p : ℕ) (f g : Terms) :
    decDivInstance (encDivInstance p f g) = some (p, f, g) := by
  simp [decDivInstance, encDivInstance, pair]

theorem length_encDivInstance (p : ℕ) (f g : Terms) :
    (encDivInstance p f g).length =
      2 * Nat.size p + 2 + (2 * (encTerms f).length + 2 + (encTerms g).length) := by
  simp [encDivInstance]

/-- Decoding is injective on the range of the encoder: two instances with the same code coincide. -/
theorem encDivInstance_injective :
    Function.Injective fun x : ℕ × Terms × Terms ↦ encDivInstance x.1 x.2.1 x.2.2 := by
  rintro ⟨p, f, g⟩ ⟨p', f', g'⟩ h
  have h' := congrArg decDivInstance h
  simpa [decDivInstance_encDivInstance] using h'

theorem encRootInstance_injective :
    Function.Injective fun x : ℕ × Terms ↦ encRootInstance x.1 x.2 := by
  rintro ⟨p, l⟩ ⟨p', l'⟩ h
  have h' := congrArg decRootInstance h
  simpa [decRootInstance_encRootInstance] using h'

end SparseDiv
