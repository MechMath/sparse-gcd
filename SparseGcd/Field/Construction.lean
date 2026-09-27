import SparseGcd.Field.Package
import SparseGcd.Basic.Seeds
import SparseDivComplexity.Encoding
import SparseDivComplexity.StringArith.Blocks
import Complexitylib.Classes.P.Defs

/-!
# The BCR/AIRR prime construction as an explicit hypothesis (Lemma 14)

The paper invokes the Las Vegas prime-construction procedure of Bi–Cheng–Rojas (cited as
"Theorem 1.11"; Theorem 1.10 in the author version we have) which, for `N ≥ 4`, produces distinct
primes `ℓ_1, …, ℓ_N`, a cofactor `c` and a prime `p = 1 + c ∏ ℓ_j` with `log p = poly(N)` in
expected polynomial time. Its proof needs effective prime-density estimates in arithmetic
progressions and a polynomial-time primality test, neither of which is available here; it is
therefore an **external dependency, not closed**, and is stated as the structure
`PrimeConstruction`: a polynomial-time function (`FP`) of the unary `N` and a random seed which
either outputs a valid package or fails, succeeding with probability at least `1/2` for `N ≥ 4`.
The Las Vegas expected-time procedure is replaced by this bounded-cutoff form, as the paper's
Lemma 26 remark suggests; cutoff failures are counted in the error budget.
-/

open Complexity SparseDiv Finset

namespace SparseGcd

/-- Encoding of a package `(ℓ, c)`: framed list of numerals, then `c`. -/
def encPackage (ℓ : List ℕ) (c : ℕ) : List Bool := pair (SparseDiv.StringArith.frame (ℓ.map encNat)) (encNat c)

/-- Decoding (lenient on numerals, strict on framing). -/
def decPackage (s : List Bool) : Option (List ℕ × ℕ) :=
  (unpair? s).bind fun ac ↦
    (undelimitBlocks ac.1).map fun bs ↦ (bs.map decNat, decNat ac.2)

theorem decPackage_encPackage (ℓ : List ℕ) (c : ℕ) : decPackage (encPackage ℓ c) = some (ℓ, c) := by
  have h : undelimitBlocks ((ℓ.map fun x ↦ delimit (encNat x)).flatten) = some (ℓ.map encNat) := by
    simpa [List.map_map, Function.comp_def] using undelimitBlocks_flatten_delimit (ℓ.map encNat)
  simp [decPackage, encPackage, SparseDiv.StringArith.frame, h, List.map_map, Function.comp_def,
    SparseDiv.decNat_encNat]

/-- The unary input `N`. -/
def unaryN (N : ℕ) : List Bool := List.replicate N true

/-- Validity of a decoded package for `N`. -/
def ValidPackage (N : ℕ) (ℓ : List ℕ) (c : ℕ) : Prop :=
  ℓ.length = N ∧ ℓ.Nodup ∧ (∀ q ∈ ℓ, q.Prime) ∧ 1 ≤ c ∧ (1 + c * ℓ.prod).Prime

/-- Package from a valid decode. -/
def ValidPackage.toPackage {N : ℕ} {ℓ : List ℕ} {c : ℕ} (h : ValidPackage N ℓ c) : PrimePackage :=
  ⟨ℓ, c, h.2.2.1, h.2.1, h.2.2.2.1, h.2.2.2.2⟩

/-- **Hypothesis (Lemma 14, BCR/AIRR).** A randomized polynomial-time prime construction. -/
structure PrimeConstruction where
  /-- The procedure, on `pair (unaryN N) seed`. -/
  build : List Bool → List Bool
  build_mem_FP : build ∈ FP
  /-- Seed length as a polynomial in `N`. -/
  seedLen : Polynomial ℕ
  /-- Bit-length bound `bitLength p ≤ bitBound N`. -/
  bitBound : Polynomial ℕ
  /-- Whatever decodes is a valid package with small `p`. -/
  sound : ∀ N seed ℓ c, decPackage (build (pair (unaryN N) seed)) = some (ℓ, c) →
    ValidPackage N ℓ c ∧ Nat.size (1 + c * ℓ.prod) ≤ bitBound.eval N
  /-- Success probability at least `1/2` for `N ≥ 4` over seeds of the declared length. -/
  success : ∀ N, 4 ≤ N → (1 : ℚ) / 2 ≤ eventProb (univ.filter fun r : BitString (seedLen.eval N) ↦
    (decPackage (build (pair (unaryN N) (List.ofFn r)))).isSome)

namespace PrimeConstruction

variable (C : PrimeConstruction)

/-- Run `t` attempts on consecutive seed blocks of length `L`; return the first valid package. -/
def firstPackage (N t L : ℕ) (bits : List Bool) : Option (List ℕ × ℕ) :=
  (List.range t).findSome? fun i ↦ decPackage (C.build (pair (unaryN N) ((bits.drop (i * L)).take L)))

theorem firstPackage_sound {N t L : ℕ} {bits : List Bool} {ℓ : List ℕ} {c : ℕ}
    (h : C.firstPackage N t L bits = some (ℓ, c)) :
    ValidPackage N ℓ c ∧ Nat.size (1 + c * ℓ.prod) ≤ C.bitBound.eval N := by
  obtain ⟨i, -, hi⟩ := List.exists_of_findSome?_eq_some h
  exact C.sound N _ ℓ c hi

/-- All attempts on a `t * L`-bit seed fail iff no block lies in the success event. -/
theorem firstPackage_ofFn_eq_none_iff (N t L : ℕ) (w : BitString (t * L)) :
    C.firstPackage N t L (List.ofFn w) = none ↔
      blockEventCount (univ.filter fun r : BitString L ↦
        (decPackage (C.build (pair (unaryN N) (List.ofFn r)))).isSome) w = 0 := by
  rw [firstPackage, List.findSome?_eq_none_iff, blockEventCount, Finset.card_eq_zero,
    Finset.filter_eq_empty_iff]
  constructor
  · intro h i _
    have := h i.val (List.mem_range.mpr i.isLt)
    simp only [mem_filter, mem_univ, true_and, ofFn_blocksEquiv]
    rw [Option.isSome_iff_ne_none]
    exact fun hne ↦ hne this
  · intro h i hi
    have := h (Finset.mem_univ (⟨i, List.mem_range.mp hi⟩ : Fin t))
    simp only [mem_filter, mem_univ, true_and, ofFn_blocksEquiv] at this
    exact Option.not_isSome_iff_eq_none.mp this

/-- All `t` attempts fail with probability at most `2^{-t}` (seed blocks of the declared length). -/
theorem eventProb_firstPackage_none_le (N t : ℕ) (hN : 4 ≤ N) :
    eventProb (univ.filter fun w : BitString (t * C.seedLen.eval N) ↦
      C.firstPackage N t (C.seedLen.eval N) (List.ofFn w) = none) ≤ 1 / (2 : ℚ) ^ t := by
  simp_rw [firstPackage_ofFn_eq_none_iff]
  rw [eventProb_blockEventCount_eq_zero, ← one_div_pow]
  have h1 := C.success N hN
  have h2 := eventProb_le_one (univ.filter fun r : BitString (C.seedLen.eval N) ↦
    (decPackage (C.build (pair (unaryN N) (List.ofFn r)))).isSome)
  exact pow_le_pow_left₀ (by linarith) (by linarith) t

end PrimeConstruction

end SparseGcd
