import Complexitylib.Classes.P.Cobham
import Complexitylib.Classes.P.Cobham.Internal
import SparseDivComplexity.Encoding

/-!
# Binary successor in Cobham's algebra

LSB-first numerals (`SparseDiv.decNat = Nat.fromBitsLE`). Every function in `SparseDiv.StringArith`
is specified by its effect on `decNat`, comes with an explicit output-length bound, and is shown to
belong to Cobham's function algebra `Complexity.Cobham` (hence to `FP` via `CobhamFP_eq_FP`).

The successor is a genuine recursion on notation on the numeral itself: `succ (b :: s)` depends on
`succ s` only when `b = true`, so no carry has to travel against the direction of the recursion.
-/

open Complexity

namespace SparseDiv.StringArith

/-- Successor of an LSB-first numeral: `[] ↦ [1]`, `0 :: s ↦ 1 :: s`, `1 :: s ↦ 0 :: succ s`. -/
def succBits : List Bool → List Bool
  | [] => [true]
  | false :: s => true :: s
  | true :: s => false :: succBits s

theorem decNat_succBits (s : List Bool) : decNat (succBits s) = decNat s + 1 := by
  induction s with
  | nil => simp [succBits, decNat_cons]
  | cons b s ih => cases b <;> simp [succBits, decNat_cons, ih] <;> omega

theorem length_succBits_le (s : List Bool) : (succBits s).length ≤ s.length + 1 := by
  induction s with
  | nil => simp [succBits]
  | cons b s ih =>
    cases b
    · simp [succBits]
    · simp only [succBits, List.length_cons]
      omega

/-- `succBits` as a recursion on notation: base `[1]`, step `1 :: x` on the peeled tail `x` for a
leading `0`, and `0 :: r` on the recursive value `r` for a leading `1`. -/
theorem recNotation_succBits (x : List Bool) (v : Fin 0 → List Bool) :
    recNotation (fun _ : Fin 0 → List Bool ↦ [true])
      (fun w : Fin 2 → List Bool ↦ true :: w 0)
      (fun w : Fin 2 → List Bool ↦ false :: w 1) x v = succBits x := by
  induction x with
  | nil => rfl
  | cons b x ih => cases b <;> simp [ih, succBits]

/-- The successor is in Cobham's algebra. -/
theorem cobham_succBits : Cobham fun v : Fin 1 → List Bool ↦ succBits (v 0) := by
  -- The step functions: prepend a bit to the tail (`w 0`) or to the recursive value (`w 1`).
  have h₀ : Cobham fun w : Fin 2 → List Bool ↦ true :: w 0 :=
    (Cobham.comp (.bit true) fun _ : Fin 1 ↦ .proj 0).of_eq fun _ ↦ rfl
  have h₁ : Cobham fun w : Fin 2 → List Bool ↦ false :: w 1 :=
    (Cobham.comp (.bit false) fun _ : Fin 1 ↦ .proj 1).of_eq fun _ ↦ rfl
  -- The bound `0 :: x`, of length `|x| + 1`.
  have hj : Cobham fun w : Fin 1 → List Bool ↦ false :: w 0 :=
    (Cobham.comp (.bit false) fun _ : Fin 1 ↦ .proj 0).of_eq fun _ ↦ rfl
  refine (Cobham.boundedRec (Cobham.const [true]) h₀ h₁ hj ?_).of_eq fun v ↦ ?_
  · intro x v
    rw [recNotation_succBits, Fin.cons_zero, List.length_cons]
    exact length_succBits_le x
  · rw [recNotation_succBits]

/-- Composition form: the successor of a Cobham function is Cobham. -/
theorem cobham_succBits_comp {n : ℕ} {g : (Fin n → List Bool) → List Bool} (hg : Cobham g) :
    Cobham fun v : Fin n → List Bool ↦ succBits (g v) :=
  (Cobham.comp cobham_succBits fun _ : Fin 1 ↦ hg).of_eq fun _ ↦ rfl

end SparseDiv.StringArith
