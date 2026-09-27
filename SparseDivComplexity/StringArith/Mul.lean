import SparseDivComplexity.StringArith.Add

/-!
# Binary multiplication in Cobham's algebra

`mulBits a b` denotes `decNat a * decNat b`, by shift-and-add recursion on the bits of `b`:
`mul a [] = []`, `mul a (bit :: y) = (if bit then a else []) + (0 :: mul a y)`, which is a recursion
on notation on the second argument with the first argument as parameter.
-/

open Complexity

namespace SparseDiv.StringArith

/-- Shift-and-add multiplication of LSB-first numerals. -/
def mulBits (a : List Bool) : List Bool → List Bool
  | [] => []
  | bit :: y => addBits (if bit then a else []) (false :: mulBits a y)

theorem decNat_mulBits (a b : List Bool) : decNat (mulBits a b) = decNat a * decNat b := by
  induction b with
  | nil => simp [mulBits]
  | cons bit y ih =>
      cases bit <;> simp [mulBits, decNat_addBits, decNat_cons, ih] <;> ring

theorem length_mulBits_le (a b : List Bool) :
    (mulBits a b).length ≤ (a.length + 3) * (b.length + 1) := by
  induction b with
  | nil => simp [mulBits]
  | cons bit y ih =>
      have h := length_addBits_le (if bit then a else []) (false :: mulBits a y)
      have hb : (if bit then a else []).length ≤ a.length := by cases bit <;> simp
      simp only [mulBits, List.length_cons] at h ⊢
      nlinarith

/-- Multiplication with the recursion argument first: `mulBits (v 1) (v 0)` is a limited recursion
on notation on `v 0` with parameter `v 1`, bounded by `smash (v 1 ++ 000) (0 :: v 0)`. -/
theorem cobham_mulBits_swap : Cobham fun v : Fin 2 → List Bool ↦ mulBits (v 1) (v 0) := by
  -- The recursion: base `[]`; on `b :: x` the step argument is `⟨x, rec, a⟩`.
  have hrec : ∀ (x : List Bool) (v : Fin 1 → List Bool),
      recNotation (fun _ : Fin 1 → List Bool ↦ ([] : List Bool))
        (fun w : Fin 3 → List Bool ↦ addBits [] (false :: w 1))
        (fun w : Fin 3 → List Bool ↦ addBits (w 2) (false :: w 1)) x v = mulBits (v 0) x := by
    intro x v
    induction x with
    | nil => rfl
    | cons b x ih =>
        cases b
        · show addBits [] (false :: recNotation _ _ _ x v) = _
          rw [ih]; rfl
        · show addBits (v 0) (false :: recNotation _ _ _ x v) = _
          rw [ih]; rfl
  -- The shifted recursive value `0 :: rec`.
  have hshift : Cobham fun w : Fin 3 → List Bool ↦ false :: w 1 :=
    (Cobham.comp (.bit false) fun _ : Fin 1 ↦ .proj 1).of_eq fun _ ↦ rfl
  have hh₀ : Cobham fun w : Fin 3 → List Bool ↦ addBits [] (false :: w 1) :=
    cobham_addBits_comp (Cobham.const []) hshift
  have hh₁ : Cobham fun w : Fin 3 → List Bool ↦ addBits (w 2) (false :: w 1) :=
    cobham_addBits_comp (.proj 2) hshift
  -- The length bound `(|a| + 3) * (|x| + 1)` realized by `smash`.
  have hj : Cobham fun w : Fin 2 → List Bool ↦
      Complexity.smash (w 1 ++ [false, false, false]) (false :: w 0) :=
    (Cobham.comp₂ .smash (Cobham.appendFn (.proj 1) (Cobham.const [false, false, false]))
      ((Cobham.comp (.bit false) fun _ : Fin 1 ↦ .proj 0).of_eq fun _ ↦ rfl)).of_eq
        fun v ↦ by simp
  refine (Cobham.boundedRec (.empty) hh₀ hh₁ hj ?_).of_eq fun v ↦ ?_
  · intro x v
    rw [hrec]
    have h0 : (Fin.cons x v : Fin 2 → List Bool) 0 = x := rfl
    have h1 : (Fin.cons x v : Fin 2 → List Bool) 1 = v 0 := rfl
    simp only [h0, h1, smash_length, List.length_append, List.length_cons, List.length_nil]
    exact length_mulBits_le (v 0) x
  · rw [hrec]
    rfl

/-- Binary multiplication is in Cobham's algebra. -/
theorem cobham_mulBits : Cobham fun v : Fin 2 → List Bool ↦ mulBits (v 0) (v 1) :=
  (Cobham.comp₂ cobham_mulBits_swap (.proj 1) (.proj 0)).of_eq fun v ↦ by simp

theorem cobham_mulBits_comp {n : ℕ} {g₀ g₁ : (Fin n → List Bool) → List Bool}
    (h₀ : Cobham g₀) (h₁ : Cobham g₁) :
    Cobham fun v : Fin n → List Bool ↦ mulBits (g₀ v) (g₁ v) :=
  (Cobham.comp₂ cobham_mulBits h₀ h₁).of_eq fun v ↦ by simp

end SparseDiv.StringArith
