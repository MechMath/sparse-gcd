import SparseDivComplexity.StringArith.DivMod
import SparseDivComplexity.StringArith.Blocks

/-!
# Euclid's algorithm in Cobham's algebra

`gcdBits a b` denotes `Nat.gcd (decNat a) (decNat b)`. Euclid's algorithm `(a, b) ↦ (b, a mod b)`
terminates within `2(|a| + |b|) + 2` steps (every two steps at least halve the second component), so
it is a clocked iteration (`Complexity.Cobham.iterFn`) of a step already in the algebra, with the
pair state bounded by a ruler. This is the integer gcd whose sparse bit complexity Appendix A.1 of the companion divisibility paper (arXiv:2606.12130)
requires for the content of an integer polynomial.

## Implementation

The state of the string iteration is the canonical pair `pair (encNat p) (encNat q)` of the two
current values; one step (`euclidStep`) tests the second component for zero (`isZeroBits`), and
otherwise moves to `pair q (canonBits (modBits p q))`. Canonicalizing the remainder keeps both
components at most `max |a| |b|` bits long along the *whole* trajectory, for arbitrary inputs, since
Euclid's step never increases the maximum of the two values (`euclidStepVal_iterate_le_max`); so the
ruler `pair (a ++ b) (a ++ b)` bounds every state and no clamp is needed. The clock is the string
`(a ++ b) ++ (a ++ b) ++ [0, 0]` of length `2(|a| + |b|) + 2`.
-/

open Complexity

namespace SparseDiv.StringArith

/-- One Euclid step on values, idempotent once the second component is zero. -/
def euclidStepVal (ab : ℕ × ℕ) : ℕ × ℕ := if ab.2 = 0 then ab else (ab.2, ab.1 % ab.2)

/-- One Euclid step preserves the gcd (`gcd b (a % b) = gcd a b`). -/
theorem euclidStepVal_gcd (ab : ℕ × ℕ) :
    Nat.gcd (euclidStepVal ab).1 (euclidStepVal ab).2 = Nat.gcd ab.1 ab.2 := by
  unfold euclidStepVal
  split_ifs with h
  · rfl
  · rw [Nat.gcd_comm ab.2, ← Nat.gcd_rec, Nat.gcd_comm]

/-! ### Termination analysis on values -/

/-- The gcd is an invariant of the iterated Euclid step. -/
theorem euclidStepVal_iterate_gcd (ab : ℕ × ℕ) (k : ℕ) :
    Nat.gcd (euclidStepVal^[k] ab).1 (euclidStepVal^[k] ab).2 = Nat.gcd ab.1 ab.2 := by
  induction k with
  | zero => rfl
  | succ k ih => rw [Function.iterate_succ_apply', euclidStepVal_gcd, ih]

/-- One Euclid step never increases the maximum of the two components. -/
theorem euclidStepVal_le_max (ab : ℕ × ℕ) :
    (euclidStepVal ab).1 ≤ max ab.1 ab.2 ∧ (euclidStepVal ab).2 ≤ max ab.1 ab.2 := by
  unfold euclidStepVal
  split_ifs with h
  · exact ⟨le_max_left _ _, le_max_right _ _⟩
  · exact ⟨le_max_right _ _,
      (Nat.mod_lt _ (Nat.pos_of_ne_zero h)).le.trans (le_max_right _ _)⟩

/-- Along the whole Euclid trajectory both components stay below the initial maximum. -/
theorem euclidStepVal_iterate_le_max (ab : ℕ × ℕ) (k : ℕ) :
    (euclidStepVal^[k] ab).1 ≤ max ab.1 ab.2 ∧ (euclidStepVal^[k] ab).2 ≤ max ab.1 ab.2 := by
  induction k with
  | zero => exact ⟨le_max_left _ _, le_max_right _ _⟩
  | succ k ih =>
    rw [Function.iterate_succ_apply']
    obtain ⟨h1, h2⟩ := euclidStepVal_le_max (euclidStepVal^[k] ab)
    exact ⟨h1.trans (max_le ih.1 ih.2), h2.trans (max_le ih.1 ih.2)⟩

/-- The remainder of `b` by a nonzero `r ≤ b` is at most half of `b`. -/
theorem mod_le_half {b r : ℕ} (hr : 0 < r) (hrb : r ≤ b) : b % r ≤ b / 2 := by
  rcases le_or_gt r (b / 2) with h | h
  · exact (Nat.mod_lt b hr).le.trans h
  · rw [Nat.mod_eq_sub_mod hrb, Nat.mod_eq_of_lt (by omega)]
    omega

/-- Two Euclid steps at least halve the second component. -/
theorem euclidStepVal_two_steps_le (ab : ℕ × ℕ) :
    (euclidStepVal (euclidStepVal ab)).2 ≤ ab.2 / 2 := by
  obtain ⟨a, b⟩ := ab
  by_cases hb : b = 0
  · simp [euclidStepVal, hb]
  · have hstep : euclidStepVal (a, b) = (b, a % b) := by simp [euclidStepVal, hb]
    rw [hstep]
    by_cases hr : a % b = 0
    · simp [euclidStepVal, hr]
    · have h2 : euclidStepVal (b, a % b) = (a % b, b % (a % b)) := by simp [euclidStepVal, hr]
      rw [h2]
      exact mod_le_half (Nat.pos_of_ne_zero hr) (Nat.mod_lt a (Nat.pos_of_ne_zero hb)).le

/-- After `2k` Euclid steps the second component has been divided by at least `2 ^ k`. -/
theorem euclidStepVal_iterate_two_mul_le (ab : ℕ × ℕ) (k : ℕ) :
    (euclidStepVal^[2 * k] ab).2 ≤ ab.2 / 2 ^ k := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [show 2 * (k + 1) = 2 + 2 * k by ring, Function.iterate_add_apply]
    calc (euclidStepVal^[2] (euclidStepVal^[2 * k] ab)).2
        ≤ (euclidStepVal^[2 * k] ab).2 / 2 := euclidStepVal_two_steps_le _
      _ ≤ ab.2 / 2 ^ k / 2 := Nat.div_le_div_right ih
      _ = ab.2 / 2 ^ (k + 1) := by rw [Nat.div_div_eq_div_mul, pow_succ]

/-- After `2 (|a| + |b|) + 2` Euclid steps starting from `(decNat a, decNat b)`, the second
component is zero and the first is the gcd. -/
theorem euclidStepVal_iterate (a b : List Bool) :
    euclidStepVal^[2 * (a.length + b.length) + 2] (decNat a, decNat b) =
      (Nat.gcd (decNat a) (decNat b), 0) := by
  rw [show 2 * (a.length + b.length) + 2 = 2 * (a.length + b.length + 1) by ring]
  have h2 : (euclidStepVal^[2 * (a.length + b.length + 1)] (decNat a, decNat b)).2 = 0 := by
    have h := euclidStepVal_iterate_two_mul_le (decNat a, decNat b) (a.length + b.length + 1)
    have hlt : decNat b < 2 ^ (a.length + b.length + 1) :=
      (decNat_lt_two_pow_length b).trans_le (Nat.pow_le_pow_right (by norm_num) (by omega))
    rw [Nat.div_eq_of_lt hlt] at h
    exact Nat.le_zero.mp h
  refine Prod.ext ?_ h2
  have hg := euclidStepVal_iterate_gcd (decNat a, decNat b) (2 * (a.length + b.length + 1))
  rw [h2, Nat.gcd_zero_right] at hg
  exact hg

/-! ### The string iteration -/

/-- One Euclid step on string states `pair x y`: a fixed point once `y` denotes zero, otherwise
`pair y (canonBits (modBits x y))`. -/
def euclidStep (s : List Bool) : List Bool :=
  caseBit₀ (isZeroBits (pairSnd s)) s
    (pair (pairSnd s) (canonBits (modBits (pairFst s) (pairSnd s))))

/-- The string step simulates the value step on canonical pair states. -/
theorem euclidStep_pair_encNat (ab : ℕ × ℕ) :
    euclidStep (pair (encNat ab.1) (encNat ab.2)) =
      pair (encNat (euclidStepVal ab).1) (encNat (euclidStepVal ab).2) := by
  by_cases hq : ab.2 = 0
  · have h0 : isZeroBits (encNat 0) = [true] := (isZeroBits_eq_true_iff _).mpr (by simp)
    simp [euclidStep, euclidStepVal, hq, h0]
  · have h0 : isZeroBits (encNat ab.2) = [false] := by
      rcases isZeroBits_flag (encNat ab.2) with h | h
      · exact absurd ((isZeroBits_eq_true_iff _).mp h) (by simpa using hq)
      · exact h
    have hb : decNat (encNat ab.2) ≠ 0 := by simpa using hq
    simp [euclidStep, euclidStepVal, hq, h0, canonBits, decNat_modBits _ _ hb]

/-- The iterated string step simulates the iterated value step on canonical pair states. -/
theorem euclidStep_iterate_pair_encNat (ab : ℕ × ℕ) (k : ℕ) :
    euclidStep^[k] (pair (encNat ab.1) (encNat ab.2)) =
      pair (encNat (euclidStepVal^[k] ab).1) (encNat (euclidStepVal^[k] ab).2) := by
  induction k with
  | zero => rfl
  | succ k ih => rw [Function.iterate_succ_apply', ih, euclidStep_pair_encNat,
      Function.iterate_succ_apply']

/-- The canonical numeral of a value below `2 ^ n` has at most `n` bits. -/
theorem length_encNat_le_of_lt {m n : ℕ} (h : m < 2 ^ n) : (encNat m).length ≤ n := by
  rw [length_encNat]
  exact Nat.size_le.mpr h

/-- Every state of the string iteration started from `pair (canonBits a) (canonBits b)` is at most
`3 (|a| + |b|) + 2` bits long. -/
theorem length_euclidStep_iterate_le (a b : List Bool) (k : ℕ) :
    (euclidStep^[k] (pair (canonBits a) (canonBits b))).length ≤ 3 * (a.length + b.length) + 2 := by
  have hit := euclidStep_iterate_pair_encNat (decNat a, decNat b) k
  simp only [canonBits] at hit ⊢
  rw [hit, pair_length]
  obtain ⟨h1, h2⟩ := euclidStepVal_iterate_le_max (decNat a, decNat b) k
  have hmax : max (decNat a, decNat b).1 (decNat a, decNat b).2 < 2 ^ (a.length + b.length) := by
    refine max_lt ?_ ?_
    · exact (decNat_lt_two_pow_length a).trans_le (Nat.pow_le_pow_right (by norm_num) (by omega))
    · exact (decNat_lt_two_pow_length b).trans_le (Nat.pow_le_pow_right (by norm_num) (by omega))
  have e1 := length_encNat_le_of_lt (h1.trans_lt hmax)
  have e2 := length_encNat_le_of_lt (h2.trans_lt hmax)
  omega

/-- The gcd numeral: the first component of the string Euclid iteration, run for
`2 (|a| + |b|) + 2` steps from the canonical pair of the inputs. -/
def gcdBits (a b : List Bool) : List Bool :=
  pairFst (euclidStep^[2 * (a.length + b.length) + 2] (pair (canonBits a) (canonBits b)))

/-- `gcdBits` is the canonical numeral of the gcd. -/
theorem gcdBits_eq_encNat (a b : List Bool) :
    gcdBits a b = encNat (Nat.gcd (decNat a) (decNat b)) := by
  have hit := euclidStep_iterate_pair_encNat (decNat a, decNat b)
    (2 * (a.length + b.length) + 2)
  rw [euclidStepVal_iterate] at hit
  simp only [gcdBits, canonBits]
  rw [hit, pairFst_pair]

/-- `gcdBits` denotes the gcd. -/
theorem decNat_gcdBits (a b : List Bool) :
    decNat (gcdBits a b) = Nat.gcd (decNat a) (decNat b) := by
  rw [gcdBits_eq_encNat, decNat_encNat]

/-- The gcd numeral is no longer than the two inputs together (plus two). -/
theorem length_gcdBits_le (a b : List Bool) : (gcdBits a b).length ≤ a.length + b.length + 2 := by
  have hb : Nat.gcd (decNat a) (decNat b) ≤ decNat a + decNat b := by
    rcases Nat.eq_zero_or_pos (decNat a) with h | h
    · rw [h, Nat.gcd_zero_left]
      omega
    · exact (Nat.gcd_le_left _ h).trans (Nat.le_add_right _ _)
  have hlt : decNat a + decNat b < 2 ^ (a.length + b.length + 1) := by
    have ha := decNat_lt_two_pow_length a
    have hb' := decNat_lt_two_pow_length b
    have h1 : 2 ^ a.length ≤ 2 ^ (a.length + b.length) :=
      Nat.pow_le_pow_right (by norm_num) (by omega)
    have h2 : 2 ^ b.length ≤ 2 ^ (a.length + b.length) :=
      Nat.pow_le_pow_right (by norm_num) (by omega)
    rw [pow_succ]
    omega
  rw [gcdBits_eq_encNat]
  exact (length_encNat_le_of_lt (hb.trans_lt hlt)).trans (by omega)

/-- The string Euclid step is in Cobham's algebra (as a function of a Cobham argument). -/
theorem cobham_euclidStep_comp {n : ℕ} {g : (Fin n → List Bool) → List Bool} (hg : Cobham g) :
    Cobham fun v : Fin n → List Bool ↦ euclidStep (g v) :=
  Cobham.iteFn (cobham_isZeroBits_comp (cobham_pairSnd_comp hg)) hg
    (cobham_pair_comp (cobham_pairSnd_comp hg)
      (cobham_canonBits_comp
        (cobham_modBits_comp (cobham_pairFst_comp hg) (cobham_pairSnd_comp hg))))

/-- Euclid's algorithm is in Cobham's algebra. -/
theorem cobham_gcdBits : Cobham fun v : Fin 2 → List Bool ↦ gcdBits (v 0) (v 1) := by
  -- The initial state, the step and the ruler of the clocked iteration.
  have he : Cobham fun v : Fin 2 → List Bool ↦ pair (canonBits (v 0)) (canonBits (v 1)) :=
    cobham_pair_comp (cobham_canonBits_comp (.proj 0)) (cobham_canonBits_comp (.proj 1))
  have hf : Cobham fun w : Fin 3 → List Bool ↦ euclidStep (w 0) := cobham_euclidStep_comp (.proj 0)
  have hruler : Cobham fun v : Fin 2 → List Bool ↦ pair (v 0 ++ v 1) (v 0 ++ v 1) :=
    cobham_pair_comp (Cobham.appendFn (.proj 0) (.proj 1)) (Cobham.appendFn (.proj 0) (.proj 1))
  have hj : Cobham fun w : Fin 3 → List Bool ↦ pair (Fin.tail w 0 ++ Fin.tail w 1)
      (Fin.tail w 0 ++ Fin.tail w 1) :=
    (Cobham.comp hruler fun i ↦ Cobham.proj i.succ).of_eq fun _ ↦ rfl
  have hiter := Cobham.iterFn he hf hj (by
    intro c v
    simp only [Fin.tail_cons, Fin.cons_zero, pair_length, List.length_append]
    refine le_trans (length_euclidStep_iterate_le (v 0) (v 1) c.length) ?_
    omega)
  -- The clock: `(a ++ b) ++ (a ++ b) ++ [false, false]`, of length `2 (|a| + |b|) + 2`.
  have hclock : Cobham fun v : Fin 2 → List Bool ↦ (v 0 ++ v 1) ++ (v 0 ++ v 1) ++ [false, false] :=
    Cobham.appendFn (Cobham.appendFn (Cobham.appendFn (.proj 0) (.proj 1))
      (Cobham.appendFn (.proj 0) (.proj 1))) (Cobham.const [false, false])
  have hloop := Cobham.comp hiter
    (gs := fun i (v : Fin 2 → List Bool) ↦
      (Fin.cons ((v 0 ++ v 1) ++ (v 0 ++ v 1) ++ [false, false]) v : Fin 3 → List Bool) i)
    (by
      intro i
      refine Fin.cases ?_ (fun i ↦ ?_) i
      · exact hclock
      · exact Cobham.proj i)
  refine (cobham_pairFst_comp hloop).of_eq fun v ↦ ?_
  simp only [gcdBits, Fin.tail_cons, Fin.cons_zero, List.length_append, List.length_cons,
    List.length_nil]
  congr 3
  ring

/-- Composition form. -/
theorem cobham_gcdBits_comp {n : ℕ} {g₀ g₁ : (Fin n → List Bool) → List Bool}
    (h₀ : Cobham g₀) (h₁ : Cobham g₁) :
    Cobham fun v : Fin n → List Bool ↦ gcdBits (g₀ v) (g₁ v) :=
  (Cobham.comp₂ cobham_gcdBits h₀ h₁).of_eq fun v ↦ by simp

end SparseDiv.StringArith
