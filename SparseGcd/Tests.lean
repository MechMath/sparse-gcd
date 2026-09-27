import SparseGcd.Cnf.Reduce
import SparseGcd.Field.Construction
import SparseGcd.Instances
import SparseGcd.Machine.TrialData

/-!
# Small-instance sanity tests (not part of any proof)

Data-level checks of polarity, encoding round trips and boundary cases by `decide`/`rfl`.
The tiny field is `𝔽_7` with Boolean primes `ℓ = [2, 3]`, `E = 6`, `ω = 3` (order 6).
-/

open Complexity SAT SparseDiv

namespace SparseGcd.Tests

/-! ### CNF gadgets -/

-- parity constraint `x₀ ⊕ x₁ = 1` with one auxiliary variable `y = x₀ ⊕ x₁`: exactly two solutions
example : (solutions (parityCnf 2 [0, 1] true).1 3).card = 2 := by decide
-- the same with target `0`
example : (solutions (parityCnf 2 [0, 1] false).1 3).card = 2 := by decide
-- empty selection: `false = true` is the empty clause, `false = false` is trivial
example : parityCnf 5 [] true = ([[]], 0) := rfl
example : parityCnf 5 [] false = ([], 0) := rfl
-- single variable: a unit clause
example : parityCnf 5 [2] false = ([[⟨false, 2⟩]], 0) := rfl
-- long clause conversion preserves the exact count (15 of 16 assignments satisfy a 4-clause)
example : (solutions (shortenClause 4 [⟨true, 0⟩, ⟨true, 1⟩, ⟨true, 2⟩, ⟨true, 3⟩]).1 6).card = 15 := by
  decide
example : (solutions [[⟨true, 0⟩, ⟨true, 1⟩, ⟨true, 2⟩, ⟨true, 3⟩]] 4).card = 15 := by decide
-- short clauses are untouched
example : shortenClause 3 [⟨true, 0⟩, ⟨false, 1⟩] = ([[⟨true, 0⟩, ⟨false, 1⟩]], 0) := rfl
-- the empty clause stays unsatisfiable through isolation
example : solutions (isolate [[]] [[true, false], [false, true]]).1 (isolate [[]] [[true, false], [false, true]]).2 = ∅ := by
  decide
-- `chooseK` boundaries (`m₀ = 3`: valid range `1..5`)
example : chooseK 3 (encNat 0) = 1 := by decide
example : chooseK 3 (encNat 1) = 1 := by decide
example : chooseK 3 (encNat 5) = 5 := by decide
example : chooseK 3 (encNat 6) = 1 := by decide

/-! ### Field data on `𝔽_7`, `ℓ = [2,3]`, `E = 6`, `ω = 3` -/

example : orderTestNat 7 6 [2, 3] 3 = true := by decide
-- `ω = 2` has order 3, not 6
example : orderTestNat 7 6 [2, 3] 2 = false := by decide
-- `ω = 6 = -1` has order 2
example : orderTestNat 7 6 [2, 3] 6 = false := by decide

/-- Evaluate a term list at a residue. -/
def evalTerms (p : ℕ) (l : Terms) (x : ℕ) : ℕ := (l.map fun t ↦ t.1 * x ^ t.2).sum % p

-- the assignment `(x₀, x₁) = (true, false)` has CRT residue `a = 3` (`3 ≡ 1 mod 2`, `3 ≡ 0 mod 3`),
-- root `ω^3 = 6`
example : powMod 3 3 7 = 6 := by decide
-- `R(6) = 0`
example : evalTerms 7 (rawRterms 7 6) 6 = 0 := by decide
-- positive literal `x₀` (true) vanishes, negative literal `¬x₀` does not
example : evalTerms 7 (rawLitTerms 7 6 [2, 3] 3 ⟨true, 0⟩) 6 = 0 := by decide
example : evalTerms 7 (rawLitTerms 7 6 [2, 3] 3 ⟨false, 0⟩) 6 ≠ 0 := by decide
-- negative literal `¬x₁` (x₁ false) vanishes, positive does not
example : evalTerms 7 (rawLitTerms 7 6 [2, 3] 3 ⟨false, 1⟩) 6 = 0 := by decide
example : evalTerms 7 (rawLitTerms 7 6 [2, 3] 3 ⟨true, 1⟩) 6 ≠ 0 := by decide
-- both `B_i` vanish on a Boolean root
example : evalTerms 7 (rawBterms 7 6 [2, 3] 3 0) 6 = 0 := by decide
example : evalTerms 7 (rawBterms 7 6 [2, 3] 3 1) 6 = 0 := by decide
-- the non-Boolean root `ω^5 = 5` (`5 ≡ 2 mod 3`) is killed by `B_1`
example : powMod 3 5 7 = 5 := by decide
example : evalTerms 7 (rawBterms 7 6 [2, 3] 3 1) 5 ≠ 0 := by decide
-- clause `(x₀ ∨ x₁)` is satisfied by `(true, false)`: its polynomial vanishes at `6`
example : evalTerms 7 (rawClauseTerms 7 6 [2, 3] 3 [⟨true, 0⟩, ⟨true, 1⟩]) 6 = 0 := by decide
-- clause `(¬x₀ ∨ x₁)` is falsified by `(true, false)`: nonzero at `6`
example : evalTerms 7 (rawClauseTerms 7 6 [2, 3] 3 [⟨false, 0⟩, ⟨true, 1⟩]) 6 ≠ 0 := by decide
-- the empty clause polynomial is the constant `1`
example : rawClauseTerms 7 6 [2, 3] 3 [] = [(1, 0)] := rfl
-- support bounds of a 3-clause: `2^3 = 8` products
example : (rawClauseTerms 7 6 [2, 3] 3 [⟨true, 0⟩, ⟨true, 1⟩, ⟨false, 0⟩]).length = 8 := by decide

/-! ### Encodings -/

example : decPackage (encPackage [2, 3] 1) = some ([2, 3], 1) := by decide
example : decRouInstance (encRouInstance 7 [(1, 3), (1, 0)] 6) = some (7, [(1, 3), (1, 0)], 6) := by decide
example : decDivInstance (encDivInstance 7 [(6, 0), (1, 6)] [(1, 3), (1, 0)]) =
    some (7, [(6, 0), (1, 6)], [(1, 3), (1, 0)]) := by decide
-- a malformed instance decodes to nothing
example : decRouInstance [true, true, false] = none := by decide

/-! ### Parameters -/

example : A 0 = 64 := rfl
example : r 0 = 512 := rfl
example : 400 * r 0 < 2 ^ cnt 0 := by decide
example : 4 ≤ Nn 0 := by decide

end SparseGcd.Tests
