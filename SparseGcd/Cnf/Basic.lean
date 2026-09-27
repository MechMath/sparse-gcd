import Complexitylib.SAT.Semantics
import Complexitylib.SAT.Rename
import Complexitylib.SAT.ThreeCNF
import Complexitylib.Circuits.BitString
import Mathlib.Data.Fintype.Pi

/-!
# CNF formulas over a declared number of variables

Complexitylib's `SAT.CNF` uses arbitrary variable indices and assignments of arbitrary length
(out-of-range reads are `false`). The paper's promise problems count satisfying assignments over a
declared set of `n` variables, so we work with `BitString n := Fin n → Bool` and the total
function view `ℕ → Bool` (`patch`, `evalF`).

* `CNF.VarsLt φ n` — every variable of `φ` is `< n`.
* `BoundedClauses φ` — every clause has at most three literals.
* `solutions φ n` — the satisfying `BitString n`s; `UniqueSat φ n` — exactly one.
-/

open Complexity SAT

namespace SparseGcd

/-- The assignment (list) of a bit vector. -/
def assignOf {n : ℕ} (α : BitString n) : Assignment := List.ofFn α

/-- Total-function view of a bit vector (out of range = `false`). -/
def toFun {n : ℕ} (α : BitString n) : ℕ → Bool := fun i ↦ if h : i < n then α ⟨i, h⟩ else false

/-- Overwrite the window `[t, t + a)` of `g` with `β`. -/
def patch (g : ℕ → Bool) (t : ℕ) {a : ℕ} (β : BitString a) : ℕ → Bool :=
  fun i ↦ if h : t ≤ i ∧ i < t + a then β ⟨i - t, by omega⟩ else g i

/-- Literal evaluation against a total function. -/
def Lit.evalF (g : ℕ → Bool) (ℓ : Lit) : Bool := g ℓ.var == ℓ.sign

/-- Clause evaluation against a total function. -/
def Clause.evalF (g : ℕ → Bool) (c : Clause) : Bool := c.any (Lit.evalF g)

/-- CNF evaluation against a total function. -/
def CNF.evalF (g : ℕ → Bool) (φ : CNF) : Bool := φ.all (Clause.evalF g)

/-- All variables of `φ` are below `n`. -/
def CNF.VarsLt (φ : CNF) (n : ℕ) : Prop := ∀ c ∈ φ, ∀ ℓ ∈ c, ℓ.var < n

instance (φ : CNF) (n : ℕ) : Decidable (CNF.VarsLt φ n) := by unfold CNF.VarsLt; infer_instance

/-- Every clause has at most three literals ("clause size at most three"). -/
def BoundedClauses (φ : CNF) : Prop := ∀ c ∈ φ, c.length ≤ 3

instance (φ : CNF) : Decidable (BoundedClauses φ) := by unfold BoundedClauses; infer_instance

/-- Satisfying bit vectors of length `n`. -/
def solutions (φ : CNF) (n : ℕ) : Finset (BitString n) :=
  Finset.univ.filter fun α ↦ CNF.eval (assignOf α) φ = true

/-- Exactly one satisfying assignment over the declared `n` variables. -/
def UniqueSat (φ : CNF) (n : ℕ) : Prop := (solutions φ n).card = 1

theorem get_assignOf {n : ℕ} (α : BitString n) (i : ℕ) :
    (assignOf α).get i = toFun α i := by
  unfold assignOf Assignment.get toFun
  by_cases h : i < n <;> simp [h]

theorem Lit_eval_eq_evalF {n : ℕ} (α : BitString n) (ℓ : Lit) :
    Lit.eval (assignOf α) ℓ = Lit.evalF (toFun α) ℓ := by
  simp [Lit.eval, Lit.evalF, get_assignOf]

theorem CNF_eval_eq_evalF {n : ℕ} (α : BitString n) (φ : CNF) :
    CNF.eval (assignOf α) φ = CNF.evalF (toFun α) φ := by
  have h : Lit.eval (assignOf α) = Lit.evalF (toFun α) := funext (Lit_eval_eq_evalF α)
  show φ.all (fun c ↦ c.any (Lit.eval (assignOf α))) =
    φ.all (fun c ↦ c.any (Lit.evalF (toFun α)))
  rw [h]

/-- `evalF` only reads the variables actually occurring. -/
theorem CNF.evalF_congr {φ : CNF} {g g' : ℕ → Bool}
    (h : ∀ c ∈ φ, ∀ ℓ ∈ c, g ℓ.var = g' ℓ.var) : CNF.evalF g φ = CNF.evalF g' φ := by
  apply Bool.eq_iff_iff.mpr
  simp only [CNF.evalF, Clause.evalF, Lit.evalF, List.all_eq_true, List.any_eq_true]
  constructor
  · intro H c hc
    obtain ⟨ℓ, hℓ, hℓ'⟩ := H c hc
    exact ⟨ℓ, hℓ, by rwa [h c hc ℓ hℓ] at hℓ'⟩
  · intro H c hc
    obtain ⟨ℓ, hℓ, hℓ'⟩ := H c hc
    exact ⟨ℓ, hℓ, by rwa [h c hc ℓ hℓ]⟩

theorem CNF.evalF_append (g : ℕ → Bool) (φ ψ : CNF) :
    CNF.evalF g (φ ++ ψ) = (CNF.evalF g φ && CNF.evalF g ψ) := by
  simp [CNF.evalF, List.all_append]

theorem mem_solutions {φ : CNF} {n : ℕ} {α : BitString n} :
    α ∈ solutions φ n ↔ CNF.evalF (toFun α) φ = true := by
  simp [solutions, CNF_eval_eq_evalF]

/-- Any assignment can be truncated/extended to `n` bits without changing the value when all
variables are below `n`. -/
theorem CNF.eval_eq_eval_assignOf {φ : CNF} {n : ℕ} (h : CNF.VarsLt φ n) (a : Assignment) :
    CNF.eval a φ = CNF.eval (assignOf (fun i : Fin n ↦ a.get i)) φ := by
  rw [CNF_eval_eq_evalF]
  have e : CNF.eval a φ = CNF.evalF a.get φ := rfl
  rw [e]
  apply CNF.evalF_congr
  intro c hc ℓ hℓ
  simp [toFun, h c hc ℓ hℓ]

theorem satisfiable_iff_solutions_nonempty {φ : CNF} {n : ℕ} (h : CNF.VarsLt φ n) :
    φ.Satisfiable ↔ (solutions φ n).Nonempty := by
  constructor
  · rintro ⟨a, ha⟩
    refine ⟨fun i ↦ a.get i, ?_⟩
    simp only [solutions, Finset.mem_filter, Finset.mem_univ, true_and]
    rwa [← CNF.eval_eq_eval_assignOf h]
  · rintro ⟨α, hα⟩
    simp only [solutions, Finset.mem_filter, Finset.mem_univ, true_and] at hα
    exact ⟨assignOf α, hα⟩

theorem not_satisfiable_iff_solutions_eq_empty {φ : CNF} {n : ℕ} (h : CNF.VarsLt φ n) :
    ¬ φ.Satisfiable ↔ solutions φ n = ∅ := by
  rw [satisfiable_iff_solutions_nonempty h, Finset.not_nonempty_iff_eq_empty]

theorem UniqueSat.satisfiable {φ : CNF} {n : ℕ} (h : CNF.VarsLt φ n) (hu : UniqueSat φ n) :
    φ.Satisfiable := by
  rw [satisfiable_iff_solutions_nonempty h, ← Finset.card_pos, hu]
  exact Nat.one_pos

/-- `maxVar + 1` bounds every variable. -/
theorem varsLt_maxVar_succ (φ : CNF) : CNF.VarsLt φ (φ.maxVar + 1) := by
  intro c hc ℓ hℓ
  have h₁ := Clause.var_le_maxVar hℓ
  have h₂ := CNF.clause_maxVar_le_maxVar hc
  omega

theorem VarsLt.mono {φ : CNF} {n n' : ℕ} (h : CNF.VarsLt φ n) (hn : n ≤ n') : CNF.VarsLt φ n' :=
  fun c hc ℓ hℓ ↦ lt_of_lt_of_le (h c hc ℓ hℓ) hn

theorem VarsLt.append {φ ψ : CNF} {n : ℕ} (h₁ : CNF.VarsLt φ n) (h₂ : CNF.VarsLt ψ n) :
    CNF.VarsLt (φ ++ ψ) n := by
  intro c hc ℓ hℓ
  rcases List.mem_append.mp hc with hc | hc
  · exact h₁ c hc ℓ hℓ
  · exact h₂ c hc ℓ hℓ

theorem BoundedClauses.append {φ ψ : CNF} (h₁ : BoundedClauses φ) (h₂ : BoundedClauses ψ) :
    BoundedClauses (φ ++ ψ) := by
  intro c hc
  rcases List.mem_append.mp hc with hc | hc
  · exact h₁ c hc
  · exact h₂ c hc

theorem patch_of_lt (g : ℕ → Bool) (t : ℕ) {a : ℕ} (β : BitString a) {i : ℕ} (hi : i < t) :
    patch g t β i = g i := by
  unfold patch
  rw [dite_eq_right (by omega)]

theorem patch_of_ge (g : ℕ → Bool) (t : ℕ) {a : ℕ} (β : BitString a) {i : ℕ} (hi : t + a ≤ i) :
    patch g t β i = g i := by
  unfold patch
  rw [dite_eq_right (by omega)]

theorem patch_window (g : ℕ → Bool) (t : ℕ) {a : ℕ} (β : BitString a) (j : Fin a) :
    patch g t β (t + j) = β j := by
  have hj := j.isLt
  unfold patch
  rw [dite_eq_left ⟨by omega, by omega⟩]
  congr 1
  ext
  simp

/-- Patching consecutive windows. -/
theorem patch_append (g : ℕ → Bool) (t : ℕ) {a b : ℕ} (β : BitString a) (γ : BitString b) :
    patch g t (Fin.append β γ) = patch (patch g t β) (t + a) γ := by
  funext i
  unfold patch
  by_cases h1 : t ≤ i ∧ i < t + (a + b)
  · rw [dite_eq_left h1]
    by_cases h2 : t + a ≤ i ∧ i < t + a + b
    · rw [dite_eq_left h2]
      have e : (⟨i - t, by omega⟩ : Fin (a + b)) = Fin.natAdd a ⟨i - (t + a), by omega⟩ := by
        ext; simp; omega
      rw [e, Fin.append_right]
    · rw [dite_eq_right h2, dite_eq_left ⟨h1.1, by omega⟩]
      have e : (⟨i - t, by omega⟩ : Fin (a + b)) = Fin.castAdd b ⟨i - t, by omega⟩ := by
        ext; simp
      rw [e, Fin.append_left]
  · rw [dite_eq_right h1, dite_eq_right (by omega), dite_eq_right (by omega)]

/-- The total function of a concatenated bit vector is a patch. -/
theorem toFun_append {n a : ℕ} (α : BitString n) (β : BitString a) :
    toFun (Fin.append α β) = patch (toFun α) n β := by
  funext i
  dsimp only [toFun, patch]
  by_cases h1 : i < n
  · rw [dite_eq_left (by omega), dite_eq_right (by omega), dite_eq_left h1]
    have e : (⟨i, by omega⟩ : Fin (n + a)) = Fin.castAdd a ⟨i, h1⟩ := rfl
    rw [e, Fin.append_left]
  · by_cases h2 : i < n + a
    · rw [dite_eq_left h2, dite_eq_left ⟨by omega, h2⟩]
      have e : (⟨i, h2⟩ : Fin (n + a)) = Fin.natAdd n ⟨i - n, by omega⟩ := by
        ext; simp; omega
      rw [e, Fin.append_right]
    · rw [dite_eq_right h2, dite_eq_right (by omega), dite_eq_right h1]

end SparseGcd
