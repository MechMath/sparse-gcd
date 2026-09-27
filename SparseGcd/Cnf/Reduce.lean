import SparseGcd.Cnf.Gadgets
import SparseGcd.Cnf.Isolation
import SparseGcd.Basic.Seeds
import SparseGcd.Basic.Bernoulli
import SparseGcd.Field.Sampling
import SparseDivComplexity.Encoding
import Complexitylib.SAT.Encoding

/-!
# The isolation reduction at the data level (Lemma 13 / Lemma 21)

`isolate φ rows` converts every clause of `φ` parsimoniously into clauses of size at most three
(`shortenAll`), then adds, for every hash row, the parsimonious parity constraint
`⊕_{j ∈ row} y_j = target(row)` (`isolateRows`). The output is a formula `ψ` together with its
number of variables `n'` (original variables `< m₀ = maxVar φ + 1`, auxiliaries `≥ m₀`).

Random choices: `k` is read from `Nat.size (m₀ + 2)` bits and the `k` hash rows from the first
`k (m₀+1)` bits of a block of `(m₀+2)(m₀+1)` bits (the affine family with an explicit offset
column and target cell `0`).

Results: unsatisfiable inputs give unsatisfiable outputs for every seed; satisfiable inputs
give a uniquely satisfiable output with probability at least `1 / (16 (m₀ + 3))`.
-/

open Complexity SAT Finset

namespace SparseGcd

/-- Parsimonious conversion of all clauses, threading the next free variable. -/
def shortenAll : ℕ → CNF → CNF × ℕ
  | t, [] => ([], t)
  | t, c :: cs =>
    let r := shortenClause t c
    let rest := shortenAll (t + r.2) cs
    (r.1 ++ rest.1, rest.2)

/-- The selected variables and the target bit of a hash row (`m₀` data columns, then the offset). -/
def rowOfList (m₀ : ℕ) (row : List Bool) : List ℕ × Bool :=
  ((List.range m₀).filter fun j ↦ row.getD j false, row.getD m₀ false)

/-- Parity constraints for all rows, threading the next free variable. -/
def isolateRows (m₀ : ℕ) : ℕ → List (List Bool) → CNF × ℕ
  | t, [] => ([], t)
  | t, row :: rows =>
    let xb := rowOfList m₀ row
    let r := parityCnf t xb.1 xb.2
    let rest := isolateRows m₀ (t + r.2) rows
    (r.1 ++ rest.1, rest.2)

/-- **The isolation map**: `(ψ, n')`. -/
def isolate (φ : CNF) (rows : List (List Bool)) : CNF × ℕ :=
  let m₀ := φ.maxVar + 1
  let s := shortenAll m₀ φ
  let r := isolateRows m₀ s.2 rows
  (s.1 ++ r.1, r.2)

/-- Read `k` from a bit block: `k ∈ [1, m₀ + 2]`, defaulting to `1`. -/
def chooseK (m₀ : ℕ) (bits : List Bool) : ℕ :=
  let j := SparseDiv.decNat bits
  if 1 ≤ j ∧ j ≤ m₀ + 2 then j else 1

/-- The `k` rows of width `m₀ + 1` read from a bit block (row-major). -/
def hashRows (m₀ k : ℕ) (bits : List Bool) : List (List Bool) :=
  (List.range k).map fun i ↦ (bits.drop (i * (m₀ + 1))).take (m₀ + 1)

/-- Number of `k`-bits and hash bits used for a formula with `m₀` variables. -/
def kBits (m₀ : ℕ) : ℕ := Nat.size (m₀ + 2)
def hashBits (m₀ : ℕ) : ℕ := (m₀ + 2) * (m₀ + 1)

/-- The isolation map on the seed `kbits ++ hbits`. -/
def isolateSeed (φ : CNF) (kbits hbits : List Bool) : CNF × ℕ :=
  isolate φ (hashRows (φ.maxVar + 1) (chooseK (φ.maxVar + 1) kbits) hbits)

/-! ### Transport helpers for `WindowExt` -/

private theorem windowExt_congr_pred {ψ : CNF} {t a : ℕ} {P Q : (ℕ → Bool) → Prop}
    (h : WindowExt ψ t a P) (hPQ : ∀ g, P g ↔ Q g) : WindowExt ψ t a Q := by
  have e : P = Q := funext fun g ↦ propext (hPQ g)
  subst e
  exact h

private theorem windowExt_cast_a {ψ : CNF} {t a a' : ℕ} {P : (ℕ → Bool) → Prop}
    (h : WindowExt ψ t a P) (e : a = a') : WindowExt ψ t a' P := e ▸ h

private theorem windowExt_cast_t {ψ : CNF} {t t' a : ℕ} {P : (ℕ → Bool) → Prop}
    (h : WindowExt ψ t a P) (e : t = t') : WindowExt ψ t' a P := e ▸ h

private theorem windowExt_nil (t : ℕ) : WindowExt [] t 0 (fun _ ↦ True) :=
  windowExt_congr_pred (windowExt_plain (ψ := []) (t := t) fun c hc ↦ by simp at hc)
    fun g ↦ by simp [CNF.evalF]

/-! ### Structural properties -/

theorem shortenAll_boundedClauses (t : ℕ) (φ : CNF) : BoundedClauses (shortenAll t φ).1 := by
  induction φ generalizing t with
  | nil => intro c hc; simp [shortenAll] at hc
  | cons c cs ih => exact BoundedClauses.append (shortenClause_boundedClauses t c) (ih _)

theorem shortenAll_snd_ge (t : ℕ) (φ : CNF) : t ≤ (shortenAll t φ).2 := by
  induction φ generalizing t with
  | nil => exact le_rfl
  | cons c cs ih => exact le_trans (Nat.le_add_right _ _) (ih _)

/-- Total number of literals. -/
def CNF.numLits (φ : CNF) : ℕ := (φ.map List.length).sum

theorem numLits_nil : CNF.numLits [] = 0 := rfl

theorem numLits_cons (c : Clause) (cs : CNF) : CNF.numLits (c :: cs) = c.length + CNF.numLits cs := by
  simp [CNF.numLits]

theorem shortenAll_snd_le (t : ℕ) (φ : CNF) : (shortenAll t φ).2 ≤ t + CNF.numLits φ := by
  induction φ generalizing t with
  | nil => simp [shortenAll, numLits_nil]
  | cons c cs ih =>
    have h1 := shortenClause_aux_le t c
    have h2 := ih (t + (shortenClause t c).2)
    rw [numLits_cons]
    show (shortenAll (t + (shortenClause t c).2) cs).2 ≤ _
    omega

theorem shortenAll_length_le (t : ℕ) (φ : CNF) :
    (shortenAll t φ).1.length ≤ 3 * CNF.numLits φ + φ.length := by
  induction φ generalizing t with
  | nil => simp [shortenAll, numLits_nil]
  | cons c cs ih =>
    have h1 := shortenClause_length_le t c
    have h2 := ih (t + (shortenClause t c).2)
    rw [numLits_cons, List.length_cons]
    show ((shortenClause t c).1 ++ (shortenAll (t + (shortenClause t c).2) cs).1).length ≤ _
    rw [List.length_append]
    omega

private theorem varsLt_cons_head {c : Clause} {cs : CNF} {t : ℕ} (h : CNF.VarsLt (c :: cs) t) :
    ∀ ℓ ∈ c, ℓ.var < t :=
  h c (List.mem_cons_self ..)

private theorem varsLt_cons_tail {c : Clause} {cs : CNF} {t : ℕ} (h : CNF.VarsLt (c :: cs) t) :
    CNF.VarsLt cs t :=
  fun c' hc' ↦ h c' (List.mem_cons_of_mem _ hc')

theorem shortenAll_varsLt (t : ℕ) {φ : CNF} (hφ : CNF.VarsLt φ t) :
    CNF.VarsLt (shortenAll t φ).1 (shortenAll t φ).2 := by
  induction φ generalizing t with
  | nil => intro c hc; simp [shortenAll] at hc
  | cons c cs ih =>
    apply VarsLt.append
    · exact VarsLt.mono (shortenClause_varsLt t c (varsLt_cons_head hφ)) (shortenAll_snd_ge _ _)
    · exact ih _ (VarsLt.mono (varsLt_cons_tail hφ) (Nat.le_add_right _ _))

private theorem dependsBelow_evalF {φ : CNF} {t : ℕ} (hφ : CNF.VarsLt φ t) :
    DependsBelow t (fun g ↦ CNF.evalF g φ = true) := by
  intro g g' hg
  show CNF.evalF g φ = true ↔ CNF.evalF g' φ = true
  rw [CNF.evalF_congr fun c hc ℓ hℓ ↦ hg _ (hφ c hc ℓ hℓ)]

theorem shortenAll_windowExt (t : ℕ) {φ : CNF} (hφ : CNF.VarsLt φ t) :
    WindowExt (shortenAll t φ).1 t ((shortenAll t φ).2 - t) (fun g ↦ CNF.evalF g φ = true) := by
  induction φ generalizing t with
  | nil =>
    show WindowExt [] t (t - t) _
    rw [Nat.sub_self]
    exact windowExt_congr_pred (windowExt_nil t) fun g ↦ by simp [CNF.evalF]
  | cons c cs ih =>
    have h₁ := windowExt_shortenClause t c (varsLt_cons_head hφ)
    have h₂ := ih _ (VarsLt.mono (varsLt_cons_tail hφ) (Nat.le_add_right t (shortenClause t c).2))
    have h := WindowExt.append h₁ h₂ (dependsBelow_evalF (varsLt_cons_tail hφ))
    have hge := shortenAll_snd_ge (t + (shortenClause t c).2) cs
    show WindowExt ((shortenClause t c).1 ++ (shortenAll (t + (shortenClause t c).2) cs).1) t
      ((shortenAll (t + (shortenClause t c).2) cs).2 - t) _
    refine windowExt_congr_pred (windowExt_cast_a h (by omega)) fun g ↦ ?_
    simp [CNF.evalF]

theorem rowOfList_fst_lt (m₀ : ℕ) (row : List Bool) : ∀ x ∈ (rowOfList m₀ row).1, x < m₀ := by
  intro x hx
  simp only [rowOfList, List.mem_filter, List.mem_range] at hx
  exact hx.1

theorem rowOfList_fst_length_le (m₀ : ℕ) (row : List Bool) : (rowOfList m₀ row).1.length ≤ m₀ :=
  (List.length_filter_le _ _).trans (by simp)

theorem isolateRows_boundedClauses (m₀ t : ℕ) (rows : List (List Bool)) :
    BoundedClauses (isolateRows m₀ t rows).1 := by
  induction rows generalizing t with
  | nil => intro c hc; simp [isolateRows] at hc
  | cons row rows ih => exact BoundedClauses.append (parityCnf_boundedClauses _ _ _) (ih _)

theorem isolateRows_snd_ge (m₀ t : ℕ) (rows : List (List Bool)) : t ≤ (isolateRows m₀ t rows).2 := by
  induction rows generalizing t with
  | nil => exact le_rfl
  | cons row rows ih => exact le_trans (Nat.le_add_right _ _) (ih _)

/-- The number of auxiliaries of one row is at most `m₀`. -/
private theorem parityCnf_row_aux_le (m₀ t : ℕ) (row : List Bool) :
    (parityCnf t (rowOfList m₀ row).1 (rowOfList m₀ row).2).2 ≤ m₀ :=
  (parityCnf_aux_le _ _ _).trans (rowOfList_fst_length_le m₀ row)

theorem isolateRows_snd_le (m₀ t : ℕ) (rows : List (List Bool)) :
    (isolateRows m₀ t rows).2 ≤ t + rows.length * m₀ := by
  induction rows generalizing t with
  | nil => simp [isolateRows]
  | cons row rows ih =>
    have h1 := parityCnf_row_aux_le m₀ t row
    have h2 := ih (t + (parityCnf t (rowOfList m₀ row).1 (rowOfList m₀ row).2).2)
    rw [List.length_cons, Nat.succ_mul]
    show (isolateRows m₀ (t + (parityCnf t (rowOfList m₀ row).1 (rowOfList m₀ row).2).2) rows).2 ≤ _
    omega

theorem isolateRows_length_le (m₀ t : ℕ) (rows : List (List Bool)) :
    (isolateRows m₀ t rows).1.length ≤ rows.length * (4 * m₀ + 1) := by
  induction rows generalizing t with
  | nil => simp [isolateRows]
  | cons row rows ih =>
    have h1 := parityCnf_length_le t (rowOfList m₀ row).1 (rowOfList m₀ row).2
    have h1' := rowOfList_fst_length_le m₀ row
    have h2 := ih (t + (parityCnf t (rowOfList m₀ row).1 (rowOfList m₀ row).2).2)
    rw [List.length_cons, Nat.succ_mul]
    show ((parityCnf t (rowOfList m₀ row).1 (rowOfList m₀ row).2).1 ++
      (isolateRows m₀ (t + (parityCnf t (rowOfList m₀ row).1 (rowOfList m₀ row).2).2) rows).1).length ≤ _
    rw [List.length_append]
    omega

private theorem rowOfList_fst_lt_of_le {m₀ t : ℕ} (hm : m₀ ≤ t) (row : List Bool) :
    ∀ x ∈ (rowOfList m₀ row).1, x < t :=
  fun x hx ↦ lt_of_lt_of_le (rowOfList_fst_lt m₀ row x hx) hm

theorem isolateRows_varsLt (m₀ t : ℕ) (hm : m₀ ≤ t) (rows : List (List Bool)) :
    CNF.VarsLt (isolateRows m₀ t rows).1 (isolateRows m₀ t rows).2 := by
  induction rows generalizing t with
  | nil => intro c hc; simp [isolateRows] at hc
  | cons row rows ih =>
    apply VarsLt.append
    · exact VarsLt.mono (parityCnf_varsLt t _ _ (rowOfList_fst_lt_of_le hm row))
        (isolateRows_snd_ge _ _ _)
    · exact ih _ (by omega)

/-- The parity predicate of a list of rows. -/
def rowsHold (m₀ : ℕ) (rows : List (List Bool)) (g : ℕ → Bool) : Prop :=
  ∀ row ∈ rows, rowParity g (rowOfList m₀ row).1 = (rowOfList m₀ row).2

private theorem rowParity_congr' {g g' : ℕ → Bool} {xs : List ℕ} (h : ∀ x ∈ xs, g x = g' x) :
    rowParity g xs = rowParity g' xs := by
  unfold rowParity
  exact List.foldl_ext _ _ _ fun b x hx ↦ by rw [h x hx]

theorem rowsHold_nil (m₀ : ℕ) (g : ℕ → Bool) : rowsHold m₀ [] g := by
  simp [rowsHold]

theorem rowsHold_cons (m₀ : ℕ) (row : List Bool) (rows : List (List Bool)) (g : ℕ → Bool) :
    rowsHold m₀ (row :: rows) g ↔
      rowParity g (rowOfList m₀ row).1 = (rowOfList m₀ row).2 ∧ rowsHold m₀ rows g := by
  simp [rowsHold]

private theorem dependsBelow_rowsHold {m₀ t : ℕ} (hm : m₀ ≤ t) (rows : List (List Bool)) :
    DependsBelow t (rowsHold m₀ rows) := by
  intro g g' hg
  unfold rowsHold
  refine forall_congr' fun row ↦ imp_congr_right fun _ ↦ ?_
  rw [rowParity_congr' fun x hx ↦ hg x (rowOfList_fst_lt_of_le hm row x hx)]

theorem isolateRows_windowExt (m₀ t : ℕ) (hm : m₀ ≤ t) (rows : List (List Bool)) :
    WindowExt (isolateRows m₀ t rows).1 t ((isolateRows m₀ t rows).2 - t) (rowsHold m₀ rows) := by
  induction rows generalizing t with
  | nil =>
    show WindowExt [] t (t - t) _
    rw [Nat.sub_self]
    exact windowExt_congr_pred (windowExt_nil t) fun g ↦ by simp [rowsHold]
  | cons row rows ih =>
    have h₁ := windowExt_parityCnf t (rowOfList m₀ row).1 (rowOfList m₀ row).2
      (rowOfList_fst_lt_of_le hm row)
    have h₂ := ih (t + (parityCnf t (rowOfList m₀ row).1 (rowOfList m₀ row).2).2) (by omega)
    have h := WindowExt.append h₁ h₂ (dependsBelow_rowsHold hm rows)
    have hge := isolateRows_snd_ge m₀ (t + (parityCnf t (rowOfList m₀ row).1 (rowOfList m₀ row).2).2) rows
    show WindowExt ((parityCnf t (rowOfList m₀ row).1 (rowOfList m₀ row).2).1 ++
      (isolateRows m₀ (t + (parityCnf t (rowOfList m₀ row).1 (rowOfList m₀ row).2).2) rows).1) t
      ((isolateRows m₀ (t + (parityCnf t (rowOfList m₀ row).1 (rowOfList m₀ row).2).2) rows).2 - t) _
    refine windowExt_congr_pred (windowExt_cast_a h (by omega)) fun g ↦ ?_
    rw [rowsHold_cons]
    rfl

theorem isolate_boundedClauses (φ : CNF) (rows : List (List Bool)) :
    BoundedClauses (isolate φ rows).1 :=
  BoundedClauses.append (shortenAll_boundedClauses _ _) (isolateRows_boundedClauses _ _ _)

theorem isolate_varsLt (φ : CNF) (rows : List (List Bool)) :
    CNF.VarsLt (isolate φ rows).1 (isolate φ rows).2 :=
  VarsLt.append (VarsLt.mono (shortenAll_varsLt _ (varsLt_maxVar_succ φ)) (isolateRows_snd_ge _ _ _))
    (isolateRows_varsLt _ _ (shortenAll_snd_ge _ _) _)

theorem isolate_snd_ge (φ : CNF) (rows : List (List Bool)) : φ.maxVar + 1 ≤ (isolate φ rows).2 :=
  (shortenAll_snd_ge _ _).trans (isolateRows_snd_ge _ _ _)

theorem isolate_snd_le (φ : CNF) (rows : List (List Bool)) :
    (isolate φ rows).2 ≤ φ.maxVar + 1 + CNF.numLits φ + rows.length * (φ.maxVar + 1) := by
  have h1 := shortenAll_snd_le (φ.maxVar + 1) φ
  have h2 := isolateRows_snd_le (φ.maxVar + 1) (shortenAll (φ.maxVar + 1) φ).2 rows
  show (isolateRows (φ.maxVar + 1) (shortenAll (φ.maxVar + 1) φ).2 rows).2 ≤ _
  omega

theorem isolate_length_le (φ : CNF) (rows : List (List Bool)) :
    (isolate φ rows).1.length ≤ 3 * CNF.numLits φ + φ.length + rows.length * (4 * (φ.maxVar + 1) + 1) := by
  have h1 := shortenAll_length_le (φ.maxVar + 1) φ
  have h2 := isolateRows_length_le (φ.maxVar + 1) (shortenAll (φ.maxVar + 1) φ).2 rows
  show ((shortenAll (φ.maxVar + 1) φ).1 ++
    (isolateRows (φ.maxVar + 1) (shortenAll (φ.maxVar + 1) φ).2 rows).1).length ≤ _
  rw [List.length_append]
  omega

/-- **Windowed extension form of the isolated formula.** -/
theorem isolate_windowExt (φ : CNF) (rows : List (List Bool)) :
    WindowExt (isolate φ rows).1 (φ.maxVar + 1) ((isolate φ rows).2 - (φ.maxVar + 1))
      (fun g ↦ CNF.evalF g φ = true ∧ rowsHold (φ.maxVar + 1) rows g) := by
  have h₁ := shortenAll_windowExt (φ.maxVar + 1) (varsLt_maxVar_succ φ)
  have hge₁ := shortenAll_snd_ge (φ.maxVar + 1) φ
  have h₂ := isolateRows_windowExt (φ.maxVar + 1) (shortenAll (φ.maxVar + 1) φ).2 hge₁ rows
  have hge₂ := isolateRows_snd_ge (φ.maxVar + 1) (shortenAll (φ.maxVar + 1) φ).2 rows
  have h := WindowExt.append h₁ (windowExt_cast_t h₂ (Nat.add_sub_cancel' hge₁).symm)
    (dependsBelow_rowsHold le_rfl rows)
  show WindowExt ((shortenAll (φ.maxVar + 1) φ).1 ++
    (isolateRows (φ.maxVar + 1) (shortenAll (φ.maxVar + 1) φ).2 rows).1) (φ.maxVar + 1)
    ((isolateRows (φ.maxVar + 1) (shortenAll (φ.maxVar + 1) φ).2 rows).2 - (φ.maxVar + 1)) _
  exact windowExt_cast_a h (by omega)

theorem isolate_solutions_eq_empty (φ : CNF) (rows : List (List Bool)) (h : ¬ φ.Satisfiable) :
    solutions (isolate φ rows).1 (isolate φ rows).2 = ∅ := by
  have hφ := (not_satisfiable_iff_solutions_eq_empty (varsLt_maxVar_succ φ)).1 h
  have hu : ∀ α : BitString (φ.maxVar + 1),
      ¬ (CNF.evalF (toFun α) φ = true ∧ rowsHold (φ.maxVar + 1) rows (toFun α)) := by
    intro α hα
    have : α ∈ solutions φ (φ.maxVar + 1) := mem_solutions.2 hα.1
    rw [hφ] at this
    exact Finset.notMem_empty α this
  have hs := solutions_eq_empty_of_windowExt (isolate_windowExt φ rows) hu
  rwa [Nat.add_sub_cancel' (isolate_snd_ge φ rows)] at hs

/-- Unsatisfiable inputs stay unsatisfiable for every choice of rows. -/
theorem isolate_unsat (φ : CNF) (rows : List (List Bool)) (h : ¬ φ.Satisfiable) :
    ¬ (isolate φ rows).1.Satisfiable :=
  (not_satisfiable_iff_solutions_eq_empty (isolate_varsLt φ rows)).2
    (isolate_solutions_eq_empty φ rows h)

open scoped Classical in
/-- The solution count of the isolated formula equals the number of solutions of `φ` (over `m₀`
variables) satisfying the row constraints. -/
theorem card_solutions_isolate (φ : CNF) (rows : List (List Bool)) :
    (solutions (isolate φ rows).1 (isolate φ rows).2).card =
      ((solutions φ (φ.maxVar + 1)).filter fun α ↦ rowsHold (φ.maxVar + 1) rows (toFun α)).card := by
  have h := card_solutions_of_windowExt (isolate_windowExt φ rows)
  rw [Nat.add_sub_cancel' (isolate_snd_ge φ rows)] at h
  rw [h]
  congr 1
  ext α
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, mem_solutions]

/-! ### Connection with the affine family -/

/-- The rows of an affine seed as lists. -/
def rowsOfSeed {m₀ k : ℕ} (seed : BitString (PairwiseIndependentHash.affineSeedWidth m₀ k)) :
    List (List Bool) :=
  (List.finRange k).map fun i ↦ List.ofFn (PairwiseIndependentHash.affineRows seed i)

private theorem getD_ofFn_of_lt {n : ℕ} (f : Fin n → Bool) {j : ℕ} (hj : j < n) :
    (List.ofFn f).getD j false = f ⟨j, hj⟩ := by
  simp [List.getD_eq_getElem?_getD, hj]

private theorem filterMap_ite_eq_map_filter {α β : Type*} (p : α → Bool) (g : α → β) (l : List α) :
    (l.filterMap fun a ↦ if p a then some (g a) else none) = (l.filter p).map g := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    rw [List.filterMap_cons, List.filter_cons]
    cases p a <;> simp [ih]

theorem rowOfList_rowsOfSeed {m₀ k : ℕ} (seed : BitString (PairwiseIndependentHash.affineSeedWidth m₀ k))
    (i : Fin k) :
    rowOfList m₀ (List.ofFn (PairwiseIndependentHash.affineRows seed i)) =
      (rowVars seed i, rowTarget seed i) := by
  unfold rowOfList rowVars rowTarget
  refine Prod.ext ?_ ?_
  · show (List.range m₀).filter _ = _
    rw [← List.map_coe_finRange_eq_range, List.filter_map, filterMap_ite_eq_map_filter]
    congr 1
    apply List.filter_congr
    intro j _
    simp only [Function.comp]
    rw [getD_ofFn_of_lt _ (Nat.lt_succ_of_lt j.isLt)]
    rfl
  · show (List.ofFn _).getD m₀ false = _
    rw [getD_ofFn_of_lt _ (Nat.lt_succ_self m₀)]
    rfl

theorem rowsHold_rowsOfSeed_iff {m₀ k : ℕ}
    (seed : BitString (PairwiseIndependentHash.affineSeedWidth m₀ k)) (α : BitString m₀) :
    rowsHold m₀ (rowsOfSeed seed) (toFun α) ↔
      PairwiseIndependentHash.affineEval seed α = zeroCell k := by
  rw [affineEval_eq_zeroCell_iff]
  simp only [rowsHold, rowsOfSeed, List.forall_mem_map, List.mem_finRange, true_implies,
    rowOfList_rowsOfSeed]

/-- The rows read from the flat seed bits agree with `affineRows`. -/
theorem hashRows_ofFn {m₀ k : ℕ} (seed : BitString (PairwiseIndependentHash.affineSeedWidth m₀ k)) :
    hashRows m₀ k (List.ofFn seed) = rowsOfSeed seed := by
  unfold hashRows rowsOfSeed
  apply List.ext_getElem
  · simp
  · intro i h₁ h₂
    have hi : i < k := by simpa using h₁
    simp only [List.getElem_map, List.getElem_range, List.getElem_finRange]
    have hmul : (i + 1) * (m₀ + 1) ≤ k * (m₀ + 1) := Nat.mul_le_mul_right _ hi
    rw [add_mul, one_mul] at hmul
    apply List.ext_getElem
    · simp only [List.length_take, List.length_drop, List.length_ofFn]
      have e : PairwiseIndependentHash.affineSeedWidth m₀ k = k * (m₀ + 1) := rfl
      omega
    · intro j hj₁ hj₂
      simp only [List.getElem_take, List.getElem_drop, List.getElem_ofFn,
        PairwiseIndependentHash.affineRows]
      congr 1
      ext
      simp only [finProdFinEquiv_apply_val, Fin.val_cast]
      ring

open scoped Classical in
/-- **Lemma 12 applied**: for the right `k`, a uniform affine seed isolates with probability
`≥ 1/8`. -/
theorem eventProb_isolate_unique_ge (φ : CNF) (hsat : φ.Satisfiable) :
    let m₀ := φ.maxVar + 1
    let k := Nat.size (solutions φ m₀).card + 1
    (1 : ℚ) / 8 ≤ eventProb (univ.filter fun seed : BitString (PairwiseIndependentHash.affineSeedWidth m₀ k) ↦
      UniqueSat (isolate φ (rowsOfSeed seed)).1 (isolate φ (rowsOfSeed seed)).2) := by
  dsimp only
  have hS : (solutions φ (φ.maxVar + 1)).Nonempty :=
    (satisfiable_iff_solutions_nonempty (varsLt_maxVar_succ φ)).1 hsat
  obtain ⟨hlow, hhigh, -⟩ := exists_k_of_card (solutions φ (φ.maxVar + 1)) hS
  refine le_of_le_of_eq (eventProb_isolatingSeeds_ge _ hS hlow hhigh) ?_
  unfold isolatingSeeds
  refine congrArg eventProb (Finset.filter_congr fun seed _ ↦ ?_)
  rw [UniqueSat, card_solutions_isolate]
  exact Iff.of_eq (congrArg (· = 1) (congrArg Finset.card
    (Finset.filter_congr fun x _ ↦ (rowsHold_rowsOfSeed_iff seed x).symm)))

/-- Reading the hash from a longer block only uses a prefix; reading `k` from `kBits m₀` bits
hits the right `k` with probability `≥ 1 / (2 (m₀ + 3))`. -/
theorem eventProb_chooseK_eq (m₀ k : ℕ) (hk1 : 1 ≤ k) (hk2 : k ≤ m₀ + 2) :
    (1 : ℚ) / (2 * (m₀ + 3)) ≤
      eventProb (univ.filter fun v : BitString (kBits m₀) ↦ chooseK m₀ (List.ofFn v) = k) := by
  have hsub : (univ.filter fun v : BitString (kBits m₀) ↦ bitsVal v = k) ⊆
      univ.filter fun v ↦ chooseK m₀ (List.ofFn v) = k := by
    intro v hv
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hv ⊢
    unfold bitsVal at hv
    show (if 1 ≤ SparseDiv.decNat (List.ofFn v) ∧ SparseDiv.decNat (List.ofFn v) ≤ m₀ + 2 then
      SparseDiv.decNat (List.ofFn v) else 1) = k
    rw [hv, ite_eq_left ⟨hk1, hk2⟩]
  have hk : k < 2 ^ kBits m₀ := lt_of_le_of_lt hk2 (Nat.lt_size_self (m₀ + 2))
  have h1 : eventProb (univ.filter fun v : BitString (kBits m₀) ↦ bitsVal v = k) =
      1 / 2 ^ kBits m₀ := by
    unfold eventProb
    rw [card_bitsVal_eq hk]
    simp
  have h2 : (2 : ℚ) ^ kBits m₀ ≤ 2 * (m₀ + 3) := by
    have h := two_pow_size_le_two_mul (n := m₀ + 2) (by omega)
    have h' : (2 : ℚ) ^ kBits m₀ ≤ 2 * ((m₀ : ℚ) + 2) := by exact_mod_cast h
    linarith
  calc (1 : ℚ) / (2 * (m₀ + 3)) ≤ 1 / 2 ^ kBits m₀ :=
        one_div_le_one_div_of_le (by positivity) h2
    _ = eventProb (univ.filter fun v : BitString (kBits m₀) ↦ bitsVal v = k) := h1.symm
    _ ≤ _ := eventProb_mono hsub

/-- Only the first `k (m₀ + 1)` bits are read by `hashRows`. -/
theorem hashRows_take (m₀ k : ℕ) (bits : List Bool) :
    hashRows m₀ k (bits.take (k * (m₀ + 1))) = hashRows m₀ k bits := by
  unfold hashRows
  apply List.map_congr_left
  intro i hi
  rw [List.mem_range] at hi
  rw [List.drop_take, List.take_take]
  have hmul : (i + 1) * (m₀ + 1) ≤ k * (m₀ + 1) := Nat.mul_le_mul_right _ hi
  rw [add_mul, one_mul] at hmul
  congr 1
  omega

theorem hashRows_take' (m₀ k : ℕ) (bits : List Bool) :
    hashRows m₀ k (bits.take (PairwiseIndependentHash.affineSeedWidth m₀ k)) = hashRows m₀ k bits :=
  hashRows_take m₀ k bits

open scoped Classical in
/-- An event on `T = a + b` bits that only reads the first `a` bits (as a list) has the probability
of the corresponding event on `a` bits. -/
private theorem eventProb_filter_take_ge {a b : ℕ} (G : Finset (BitString a)) (q : ℚ)
    (hG : q ≤ eventProb G) (Q : List Bool → Prop)
    (hQ : ∀ u : BitString a, Q (List.ofFn u) ↔ u ∈ G)
    (hQtake : ∀ l : List Bool, Q (l.take a) ↔ Q l) (T : ℕ) (hT : T = a + b) :
    q ≤ eventProb (univ.filter fun w : BitString T ↦ Q (List.ofFn w)) := by
  subst hT
  rw [← eventProb_filter_blockFst (b := b) G] at hG
  refine hG.trans (le_of_eq ?_)
  congr 1
  ext w
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  rw [← hQ, ofFn_blockFst, hQtake]

open scoped Classical in
/-- **Lemma 13 / Lemma 21 (probabilistic part).** -/
theorem eventProb_isolateSeed_unique_ge (φ : CNF) (hsat : φ.Satisfiable) :
    let m₀ := φ.maxVar + 1
    (1 : ℚ) / (16 * (m₀ + 3)) ≤
      eventProb (univ.filter fun w : BitString (kBits m₀ + hashBits m₀) ↦
        UniqueSat (isolateSeed φ (List.ofFn (blockFst _ _ w)) (List.ofFn (blockSnd _ _ w))).1
          (isolateSeed φ (List.ofFn (blockFst _ _ w)) (List.ofFn (blockSnd _ _ w))).2) := by
  intro m₀
  have hm₀ : m₀ = φ.maxVar + 1 := rfl
  clear_value m₀
  have hG := eventProb_isolate_unique_ge φ hsat
  dsimp only at hG
  rw [← hm₀] at hG
  obtain ⟨k, hk⟩ : ∃ k, Nat.size (solutions φ m₀).card + 1 = k := ⟨_, rfl⟩
  rw [hk] at hG
  have hS : (solutions φ m₀).Nonempty :=
    (satisfiable_iff_solutions_nonempty (hm₀ ▸ varsLt_maxVar_succ φ)).1 hsat
  obtain ⟨-, -, hkle⟩ := exists_k_of_card (solutions φ m₀) hS
  rw [hk] at hkle
  have hk1 : 1 ≤ k := by omega
  -- the hash block: only the first `k (m₀ + 1)` bits matter
  have hQ : (1 : ℚ) / 8 ≤ eventProb (univ.filter fun v : BitString (hashBits m₀) ↦
      UniqueSat (isolate φ (hashRows m₀ k (List.ofFn v))).1
        (isolate φ (hashRows m₀ k (List.ofFn v))).2) := by
    refine eventProb_filter_take_ge (a := PairwiseIndependentHash.affineSeedWidth m₀ k)
      (b := (m₀ + 2 - k) * (m₀ + 1)) _ _ hG
      (fun l ↦ UniqueSat (isolate φ (hashRows m₀ k l)).1 (isolate φ (hashRows m₀ k l)).2)
      ?_ ?_ _ ?_
    · intro u
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, hashRows_ofFn]
    · intro l
      rw [hashRows_take']
    · show (m₀ + 2) * (m₀ + 1) = k * (m₀ + 1) + (m₀ + 2 - k) * (m₀ + 1)
      rw [← add_mul]
      congr 1
      omega
  have hP := eventProb_chooseK_eq m₀ k hk1 hkle
  have hPQ := eventProb_block (fun u : BitString (kBits m₀) ↦ chooseK m₀ (List.ofFn u) = k)
    (fun v : BitString (hashBits m₀) ↦ UniqueSat (isolate φ (hashRows m₀ k (List.ofFn v))).1
        (isolate φ (hashRows m₀ k (List.ofFn v))).2)
  have hsub : (univ.filter fun w : BitString (kBits m₀ + hashBits m₀) ↦
      chooseK m₀ (List.ofFn (blockFst _ _ w)) = k ∧
      UniqueSat (isolate φ (hashRows m₀ k (List.ofFn (blockSnd _ _ w)))).1
        (isolate φ (hashRows m₀ k (List.ofFn (blockSnd _ _ w)))).2) ⊆
      univ.filter fun w ↦
        UniqueSat (isolateSeed φ (List.ofFn (blockFst _ _ w)) (List.ofFn (blockSnd _ _ w))).1
          (isolateSeed φ (List.ofFn (blockFst _ _ w)) (List.ofFn (blockSnd _ _ w))).2 := by
    intro w hw
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hw ⊢
    unfold isolateSeed
    rw [← hm₀, hw.1]
    exact hw.2
  calc (1 : ℚ) / (16 * (m₀ + 3)) = 1 / (2 * (m₀ + 3)) * (1 / 8) := by
        rw [div_mul_div_comm, one_mul]
        congr 1
        ring
    _ ≤ eventProb (univ.filter fun u : BitString (kBits m₀) ↦ chooseK m₀ (List.ofFn u) = k) *
        eventProb (univ.filter fun v : BitString (hashBits m₀) ↦
          UniqueSat (isolate φ (hashRows m₀ k (List.ofFn v))).1
            (isolate φ (hashRows m₀ k (List.ofFn v))).2) :=
        mul_le_mul hP hQ (by norm_num) (eventProb_nonneg _)
    _ = _ := hPQ.symm
    _ ≤ _ := eventProb_mono hsub

theorem isolateSeed_unsat (φ : CNF) (kbits hbits : List Bool) (h : ¬ φ.Satisfiable) :
    ¬ (isolateSeed φ kbits hbits).1.Satisfiable :=
  isolate_unsat _ _ h

theorem isolateSeed_boundedClauses (φ : CNF) (kbits hbits : List Bool) :
    BoundedClauses (isolateSeed φ kbits hbits).1 :=
  isolate_boundedClauses _ _

theorem isolateSeed_varsLt (φ : CNF) (kbits hbits : List Bool) :
    CNF.VarsLt (isolateSeed φ kbits hbits).1 (isolateSeed φ kbits hbits).2 :=
  isolate_varsLt _ _

theorem chooseK_le (m₀ : ℕ) (bits : List Bool) : chooseK m₀ bits ≤ m₀ + 2 := by
  simp only [chooseK]
  split_ifs with h <;> omega

theorem hashRows_length (m₀ k : ℕ) (bits : List Bool) : (hashRows m₀ k bits).length = k := by
  simp [hashRows]

theorem isolateSeed_snd_le (φ : CNF) (kbits hbits : List Bool) :
    (isolateSeed φ kbits hbits).2 ≤ φ.maxVar + 1 + CNF.numLits φ + (φ.maxVar + 3) * (φ.maxVar + 1) := by
  have h := isolate_snd_le φ (hashRows (φ.maxVar + 1) (chooseK (φ.maxVar + 1) kbits) hbits)
  rw [hashRows_length] at h
  have hk : chooseK (φ.maxVar + 1) kbits ≤ φ.maxVar + 3 := by
    have := chooseK_le (φ.maxVar + 1) kbits
    omega
  have hmul := Nat.mul_le_mul_right (φ.maxVar + 1) hk
  unfold isolateSeed
  omega

theorem isolateSeed_length_le (φ : CNF) (kbits hbits : List Bool) :
    (isolateSeed φ kbits hbits).1.length ≤
      3 * CNF.numLits φ + φ.length + (φ.maxVar + 3) * (4 * (φ.maxVar + 1) + 1) := by
  have h := isolate_length_le φ (hashRows (φ.maxVar + 1) (chooseK (φ.maxVar + 1) kbits) hbits)
  rw [hashRows_length] at h
  have hk : chooseK (φ.maxVar + 1) kbits ≤ φ.maxVar + 3 := by
    have := chooseK_le (φ.maxVar + 1) kbits
    omega
  have hmul := Nat.mul_le_mul_right (4 * (φ.maxVar + 1) + 1) hk
  unfold isolateSeed
  omega

/-- `maxVar` and the number of literals are bounded by the encoding length (complexitylib's
unary encoding). -/
theorem maxVar_le_length_encode (φ : CNF) : φ.maxVar ≤ (CNF.encode φ).length :=
  CNF.maxVar_le_encode_length φ

private theorem clause_length_le_length_encode (c : Clause) :
    c.length ≤ (Clause.encode c).length := by
  induction c with
  | nil => simp
  | cons ℓ ℓs ih =>
    rw [Clause.encode_cons, List.length_append, List.length_append]
    simp only [List.length_cons, List.length_nil]
    omega

theorem numLits_le_length_encode (φ : CNF) : CNF.numLits φ ≤ (CNF.encode φ).length := by
  induction φ with
  | nil => simp [numLits_nil]
  | cons c cs ih =>
    rw [numLits_cons, CNF.encode_cons, List.length_append, List.length_append]
    have := clause_length_le_length_encode c
    simp only [List.length_cons, List.length_nil]
    omega

theorem length_le_length_encode (φ : CNF) : φ.length ≤ (CNF.encode φ).length := by
  induction φ with
  | nil => simp
  | cons c cs ih =>
    rw [List.length_cons, CNF.encode_cons, List.length_append, List.length_append]
    simp only [List.length_cons, List.length_nil]
    omega

end SparseGcd
