import SparseGcd.Cnf.Basic

/-!
# Parsimonious gadgets (Definition 9, Lemma 13/21 item 3)

A *definitional gadget* `ψ` on the window `[t, t + a)` forces the window variables to a function
`F` of the variables below `t`: for every `g : ℕ → Bool` and `β : BitString a`,
`ψ` is satisfied by `patch g t β` iff `β = F g`. Gadgets compose along consecutive windows, and a
formula `ψ_def ++ ψ_plain` whose plain part only reads variables `< n + a` has exactly as many
solutions over `n + a` variables as the projected predicate `α ↦ ψ_plain (α, F α)` has over `n`
variables. This is the precise form of "auxiliary variables are uniquely forced".

Concrete gadgets: `y ↔ λ₁ ∨ λ₂` (three clauses), `y ↔ x₁ ⊕ x₂` (four clauses), OR-chains for long
clauses, XOR-chains for parity constraints. All clauses have at most three literals.
-/

open Complexity SAT

namespace SparseGcd

/-! ### Helpers on `Fin.append` and `patch` -/

theorem append_eq_append_iff {a b : ℕ} {u u' : BitString a} {v v' : BitString b} :
    Fin.append u v = Fin.append u' v' ↔ u = u' ∧ v = v' := by
  constructor
  · intro h
    refine ⟨funext fun j ↦ ?_, funext fun j ↦ ?_⟩
    · simpa using congrFun h (Fin.castAdd b j)
    · simpa using congrFun h (Fin.natAdd a j)
  · rintro ⟨rfl, rfl⟩; rfl

theorem exists_eq_append {a b : ℕ} (β : BitString (a + b)) :
    ∃ (β₁ : BitString a) (β₂ : BitString b), β = Fin.append β₁ β₂ :=
  ⟨_, _, Fin.append_castAdd_natAdd.symm⟩

theorem append_apply_of_lt {a b : ℕ} (u : BitString a) (v : BitString b) {j : ℕ}
    (hj : j < a + b) (h : j < a) : Fin.append u v ⟨j, hj⟩ = u ⟨j, h⟩ := by
  have e : (⟨j, hj⟩ : Fin (a + b)) = Fin.castAdd b ⟨j, h⟩ := rfl
  rw [e, Fin.append_left]

theorem append_apply_of_ge {a b : ℕ} (u : BitString a) (v : BitString b) {j : ℕ}
    (hj : j < a + b) (h : a ≤ j) : Fin.append u v ⟨j, hj⟩ = v ⟨j - a, by omega⟩ := by
  have e : (⟨j, hj⟩ : Fin (a + b)) = Fin.natAdd a ⟨j - a, by omega⟩ := by
    ext; simp; omega
  rw [e, Fin.append_right]

theorem patch_of_mem (g : ℕ → Bool) (t : ℕ) {a : ℕ} (β : BitString a) {i : ℕ} (h₁ : t ≤ i)
    (h₂ : i < t + a) : patch g t β i = β ⟨i - t, by omega⟩ := by
  unfold patch
  rw [dite_eq_left ⟨h₁, h₂⟩]

theorem patch_add (g : ℕ → Bool) (t : ℕ) {a : ℕ} (β : BitString a) (j : ℕ) (hj : j < a) :
    patch g t β (t + j) = β ⟨j, hj⟩ :=
  patch_window g t β ⟨j, hj⟩

/-- The first window variable. -/
theorem patch_zero (g : ℕ → Bool) (t : ℕ) {a : ℕ} (β : BitString (a + 1)) :
    patch g t β t = β 0 := by
  simpa using patch_window g t β 0

theorem bitString_one_eq {β : BitString 1} {v : Bool} : (β = fun _ ↦ v) ↔ β 0 = v := by
  constructor
  · rintro rfl; rfl
  · intro h; funext j; rw [Subsingleton.elim j 0, h]

/-- Patching a window above every variable of `ψ` does not change its value. -/
theorem CNF.evalF_patch_of_varsLt {ψ : CNF} {t : ℕ} (h : CNF.VarsLt ψ t) (g : ℕ → Bool) {a : ℕ}
    (β : BitString a) : CNF.evalF (patch g t β) ψ = CNF.evalF g ψ :=
  CNF.evalF_congr fun c hc ℓ hℓ ↦ patch_of_lt _ _ _ (h c hc ℓ hℓ)

theorem Lit.evalF_mk (g : ℕ → Bool) (s : Bool) (v : ℕ) : Lit.evalF g ⟨s, v⟩ = (g v == s) := rfl

theorem Lit.evalF_patch_of_lt (g : ℕ → Bool) (t : ℕ) {a : ℕ} (β : BitString a) {ℓ : Lit}
    (h : ℓ.var < t) : Lit.evalF (patch g t β) ℓ = Lit.evalF g ℓ := by
  simp [Lit.evalF, patch_of_lt _ _ _ h]

theorem Clause.evalF_cons (g : ℕ → Bool) (ℓ : Lit) (c : Clause) :
    Clause.evalF g (ℓ :: c) = (Lit.evalF g ℓ || Clause.evalF g c) := rfl

theorem Clause.evalF_patch_of_lt (g : ℕ → Bool) (t : ℕ) {a : ℕ} (β : BitString a) {c : Clause}
    (h : ∀ ℓ ∈ c, ℓ.var < t) : Clause.evalF (patch g t β) c = Clause.evalF g c := by
  induction c with
  | nil => rfl
  | cons ℓ c ih =>
    have h1 := h ℓ (by simp)
    have h2 := ih fun ℓ' hℓ' ↦ h ℓ' (List.mem_cons_of_mem _ hℓ')
    rw [Clause.evalF_cons, Clause.evalF_cons, Lit.evalF_patch_of_lt _ _ _ h1, h2]

/-! ### Definitional gadgets -/

/-- `ψ` reads only variables below `t + a` and forces the window `[t, t+a)` to `F g`, where `F` only
depends on the variables below `t`. -/
structure DefGadget (ψ : CNF) (t a : ℕ) (F : (ℕ → Bool) → BitString a) : Prop where
  vars : CNF.VarsLt ψ (t + a)
  indep : ∀ g g' : ℕ → Bool, (∀ i, i < t → g i = g' i) → F g = F g'
  spec : ∀ (g : ℕ → Bool) (β : BitString a), CNF.evalF (patch g t β) ψ = true ↔ β = F g

/-- The empty gadget on an empty window. -/
theorem defGadget_nil (t : ℕ) : DefGadget [] t 0 (fun _ ↦ Fin.elim0) := by
  refine ⟨fun c hc ↦ by simp at hc, fun _ _ _ ↦ rfl, fun g β ↦ ?_⟩
  simp only [CNF.evalF, List.all_nil, true_iff]
  exact Subsingleton.elim _ _

/-- Transport a gadget along an equality of window sizes and a pointwise equality of the forcing
functions. -/
theorem DefGadget.congr {ψ : CNF} {t a a' : ℕ} (h : a = a') {F : (ℕ → Bool) → BitString a}
    {F' : (ℕ → Bool) → BitString a'}
    (hF : ∀ g (j : ℕ) (hj : j < a) (hj' : j < a'), F g ⟨j, hj⟩ = F' g ⟨j, hj'⟩)
    (hg : DefGadget ψ t a F) : DefGadget ψ t a' F' := by
  subst h
  have e : F = F' := funext fun g ↦ funext fun j ↦ hF g j j.isLt j.isLt
  subst e
  exact hg

/-- Sequential composition of gadgets on consecutive windows; the second may read the first. -/
theorem DefGadget.append {ψ₁ ψ₂ : CNF} {t a₁ a₂ : ℕ} {F₁ : (ℕ → Bool) → BitString a₁}
    {F₂ : (ℕ → Bool) → BitString a₂} (h₁ : DefGadget ψ₁ t a₁ F₁)
    (h₂ : DefGadget ψ₂ (t + a₁) a₂ F₂) :
    DefGadget (ψ₁ ++ ψ₂) t (a₁ + a₂) (fun g ↦ Fin.append (F₁ g) (F₂ (patch g t (F₁ g)))) := by
  refine ⟨VarsLt.append (VarsLt.mono h₁.vars (by omega)) (VarsLt.mono h₂.vars (by omega)), ?_, ?_⟩
  · intro g g' hgg'
    have e₁ : F₁ g = F₁ g' := h₁.indep g g' hgg'
    simp only [e₁]
    congr 1
    apply h₂.indep
    intro i hi
    by_cases hit : i < t
    · rw [patch_of_lt _ _ _ hit, patch_of_lt _ _ _ hit, hgg' i hit]
    · rw [patch_of_mem _ _ _ (by omega) (by omega), patch_of_mem _ _ _ (by omega) (by omega)]
  · intro g β
    obtain ⟨β₁, β₂, rfl⟩ := exists_eq_append β
    rw [patch_append, CNF.evalF_append, Bool.and_eq_true, CNF.evalF_patch_of_varsLt h₁.vars,
      h₁.spec, h₂.spec, append_eq_append_iff]
    constructor <;> rintro ⟨rfl, h⟩ <;> exact ⟨rfl, h⟩

/-- The negation of a literal. -/
def Lit.neg (ℓ : Lit) : Lit := ⟨!ℓ.sign, ℓ.var⟩

theorem Lit.evalF_neg (g : ℕ → Bool) (ℓ : Lit) : Lit.evalF g (Lit.neg ℓ) = !Lit.evalF g ℓ := by
  simp only [Lit.evalF, Lit.neg]
  cases g ℓ.var <;> cases ℓ.sign <;> rfl

/-- `y ↔ (λ₁ ∨ λ₂)`: `(¬y ∨ λ₁ ∨ λ₂), (y ∨ ¬λ₁), (y ∨ ¬λ₂)`. -/
def orGadget (y : ℕ) (l₁ l₂ : Lit) : CNF :=
  [[⟨false, y⟩, l₁, l₂], [⟨true, y⟩, Lit.neg l₁], [⟨true, y⟩, Lit.neg l₂]]

theorem orGadget_boundedClauses (y : ℕ) (l₁ l₂ : Lit) : BoundedClauses (orGadget y l₁ l₂) := by
  simp [BoundedClauses, orGadget]

theorem defGadget_orGadget (t : ℕ) {l₁ l₂ : Lit} (h₁ : l₁.var < t) (h₂ : l₂.var < t) :
    DefGadget (orGadget t l₁ l₂) t 1 (fun g _ ↦ Lit.evalF g l₁ || Lit.evalF g l₂) := by
  refine ⟨?_, ?_, ?_⟩
  · simp only [CNF.VarsLt, orGadget, Lit.neg, List.mem_cons, List.mem_nil_iff, or_false,
      forall_eq_or_imp, forall_eq]
    omega
  · intro g g' hgg'
    funext j
    simp only [Lit.evalF, hgg' _ h₁, hgg' _ h₂]
  · intro g β
    simp only [CNF.evalF, Clause.evalF, orGadget, List.all_cons, List.all_nil, List.any_cons,
      List.any_nil, Lit.evalF_neg, Lit.evalF_patch_of_lt _ _ _ h₁, Lit.evalF_patch_of_lt _ _ _ h₂,
      Lit.evalF_mk, patch_zero, bitString_one_eq]
    cases β 0 <;> cases Lit.evalF g l₁ <;> cases Lit.evalF g l₂ <;> decide

/-- `y ↔ (x₁ ⊕ x₂)`: `(¬y ∨ x₁ ∨ x₂), (¬y ∨ ¬x₁ ∨ ¬x₂), (y ∨ ¬x₁ ∨ x₂), (y ∨ x₁ ∨ ¬x₂)`. -/
def xorGadget (y x₁ x₂ : ℕ) : CNF :=
  [[⟨false, y⟩, ⟨true, x₁⟩, ⟨true, x₂⟩], [⟨false, y⟩, ⟨false, x₁⟩, ⟨false, x₂⟩],
   [⟨true, y⟩, ⟨false, x₁⟩, ⟨true, x₂⟩], [⟨true, y⟩, ⟨true, x₁⟩, ⟨false, x₂⟩]]

theorem xorGadget_boundedClauses (y x₁ x₂ : ℕ) : BoundedClauses (xorGadget y x₁ x₂) := by
  simp [BoundedClauses, xorGadget]

theorem defGadget_xorGadget (t : ℕ) {x₁ x₂ : ℕ} (h₁ : x₁ < t) (h₂ : x₂ < t) :
    DefGadget (xorGadget t x₁ x₂) t 1 (fun g _ ↦ xor (g x₁) (g x₂)) := by
  refine ⟨?_, ?_, ?_⟩
  · simp only [CNF.VarsLt, xorGadget, List.mem_cons, List.mem_nil_iff, or_false,
      forall_eq_or_imp, forall_eq]
    omega
  · intro g g' hgg'
    funext j
    simp only [hgg' _ h₁, hgg' _ h₂]
  · intro g β
    simp only [CNF.evalF, Clause.evalF, xorGadget, List.all_cons, List.all_nil, List.any_cons,
      List.any_nil, Lit.evalF_mk, patch_zero, patch_of_lt _ _ _ h₁, patch_of_lt _ _ _ h₂,
      bitString_one_eq]
    cases β 0 <;> cases g x₁ <;> cases g x₂ <;> decide

/-! ### Windowed parsimonious extensions -/

/-- `P` only depends on the variables below `t`. -/
def DependsBelow (t : ℕ) (P : (ℕ → Bool) → Prop) : Prop :=
  ∀ g g' : ℕ → Bool, (∀ i, i < t → g i = g' i) → (P g ↔ P g')

/-- A formula `ψ` reading only variables `< t + a` is a *parsimonious extension* on the window
`[t, t + a)` of a predicate `P` (depending only on variables `< t`) if every `g` with `P g` has
exactly one satisfying window filling and every `g` without `P g` has none. -/
structure WindowExt (ψ : CNF) (t a : ℕ) (P : (ℕ → Bool) → Prop) : Prop where
  vars : CNF.VarsLt ψ (t + a)
  indep : DependsBelow t P
  unique : ∀ g : ℕ → Bool, P g → ∃! β : BitString a, CNF.evalF (patch g t β) ψ = true
  none : ∀ g : ℕ → Bool, ¬ P g → ∀ β : BitString a, CNF.evalF (patch g t β) ψ = false

/-- Transport along an equality of window sizes and an equivalence of predicates. -/
theorem WindowExt.congr {ψ : CNF} {t a a' : ℕ} {P P' : (ℕ → Bool) → Prop} (h : a = a')
    (hP : ∀ g, P g ↔ P' g) (hw : WindowExt ψ t a P) : WindowExt ψ t a' P' := by
  subst h
  have e : P = P' := funext fun g ↦ propext (hP g)
  subst e
  exact hw

/-- A plain formula with variables `< t` is an extension with an empty window of its own truth. -/
theorem windowExt_plain {ψ : CNF} {t : ℕ} (h : CNF.VarsLt ψ t) :
    WindowExt ψ t 0 (fun g ↦ CNF.evalF g ψ = true) := by
  refine ⟨VarsLt.mono h (by omega), ?_, ?_, ?_⟩
  · intro g g' hgg'
    dsimp only
    rw [CNF.evalF_congr fun c hc ℓ hℓ ↦ hgg' _ (h c hc ℓ hℓ)]
  · intro g hg
    refine ⟨Fin.elim0, ?_, fun β _ ↦ Subsingleton.elim _ _⟩
    dsimp only
    rwa [CNF.evalF_patch_of_varsLt h]
  · intro g hg β
    rw [CNF.evalF_patch_of_varsLt h]
    exact Bool.eq_false_iff.mpr hg

/-- General composition on consecutive windows: `Q` implies `P₁`, and once the first window is
correctly filled, `Q` is equivalent to `P₂` of the patched function. -/
theorem WindowExt.append_of {ψ₁ ψ₂ : CNF} {t a₁ a₂ : ℕ} {P₁ P₂ Q : (ℕ → Bool) → Prop}
    (h₁ : WindowExt ψ₁ t a₁ P₁) (h₂ : WindowExt ψ₂ (t + a₁) a₂ P₂)
    (hQ : DependsBelow t Q) (hQ₁ : ∀ g, Q g → P₁ g)
    (hQ₂ : ∀ g (β₁ : BitString a₁), CNF.evalF (patch g t β₁) ψ₁ = true →
      (Q g ↔ P₂ (patch g t β₁))) :
    WindowExt (ψ₁ ++ ψ₂) t (a₁ + a₂) Q := by
  refine ⟨VarsLt.append (VarsLt.mono h₁.vars (by omega)) (VarsLt.mono h₂.vars (by omega)), hQ,
    ?_, ?_⟩
  · intro g hg
    obtain ⟨β₁, hβ₁, hβ₁u⟩ := h₁.unique g (hQ₁ g hg)
    obtain ⟨β₂, hβ₂, hβ₂u⟩ := h₂.unique (patch g t β₁) ((hQ₂ g β₁ hβ₁).mp hg)
    refine ⟨Fin.append β₁ β₂, ?_, ?_⟩
    · dsimp only
      rw [patch_append, CNF.evalF_append, CNF.evalF_patch_of_varsLt h₁.vars, hβ₁, hβ₂]
      rfl
    · intro β hβ
      obtain ⟨γ₁, γ₂, rfl⟩ := exists_eq_append β
      rw [patch_append, CNF.evalF_append, CNF.evalF_patch_of_varsLt h₁.vars,
        Bool.and_eq_true] at hβ
      obtain ⟨hγ₁, hγ₂⟩ := hβ
      have e₁ : γ₁ = β₁ := hβ₁u γ₁ hγ₁
      subst e₁
      rw [hβ₂u γ₂ hγ₂]
  · intro g hg β
    obtain ⟨γ₁, γ₂, rfl⟩ := exists_eq_append β
    rw [patch_append, CNF.evalF_append, CNF.evalF_patch_of_varsLt h₁.vars]
    by_cases hγ₁ : CNF.evalF (patch g t γ₁) ψ₁ = true
    · rw [hγ₁, Bool.true_and]
      exact h₂.none _ (fun hP₂ ↦ hg ((hQ₂ g γ₁ hγ₁).mpr hP₂)) γ₂
    · simp only [Bool.eq_false_iff.mpr hγ₁, Bool.false_and]

/-- Composition on consecutive windows. -/
theorem WindowExt.append {ψ₁ ψ₂ : CNF} {t a₁ a₂ : ℕ} {P₁ P₂ : (ℕ → Bool) → Prop}
    (h₁ : WindowExt ψ₁ t a₁ P₁) (h₂ : WindowExt ψ₂ (t + a₁) a₂ P₂) (hP₂ : DependsBelow t P₂) :
    WindowExt (ψ₁ ++ ψ₂) t (a₁ + a₂) (fun g ↦ P₁ g ∧ P₂ g) := by
  refine h₁.append_of h₂ ?_ (fun g hg ↦ hg.1) ?_
  · intro g g' hgg'
    exact and_congr (h₁.indep g g' hgg') (hP₂ g g' hgg')
  · intro g β₁ hβ₁
    have hP₁ : P₁ g := by
      by_contra hn
      have := h₁.none g hn β₁
      rw [hβ₁] at this
      exact absurd this (by decide)
    have e : P₂ g ↔ P₂ (patch g t β₁) := hP₂ g _ fun i hi ↦ (patch_of_lt _ _ _ hi).symm
    exact ⟨fun h ↦ e.mp h.2, fun h ↦ ⟨hP₁, e.mpr h⟩⟩

/-- A definitional gadget is a windowed extension of the trivial predicate. -/
theorem DefGadget.toWindowExt {ψ : CNF} {t a : ℕ} {F : (ℕ → Bool) → BitString a}
    (h : DefGadget ψ t a F) : WindowExt ψ t a (fun _ ↦ True) :=
  ⟨h.vars, fun _ _ _ ↦ Iff.rfl,
    fun g _ ↦ ⟨F g, (h.spec g (F g)).mpr rfl, fun β hβ ↦ (h.spec g β).mp hβ⟩,
    fun _ hg ↦ absurd trivial hg⟩

/-- A definitional gadget followed by a windowed extension (which may read the gadget's window):
the resulting predicate is the second predicate evaluated on the patched function. -/
theorem DefGadget.windowExt_append {ψ₁ ψ₂ : CNF} {t a₁ a₂ : ℕ} {F₁ : (ℕ → Bool) → BitString a₁}
    {P₂ : (ℕ → Bool) → Prop} (h₁ : DefGadget ψ₁ t a₁ F₁) (h₂ : WindowExt ψ₂ (t + a₁) a₂ P₂) :
    WindowExt (ψ₁ ++ ψ₂) t (a₁ + a₂) (fun g ↦ P₂ (patch g t (F₁ g))) := by
  refine h₁.toWindowExt.append_of h₂ ?_ (fun _ _ ↦ trivial) ?_
  · intro g g' hgg'
    apply h₂.indep
    intro i hi
    rw [h₁.indep g g' hgg']
    by_cases hit : i < t
    · rw [patch_of_lt _ _ _ hit, patch_of_lt _ _ _ hit, hgg' i hit]
    · rw [patch_of_mem _ _ _ (by omega) (by omega), patch_of_mem _ _ _ (by omega) (by omega)]
  · intro g β₁ hβ₁
    rw [(h₁.spec g β₁).mp hβ₁]

/-! ### XOR chains for parity constraints -/

/-- `xorChain t x₀ xs`: auxiliary variables `t, t+1, …` with `y_t = x₀ ⊕ xs₀`, `y_{t+j} = y_{t+j-1} ⊕ xs_j`.
Returns the gadget clauses; the last auxiliary variable is `t + xs.length - 1` (when `xs ≠ []`). -/
def xorChain (t x₀ : ℕ) : List ℕ → CNF
  | [] => []
  | x :: xs => xorGadget t x₀ x ++ xorChainAux (t + 1) t xs
where
  xorChainAux (t prev : ℕ) : List ℕ → CNF
    | [] => []
    | x :: xs => xorGadget t prev x ++ xorChainAux (t + 1) t xs

/-- Parity of a list of variables under `g`. -/
def parityOf (g : ℕ → Bool) (xs : List ℕ) : Bool := xs.foldl (fun b x ↦ xor b (g x)) false

theorem xorChain_eq_aux (t x₀ : ℕ) (xs : List ℕ) :
    xorChain t x₀ xs = xorChain.xorChainAux t x₀ xs := by
  cases xs <;> rfl

theorem foldl_xor_eq (g : ℕ → Bool) (l : List ℕ) (b : Bool) :
    l.foldl (fun b x ↦ xor b (g x)) b = xor b (parityOf g l) := by
  induction l generalizing b with
  | nil => simp [parityOf]
  | cons x l ih =>
    simp only [parityOf, List.foldl_cons, Bool.false_xor] at ih ⊢
    rw [ih (xor b (g x)), ih (g x), Bool.xor_assoc]

theorem parityOf_nil (g : ℕ → Bool) : parityOf g [] = false := rfl

theorem parityOf_cons (g : ℕ → Bool) (x : ℕ) (l : List ℕ) :
    parityOf g (x :: l) = xor (g x) (parityOf g l) := by
  show l.foldl (fun b x ↦ xor b (g x)) (xor false (g x)) = _
  rw [foldl_xor_eq, Bool.false_xor]

theorem parityOf_congr {g g' : ℕ → Bool} {xs : List ℕ} (h : ∀ x ∈ xs, g x = g' x) :
    parityOf g xs = parityOf g' xs := by
  unfold parityOf
  exact List.foldl_ext _ _ _ fun b x hx ↦ by rw [h x hx]

theorem parityOf_patch_of_lt (g : ℕ → Bool) (t : ℕ) {a : ℕ} (β : BitString a) {xs : List ℕ}
    (h : ∀ x ∈ xs, x < t) : parityOf (patch g t β) xs = parityOf g xs :=
  parityOf_congr fun x hx ↦ patch_of_lt _ _ _ (h x hx)

/-- The auxiliary chain forces `y_{t+j} = prev ⊕ xs₀ ⊕ ⋯ ⊕ xs_j`. -/
theorem defGadget_xorChainAux (xs : List ℕ) : ∀ t prev : ℕ, prev < t → (∀ x ∈ xs, x < t) →
    DefGadget (xorChain.xorChainAux t prev xs) t xs.length
      (fun g j ↦ (xs.take (j.val + 1)).foldl (fun b x ↦ xor b (g x)) (g prev)) := by
  induction xs with
  | nil =>
    intro t prev _ _
    exact DefGadget.congr rfl (fun _ j hj _ ↦ absurd hj (Nat.not_lt_zero j)) (defGadget_nil t)
  | cons x xs ih =>
    intro t prev hprev hxs
    have h₁ := defGadget_xorGadget t hprev (hxs x (by simp))
    have h₂ := ih (t + 1) t (by omega) (fun y hy ↦ by have := hxs y (by simp [hy]); omega)
    refine DefGadget.congr (by simp only [List.length_cons]; omega) ?_ (h₁.append h₂)
    intro g j hj hj'
    dsimp only
    cases j with
    | zero =>
      rw [append_apply_of_lt _ _ _ (by omega)]
      simp
    | succ j =>
      rw [append_apply_of_ge _ _ _ (by omega)]
      simp only [Nat.add_sub_cancel, List.take_succ_cons, List.foldl_cons, patch_zero]
      exact List.foldl_ext _ _ _ fun b y hy ↦ by
        rw [patch_of_lt _ _ _ (hxs y (List.mem_cons_of_mem _ (List.mem_of_mem_take hy)))]

/-- The chain forces `y_{t+j} = x₀ ⊕ xs₀ ⊕ ⋯ ⊕ xs_j`. -/
theorem defGadget_xorChain (t x₀ : ℕ) (xs : List ℕ) (hx₀ : x₀ < t) (hxs : ∀ x ∈ xs, x < t) :
    DefGadget (xorChain t x₀ xs) t xs.length
      (fun g j ↦ xor (g x₀) (parityOf g (xs.take (j.val + 1)))) := by
  rw [xorChain_eq_aux]
  refine DefGadget.congr rfl ?_ (defGadget_xorChainAux xs t x₀ hx₀ hxs)
  intro g j hj hj'
  exact foldl_xor_eq g _ _

theorem xorChainAux_boundedClauses (xs : List ℕ) (t prev : ℕ) :
    BoundedClauses (xorChain.xorChainAux t prev xs) := by
  induction xs generalizing t prev with
  | nil => intro c hc; simp [xorChain.xorChainAux] at hc
  | cons x xs ih => exact (xorGadget_boundedClauses _ _ _).append (ih _ _)

theorem xorChain_boundedClauses (t x₀ : ℕ) (xs : List ℕ) : BoundedClauses (xorChain t x₀ xs) := by
  rw [xorChain_eq_aux]
  exact xorChainAux_boundedClauses xs t x₀

theorem xorChainAux_length (xs : List ℕ) (t prev : ℕ) :
    (xorChain.xorChainAux t prev xs).length = 4 * xs.length := by
  induction xs generalizing t prev with
  | nil => rfl
  | cons x xs ih =>
    have := ih (t + 1) t
    show (xorGadget t prev x ++ xorChain.xorChainAux (t + 1) t xs).length = _
    simp only [List.length_append, List.length_cons, xorGadget, List.length_nil, this]
    omega

theorem xorChain_length (t x₀ : ℕ) (xs : List ℕ) : (xorChain t x₀ xs).length = 4 * xs.length := by
  rw [xorChain_eq_aux]
  exact xorChainAux_length xs t x₀

/-- CNF encoding of the affine constraint `⊕_{x ∈ xs} g x = b` using auxiliary variables from `t`:
* `xs = []`: the constraint is `false = b`; we output `[]` if `b = false`, the empty clause if `b = true`;
* `xs = [x]`: the unit clause `x = b`;
* otherwise the XOR chain followed by the unit clause `y_last = b`.
Returns the clauses and the number of auxiliary variables used. -/
def parityCnf (t : ℕ) (xs : List ℕ) (b : Bool) : CNF × ℕ :=
  match xs with
  | [] => (if b then [[]] else [], 0)
  | [x] => ([[⟨b, x⟩]], 0)
  | x₀ :: x₁ :: rest =>
    (xorChain t x₀ (x₁ :: rest) ++ [[⟨b, t + rest.length⟩]], rest.length + 1)

theorem parityCnf_boundedClauses (t : ℕ) (xs : List ℕ) (b : Bool) :
    BoundedClauses (parityCnf t xs b).1 := by
  match xs with
  | [] => cases b <;> simp [parityCnf, BoundedClauses]
  | [x] => simp [parityCnf, BoundedClauses]
  | x₀ :: x₁ :: rest =>
    exact (xorChain_boundedClauses _ _ _).append (by simp [BoundedClauses])

theorem parityCnf_aux_le (t : ℕ) (xs : List ℕ) (b : Bool) : (parityCnf t xs b).2 ≤ xs.length := by
  match xs with
  | [] => exact Nat.le_refl _
  | [x] => exact Nat.zero_le _
  | x₀ :: x₁ :: rest =>
    show rest.length + 1 ≤ (x₀ :: x₁ :: rest).length
    simp only [List.length_cons]
    omega

theorem parityCnf_length_le (t : ℕ) (xs : List ℕ) (b : Bool) :
    (parityCnf t xs b).1.length ≤ 4 * xs.length + 1 := by
  match xs with
  | [] => cases b <;> simp [parityCnf]
  | [x] => simp [parityCnf]
  | x₀ :: x₁ :: rest =>
    show (xorChain t x₀ (x₁ :: rest) ++ [[(⟨b, t + rest.length⟩ : Lit)]]).length ≤ _
    simp only [List.length_append, xorChain_length, List.length_cons, List.length_nil]
    omega

theorem windowExt_parityCnf (t : ℕ) (xs : List ℕ) (b : Bool) (hxs : ∀ x ∈ xs, x < t) :
    WindowExt (parityCnf t xs b).1 t (parityCnf t xs b).2 (fun g ↦ parityOf g xs = b) := by
  match xs with
  | [] =>
    cases b
    · refine WindowExt.congr rfl ?_ (windowExt_plain (ψ := []) (t := t) fun c hc ↦ by simp at hc)
      intro g
      simp [CNF.evalF, parityOf]
    · refine WindowExt.congr rfl ?_ (windowExt_plain (ψ := [[]]) (t := t) ?_)
      · intro g
        simp [CNF.evalF, Clause.evalF, parityOf]
      · intro c hc ℓ hℓ
        simp at hc
        subst hc
        simp at hℓ
  | [x] =>
    refine WindowExt.congr rfl ?_ (windowExt_plain (ψ := [[⟨b, x⟩]]) (t := t) ?_)
    · intro g
      simp [CNF.evalF, Clause.evalF, Lit.evalF, parityOf]
    · intro c hc ℓ hℓ
      simp at hc
      subst hc
      simp at hℓ
      subst hℓ
      exact hxs x (by simp)
  | x₀ :: x₁ :: rest =>
    have hx₀ : x₀ < t := hxs x₀ (by simp)
    have hrest : ∀ x ∈ x₁ :: rest, x < t := fun x hx ↦ hxs x (List.mem_cons_of_mem _ hx)
    have h₁ := defGadget_xorChain t x₀ (x₁ :: rest) hx₀ hrest
    have h₂ : WindowExt [[⟨b, t + rest.length⟩]] (t + (x₁ :: rest).length) 0
        (fun g ↦ CNF.evalF g [[⟨b, t + rest.length⟩]] = true) := by
      refine windowExt_plain ?_
      intro c hc ℓ hℓ
      simp at hc
      subst hc
      simp at hℓ
      subst hℓ
      simp
    refine WindowExt.congr rfl ?_ (h₁.windowExt_append h₂)
    intro g
    simp only [CNF.evalF, Clause.evalF, List.all_cons, List.all_nil, List.any_cons, List.any_nil,
      Lit.evalF_mk, Bool.or_false, Bool.and_true, beq_iff_eq]
    rw [patch_add _ _ _ rest.length (by simp)]
    dsimp only
    rw [List.take_of_length_le (by simp)]
    simp only [parityOf_cons]

theorem parityCnf_varsLt (t : ℕ) (xs : List ℕ) (b : Bool) (hxs : ∀ x ∈ xs, x < t) :
    CNF.VarsLt (parityCnf t xs b).1 (t + (parityCnf t xs b).2) :=
  (windowExt_parityCnf t xs b hxs).vars

/-- **Parsimonious parity constraint.** For every `g`, the window `[t, t + aux)` has exactly one
satisfying filling when the parity holds and none otherwise. -/
theorem parityCnf_spec (t : ℕ) (xs : List ℕ) (b : Bool) (hxs : ∀ x ∈ xs, x < t) (g : ℕ → Bool) :
    (parityOf g xs = b → ∃! β : BitString (parityCnf t xs b).2,
        CNF.evalF (patch g t β) (parityCnf t xs b).1 = true) ∧
    (parityOf g xs ≠ b → ∀ β : BitString (parityCnf t xs b).2,
        CNF.evalF (patch g t β) (parityCnf t xs b).1 = false) :=
  ⟨(windowExt_parityCnf t xs b hxs).unique g, (windowExt_parityCnf t xs b hxs).none g⟩

/-! ### OR chains for long clauses (Lemma 21, item 3) -/

/-- Convert a clause with `≥ 4` literals `λ₁ ∨ ⋯ ∨ λ_r` into clauses of size ≤ 3 using auxiliary
variables `t, t+1, …`: `p_t = λ₁ ∨ λ₂`, `p_{t+j} = p_{t+j-1} ∨ λ_{j+2}`, final clause `p_last ∨ λ_r`.
Short clauses are returned unchanged. Returns the clauses and the number of auxiliaries. -/
def shortenClause (t : ℕ) (c : Clause) : CNF × ℕ :=
  match c with
  | l₁ :: l₂ :: l₃ :: l₄ :: rest =>
    (orGadget t l₁ l₂ ++ orChainAux (t + 1) t (l₃ :: l₄ :: rest), rest.length + 2)
  | _ => ([c], 0)
where
  /-- `orChainAux t prev ls`: for `ls = [l]`, the final clause `(p_prev ∨ l)`; otherwise a new
  auxiliary `p_t = p_prev ∨ l` and recurse. -/
  orChainAux (t prev : ℕ) : List Lit → CNF
    | [] => []
    | [l] => [[⟨true, prev⟩, l]]
    | l :: ls => orGadget t ⟨true, prev⟩ l ++ orChainAux (t + 1) t ls

theorem shortenClause_short (t : ℕ) (c : Clause) (hc : c.length ≤ 3) :
    shortenClause t c = ([c], 0) := by
  match c with
  | [] | [_] | [_, _] | [_, _, _] => rfl
  | _ :: _ :: _ :: _ :: _ =>
    exfalso
    simp only [List.length_cons] at hc
    omega

theorem orChainAux_boundedClauses (ls : List Lit) (t prev : ℕ) :
    BoundedClauses (shortenClause.orChainAux t prev ls) := by
  induction ls generalizing t prev with
  | nil => intro c hc; simp [shortenClause.orChainAux] at hc
  | cons l ls ih =>
    match ls with
    | [] => simp [shortenClause.orChainAux, BoundedClauses]
    | l' :: ls' =>
      show BoundedClauses (orGadget t ⟨true, prev⟩ l ++ shortenClause.orChainAux (t + 1) t (l' :: ls'))
      exact (orGadget_boundedClauses _ _ _).append (ih _ _)

theorem orChainAux_length (ls : List Lit) : ∀ (t prev : ℕ) (l : Lit),
    (shortenClause.orChainAux t prev (l :: ls)).length = 3 * ls.length + 1 := by
  induction ls with
  | nil => intro t prev l; rfl
  | cons l' ls ih =>
    intro t prev l
    show (orGadget t ⟨true, prev⟩ l ++ shortenClause.orChainAux (t + 1) t (l' :: ls)).length = _
    rw [List.length_append, ih]
    simp only [orGadget, List.length_cons, List.length_nil]
    omega

/-- The auxiliary OR chain: a windowed extension of `p_prev ∨ l ∨ ls`. -/
theorem windowExt_orChainAux (ls : List Lit) : ∀ (t prev : ℕ) (l : Lit), prev < t → l.var < t →
    (∀ ℓ ∈ ls, ℓ.var < t) →
    WindowExt (shortenClause.orChainAux t prev (l :: ls)) t ls.length
      (fun g ↦ (g prev || Clause.evalF g (l :: ls)) = true) := by
  induction ls with
  | nil =>
    intro t prev l hprev hl _
    refine WindowExt.congr rfl ?_ (windowExt_plain (ψ := [[⟨true, prev⟩, l]]) (t := t) ?_)
    · intro g
      simp [CNF.evalF, Clause.evalF, Lit.evalF_mk]
    · intro c hc ℓ hℓ
      simp at hc
      subst hc
      simp at hℓ
      rcases hℓ with rfl | rfl
      · exact hprev
      · exact hl
  | cons l' ls ih =>
    intro t prev l hprev hl hls
    have hls' : ∀ ℓ ∈ l' :: ls, ℓ.var < t := hls
    have h₁ := defGadget_orGadget t (l₁ := ⟨true, prev⟩) (l₂ := l) hprev hl
    have h₂ := ih (t + 1) t l' (by omega) (by have := hls l' (by simp); omega)
      (fun ℓ hℓ ↦ by have := hls ℓ (List.mem_cons_of_mem _ hℓ); omega)
    refine WindowExt.congr (by simp only [List.length_cons]; omega) ?_ (h₁.windowExt_append h₂)
    intro g
    simp only [patch_zero, Lit.evalF_mk, Clause.evalF_patch_of_lt _ _ _ hls', Clause.evalF_cons,
      Bool.or_assoc, beq_true]

theorem windowExt_shortenClause (t : ℕ) (c : Clause) (hc : ∀ ℓ ∈ c, ℓ.var < t) :
    WindowExt (shortenClause t c).1 t (shortenClause t c).2 (fun g ↦ Clause.evalF g c = true) := by
  match c with
  | l₁ :: l₂ :: l₃ :: l₄ :: rest =>
    have hc' : ∀ ℓ ∈ l₃ :: l₄ :: rest, ℓ.var < t :=
      fun ℓ hℓ ↦ hc ℓ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hℓ))
    have h₁ := defGadget_orGadget t (hc l₁ (by simp)) (hc l₂ (by simp))
    have h₂ := windowExt_orChainAux (l₄ :: rest) (t + 1) t l₃ (by omega)
      (by have := hc l₃ (by simp); omega)
      (fun ℓ hℓ ↦ by have := hc ℓ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
        (List.mem_cons_of_mem _ hℓ))); omega)
    refine WindowExt.congr ?_ ?_ (h₁.windowExt_append h₂)
    · show 1 + (l₄ :: rest).length = rest.length + 2
      simp only [List.length_cons]
      omega
    · intro g
      simp only [patch_zero, Clause.evalF_patch_of_lt _ _ _ hc', Clause.evalF_cons, Bool.or_assoc]
  | [] | [_] | [_, _] | [_, _, _] =>
    rw [shortenClause_short _ _ (by simp)]
    refine WindowExt.congr rfl ?_ (windowExt_plain (t := t) ?_)
    · intro g
      simp [CNF.evalF]
    · intro c' hc'
      simp at hc'
      subst hc'
      exact hc

theorem shortenClause_boundedClauses (t : ℕ) (c : Clause) : BoundedClauses (shortenClause t c).1 := by
  match c with
  | l₁ :: l₂ :: l₃ :: l₄ :: rest =>
    exact (orGadget_boundedClauses _ _ _).append (orChainAux_boundedClauses _ _ _)
  | [] | [_] | [_, _] | [_, _, _] =>
    rw [shortenClause_short _ _ (by simp)]
    simp [BoundedClauses]

theorem shortenClause_aux_le (t : ℕ) (c : Clause) : (shortenClause t c).2 ≤ c.length := by
  match c with
  | l₁ :: l₂ :: l₃ :: l₄ :: rest =>
    show rest.length + 2 ≤ (l₁ :: l₂ :: l₃ :: l₄ :: rest).length
    simp only [List.length_cons]
    omega
  | [] | [_] | [_, _] | [_, _, _] =>
    rw [shortenClause_short _ _ (by simp)]
    exact Nat.zero_le _

theorem shortenClause_length_le (t : ℕ) (c : Clause) :
    (shortenClause t c).1.length ≤ 3 * c.length + 1 := by
  match c with
  | l₁ :: l₂ :: l₃ :: l₄ :: rest =>
    show (orGadget t l₁ l₂ ++ shortenClause.orChainAux (t + 1) t (l₃ :: l₄ :: rest)).length ≤ _
    rw [List.length_append, orChainAux_length]
    simp only [orGadget, List.length_cons, List.length_nil]
    omega
  | [] | [_] | [_, _] | [_, _, _] =>
    rw [shortenClause_short _ _ (by simp)]
    simp

theorem shortenClause_varsLt (t : ℕ) (c : Clause) (hc : ∀ ℓ ∈ c, ℓ.var < t) :
    CNF.VarsLt (shortenClause t c).1 (t + (shortenClause t c).2) :=
  (windowExt_shortenClause t c hc).vars

/-- **Parsimonious long-clause conversion.** -/
theorem shortenClause_spec (t : ℕ) (c : Clause) (hc : ∀ ℓ ∈ c, ℓ.var < t) (g : ℕ → Bool) :
    (Clause.evalF g c = true → ∃! β : BitString (shortenClause t c).2,
        CNF.evalF (patch g t β) (shortenClause t c).1 = true) ∧
    (Clause.evalF g c = false → ∀ β : BitString (shortenClause t c).2,
        CNF.evalF (patch g t β) (shortenClause t c).1 = false) :=
  ⟨(windowExt_shortenClause t c hc).unique g,
    fun h ↦ (windowExt_shortenClause t c hc).none g (by rw [h]; decide)⟩

/-! ### Exact solution counts -/

open scoped Classical in
/-- **Exact solution count.** Solutions of a windowed extension at `[n, n + a)` are in bijection with
the bit vectors `α : BitString n` satisfying `P`. -/
theorem card_solutions_of_windowExt {ψ : CNF} {n a : ℕ} {P : (ℕ → Bool) → Prop}
    (h : WindowExt ψ n a P) :
    (solutions ψ (n + a)).card = (Finset.univ.filter fun α : BitString n ↦ P (toFun α)).card := by
  -- the unique window filling of each `α` with `P (toFun α)`
  have key : ∀ α : BitString n, P (toFun α) → ∃ β : BitString a,
      CNF.evalF (toFun (Fin.append α β)) ψ = true ∧
      ∀ β' : BitString a, CNF.evalF (toFun (Fin.append α β')) ψ = true → β' = β := by
    intro α hα
    simp only [toFun_append]
    exact h.unique (toFun α) hα
  choose! βof hβof huniq using key
  -- every solution projects to a bit vector satisfying `P`
  have hsol : ∀ γ : BitString (n + a), γ ∈ solutions ψ (n + a) →
      P (toFun fun i ↦ γ (Fin.castAdd a i)) ∧
      CNF.evalF (toFun (Fin.append (fun i ↦ γ (Fin.castAdd a i))
        (fun i ↦ γ (Fin.natAdd n i)))) ψ = true := by
    intro γ hγ
    rw [mem_solutions, ← Fin.append_castAdd_natAdd (f := γ)] at hγ
    refine ⟨?_, hγ⟩
    by_contra hP
    have := h.none _ hP (fun i ↦ γ (Fin.natAdd n i))
    rw [toFun_append, this] at hγ
    exact absurd hγ (by decide)
  symm
  refine Finset.card_bij' (fun α _ ↦ Fin.append α (βof α)) (fun γ _ ↦ fun i ↦ γ (Fin.castAdd a i))
    ?_ ?_ ?_ ?_
  · intro α hα
    rw [mem_solutions]
    exact hβof α (Finset.mem_filter.mp hα).2
  · intro γ hγ
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (hsol γ hγ).1⟩
  · intro α _
    funext i
    simp
  · intro γ hγ
    obtain ⟨hP, hev⟩ := hsol γ hγ
    rw [← huniq _ hP _ hev]
    exact Fin.append_castAdd_natAdd

theorem uniqueSat_of_windowExt {ψ : CNF} {n a : ℕ} {P : (ℕ → Bool) → Prop}
    (h : WindowExt ψ n a P) (hu : ∃! α : BitString n, P (toFun α)) : UniqueSat ψ (n + a) := by
  classical
  unfold UniqueSat
  rw [card_solutions_of_windowExt h, Finset.card_eq_one]
  obtain ⟨α₀, hα₀, huniq⟩ := hu
  refine ⟨α₀, ?_⟩
  ext α
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
  exact ⟨fun hα ↦ huniq α hα, fun e ↦ e ▸ hα₀⟩

theorem solutions_eq_empty_of_windowExt {ψ : CNF} {n a : ℕ} {P : (ℕ → Bool) → Prop}
    (h : WindowExt ψ n a P) (hu : ∀ α : BitString n, ¬ P (toFun α)) : solutions ψ (n + a) = ∅ := by
  classical
  rw [← Finset.card_eq_zero, card_solutions_of_windowExt h, Finset.card_eq_zero,
    Finset.filter_eq_empty_iff]
  intro α _
  exact hu α

end SparseGcd
