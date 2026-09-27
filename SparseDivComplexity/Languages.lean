import Complexitylib.Classes.Promise
import SparseDivComplexity.Encoding

/-!
# The languages `SparseRoot`, `DIV`, `NONDIV`

Encoded decision problems of the paper (Section 2), as total languages over `List Bool`.

* `SparseRoot = {(p, P) : p prime, P ∈ 𝔽_p[x] sparse, P has a root in 𝔽_p}` (Theorem 5).
* `DIV = {(p, f, g) : p prime, f, g ∈ 𝔽_p[x], g ≠ 0, g ∣ f}` and `NONDIV` its complement *on the
  same well-formed domain* `DivDomain`. Strings outside the domain (undecodable, non-prime modulus,
  coefficient not reduced modulo `p`, or `g = 0`) belong to neither language.

Well-formedness of a coefficient list means every coefficient is a canonical residue `< p`; repeated
exponents and zero coefficients are allowed (they are handled by `SparseDiv.normalize`).

The promise-problem view `divPromise` (yes = `DIV`, no = `NONDIV`) is also provided, using
complexitylib's `PromiseProblem`.

## Main results

* `NONDIV_eq_DivDomain_sdiff_DIV`, `mem_NONDIV_iff_not_mem_DIV` — complementarity on the domain
  (the "single oracle answer negated" convention of Theorem 6).
* `mem_SparseRoot_encRootInstance_iff`, `mem_NONDIV_encDivInstance_iff`,
  `mem_DIV_encDivInstance_iff` — membership of encoded well-formed instances.
* `yesInstance_mem_NONDIV`, `noInstance_mem_DIV`, `noInstance_not_mem_NONDIV` — the fixed instances
  `(2, 1, X)` and `(2, 0, 1)`.
-/

open Complexity Polynomial

namespace SparseDiv

/-- Well-formed coefficient lists: every coefficient is a canonical residue modulo `p`. -/
def WFTerms (p : ℕ) (l : Terms) : Prop := ∀ t ∈ l, t.1 < p

instance (p : ℕ) (l : Terms) : Decidable (WFTerms p l) := by
  unfold WFTerms; infer_instance

/-- **`SparseRoot`** (Theorem 5): encoded pairs `(p, P)` with `p` prime, `P` a well-formed sparse
polynomial over `𝔽_p`, and `P(a) = 0` for some `a ∈ 𝔽_p`. -/
def SparseRoot : Language :=
  {s | ∃ p l, decRootInstance s = some (p, l) ∧ p.Prime ∧ WFTerms p l ∧
    ∃ a : ZMod p, (toPoly p l).eval a = 0}

/-- The well-formed domain of divisibility instances: `p` prime, reduced coefficients, `g ≠ 0`. -/
def WFDiv (p : ℕ) (f g : Terms) : Prop :=
  p.Prime ∧ WFTerms p f ∧ WFTerms p g ∧ toPoly p g ≠ 0

/-- Encoded well-formed divisibility instances. -/
def DivDomain : Language :=
  {s | ∃ p f g, decDivInstance s = some (p, f, g) ∧ WFDiv p f g}

/-- **`DIV`**: well-formed `(p, f, g)` with `g ∣ f` in `𝔽_p[x]`. -/
def DIV : Language :=
  {s | ∃ p f g, decDivInstance s = some (p, f, g) ∧ WFDiv p f g ∧ toPoly p g ∣ toPoly p f}

/-- **`NONDIV`**: well-formed `(p, f, g)` with `g ∤ f` in `𝔽_p[x]`. -/
def NONDIV : Language :=
  {s | ∃ p f g, decDivInstance s = some (p, f, g) ∧ WFDiv p f g ∧ ¬ toPoly p g ∣ toPoly p f}

theorem DIV_subset_DivDomain : DIV ⊆ DivDomain := by
  rintro s ⟨p, f, g, hs, hwf, -⟩
  exact ⟨p, f, g, hs, hwf⟩

theorem NONDIV_subset_DivDomain : NONDIV ⊆ DivDomain := by
  rintro s ⟨p, f, g, hs, hwf, -⟩
  exact ⟨p, f, g, hs, hwf⟩

theorem disjoint_DIV_NONDIV : Disjoint DIV NONDIV := by
  rw [Set.disjoint_left]
  rintro s ⟨p, f, g, hs, -, hdvd⟩ ⟨p', f', g', hs', -, hndvd⟩
  rw [hs] at hs'
  simp only [Option.some.injEq, Prod.mk.injEq] at hs'
  obtain ⟨rfl, rfl, rfl⟩ := hs'
  exact hndvd hdvd

theorem DIV_union_NONDIV : DIV ∪ NONDIV = DivDomain := by
  ext s
  constructor
  · rintro (h | h)
    · exact DIV_subset_DivDomain h
    · exact NONDIV_subset_DivDomain h
  · rintro ⟨p, f, g, hs, hwf⟩
    by_cases hdvd : toPoly p g ∣ toPoly p f
    · exact Or.inl ⟨p, f, g, hs, hwf, hdvd⟩
    · exact Or.inr ⟨p, f, g, hs, hwf, hdvd⟩

/-- `NONDIV` is the complement of `DIV` relative to the well-formed domain. -/
theorem NONDIV_eq_DivDomain_sdiff_DIV : NONDIV = DivDomain \ DIV := by
  ext s
  constructor
  · intro h
    exact ⟨NONDIV_subset_DivDomain h, Set.disjoint_right.mp disjoint_DIV_NONDIV h⟩
  · rintro ⟨⟨p, f, g, hs, hwf⟩, hnot⟩
    exact ⟨p, f, g, hs, hwf, fun hdvd ↦ hnot ⟨p, f, g, hs, hwf, hdvd⟩⟩

/-- **Single-query negation** (Theorem 6): on the well-formed domain, membership in `NONDIV` is the
negated answer of a `DIV` oracle. -/
theorem mem_NONDIV_iff_not_mem_DIV {s : List Bool} (hs : s ∈ DivDomain) :
    s ∈ NONDIV ↔ s ∉ DIV := by
  rw [NONDIV_eq_DivDomain_sdiff_DIV, Set.mem_sdiff]
  exact and_iff_right hs

/-- The promise problem (yes = `DIV`, no = `NONDIV`) with promise `DivDomain`. -/
def divPromise : PromiseProblem :=
  ⟨DIV, NONDIV, disjoint_DIV_NONDIV⟩

theorem divPromise_promise : divPromise.promise = DivDomain := by
  rw [PromiseProblem.promise]
  exact DIV_union_NONDIV

/-- Membership of an encoded, well-formed `SparseRoot` instance. -/
theorem mem_SparseRoot_encRootInstance_iff {p : ℕ} {l : Terms} (hp : p.Prime) (hl : WFTerms p l) :
    encRootInstance p l ∈ SparseRoot ↔ ∃ a : ZMod p, (toPoly p l).eval a = 0 := by
  constructor
  · rintro ⟨p', l', h, -, -, ha⟩
    rw [decRootInstance_encRootInstance] at h
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ha
  · intro ha
    exact ⟨p, l, decRootInstance_encRootInstance p l, hp, hl, ha⟩

/-- An encoded instance is in `SparseRoot` only if it is well formed. -/
theorem mem_SparseRoot_encRootInstance {p : ℕ} {l : Terms} (h : encRootInstance p l ∈ SparseRoot) :
    p.Prime ∧ WFTerms p l ∧ ∃ a : ZMod p, (toPoly p l).eval a = 0 := by
  obtain ⟨p', l', h, hp, hl, ha⟩ := h
  rw [decRootInstance_encRootInstance] at h
  simp only [Option.some.injEq, Prod.mk.injEq] at h
  obtain ⟨rfl, rfl⟩ := h
  exact ⟨hp, hl, ha⟩

theorem mem_DivDomain_encDivInstance_iff {p : ℕ} {f g : Terms} :
    encDivInstance p f g ∈ DivDomain ↔ WFDiv p f g := by
  constructor
  · rintro ⟨p', f', g', h, hwf⟩
    rw [decDivInstance_encDivInstance] at h
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl, rfl⟩ := h
    exact hwf
  · intro hwf
    exact ⟨p, f, g, decDivInstance_encDivInstance p f g, hwf⟩

/-- Membership of an encoded instance in `NONDIV`. -/
theorem mem_NONDIV_encDivInstance_iff {p : ℕ} {f g : Terms} :
    encDivInstance p f g ∈ NONDIV ↔ WFDiv p f g ∧ ¬ toPoly p g ∣ toPoly p f := by
  constructor
  · rintro ⟨p', f', g', h, hwf, hndvd⟩
    rw [decDivInstance_encDivInstance] at h
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl, rfl⟩ := h
    exact ⟨hwf, hndvd⟩
  · rintro ⟨hwf, hndvd⟩
    exact ⟨p, f, g, decDivInstance_encDivInstance p f g, hwf, hndvd⟩

/-- Membership of an encoded instance in `DIV`. -/
theorem mem_DIV_encDivInstance_iff {p : ℕ} {f g : Terms} :
    encDivInstance p f g ∈ DIV ↔ WFDiv p f g ∧ toPoly p g ∣ toPoly p f := by
  constructor
  · rintro ⟨p', f', g', h, hwf, hdvd⟩
    rw [decDivInstance_encDivInstance] at h
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl, rfl⟩ := h
    exact ⟨hwf, hdvd⟩
  · rintro ⟨hwf, hdvd⟩
    exact ⟨p, f, g, decDivInstance_encDivInstance p f g, hwf, hdvd⟩

/-- Undecodable strings are in neither language. -/
theorem not_mem_NONDIV_of_decDivInstance_eq_none {s : List Bool} (h : decDivInstance s = none) :
    s ∉ NONDIV := by
  rintro ⟨p, f, g, hs, -⟩
  rw [h] at hs
  cases hs

theorem not_mem_SparseRoot_of_decRootInstance_eq_none {s : List Bool}
    (h : decRootInstance s = none) : s ∉ SparseRoot := by
  rintro ⟨p, l, hs, -⟩
  rw [h] at hs
  cases hs

/-- The fixed YES instance of `NONDIV`: `(p, f, g) = (2, 1, X)`. -/
def yesInstance : List Bool := encDivInstance 2 [(1, 0)] [(1, 1)]

/-- The fixed NO instance of `NONDIV` (a YES instance of `DIV`): `(p, f, g) = (2, 0, 1)`. -/
def noInstance : List Bool := encDivInstance 2 [] [(1, 0)]

theorem yesInstance_mem_NONDIV : yesInstance ∈ NONDIV := by
  have := Fact.mk Nat.prime_two
  refine mem_NONDIV_encDivInstance_iff.mpr ⟨⟨Nat.prime_two, ?_, ?_, ?_⟩, ?_⟩
  · decide
  · decide
  · simp [toPoly_cons]
  · simp [toPoly_cons, Polynomial.X_dvd_iff]

theorem noInstance_mem_DIV : noInstance ∈ DIV := by
  have := Fact.mk Nat.prime_two
  refine mem_DIV_encDivInstance_iff.mpr ⟨⟨Nat.prime_two, ?_, ?_, ?_⟩, ?_⟩
  · decide
  · decide
  · simp [toPoly_cons]
  · simp

theorem noInstance_not_mem_NONDIV : noInstance ∉ NONDIV :=
  Set.disjoint_left.mp disjoint_DIV_NONDIV noInstance_mem_DIV

theorem yesInstance_not_mem_DIV : yesInstance ∉ DIV :=
  Set.disjoint_right.mp disjoint_DIV_NONDIV yesInstance_mem_NONDIV

end SparseDiv
