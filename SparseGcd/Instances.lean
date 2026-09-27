import SparseGcd.Poly.Gcd
import SparseDivComplexity.Encoding
import SparseDivComplexity.Languages
import SparseDivComplexity.Randomized.Defs
import Complexitylib.Models.TuringMachine

/-!
# Problems and solver hypotheses

* **Sparse GCD (function problem, Theorem 18).** Instances `(p, f, g)` reuse the encoding
  `encDivInstance` of the divisibility project. Well-formed: `p` prime, `f`, `g` canonical
  (normalized) term lists. The correct output is the canonical term list of the monic gcd
  (`gcdTerms`; `gcd(0,0) = 0` with empty support). An *output-sensitive solver* is a deterministic
  Turing machine which, on every well-formed instance, halts within `time(T + bitLength Δ + bitLength p)`
  steps with the correct output on its output tape, where `T` is the largest of the three supports
  (input and output) and `Δ` the largest degree. Nothing is assumed off the well-formed domain.

* **Roots-of-unity detection (decision problem, Theorem 19).** Instances `(p, f, n)` with `p`
  prime, `f` normalized, `n ≥ 1`; yes-instances: `f` and `X^n - 1` are *not* coprime
  (equivalently `deg gcd(f, X^n - 1) > 0`). Note the polarity: "not coprime" is the yes side.
-/

open Complexity SparseDiv Polynomial

namespace SparseGcd

/-! ### Sparse GCD -/

/-- Well-formed gcd instance: prime field, canonical inputs. -/
def WFGcd (p : ℕ) (f g : Terms) : Prop := p.Prime ∧ Normalized p f ∧ Normalized p g

/-- The canonical sparse output. -/
noncomputable def gcdTerms (p : ℕ) [Fact p.Prime] (f g : Terms) : Terms :=
  termsOf p (monicGcd (toPoly p f) (toPoly p g))

/-- The size parameter `T + bitLength Δ + bitLength p` of an instance together with its answer. -/
noncomputable def gcdParam (p : ℕ) [Fact p.Prime] (f g : Terms) : ℕ :=
  max (max f.length g.length) (gcdTerms p f g).length +
    Nat.size (max (toPoly p f).natDegree (toPoly p g).natDegree) + Nat.size p

/-- A machine halts on `x` within `t` steps with `y` on its output tape. -/
def OutputsWithin {k : ℕ} (tm : TM k) (x y : List Bool) (t : ℕ) : Prop :=
  ∃ c' s, s ≤ t ∧ tm.reachesIn s (tm.initCfg x) c' ∧ tm.halted c' ∧ c'.output.HasOutput y

/-- **Hypothesis of Theorem 18**: an output-sensitive sparse gcd solver. -/
structure GcdSolver where
  k : ℕ
  tm : TM k
  /-- Time bound, a polynomial in `T + bitLength Δ + bitLength p`. -/
  time : Polynomial ℕ
  correct : ∀ p f g, (h : WFGcd p f g) →
    haveI : Fact p.Prime := ⟨h.1⟩
    OutputsWithin tm (encDivInstance p f g) (encTerms (gcdTerms p f g)) (time.eval (gcdParam p f g))

/-! ### Roots-of-unity detection -/

/-- Encoding of `(p, f, n)`. -/
def encRouInstance (p : ℕ) (f : Terms) (n : ℕ) : List Bool :=
  pair (encNat p) (pair (encTerms f) (encNat n))

def decRouInstance (s : List Bool) : Option (ℕ × Terms × ℕ) :=
  (unpair? s).bind fun ar ↦
    (unpair? ar.2).bind fun fn ↦
      (decTerms fn.1).map fun f ↦ (decNat ar.1, f, decNat fn.2)

theorem decRouInstance_encRouInstance (p : ℕ) (f : Terms) (n : ℕ) :
    decRouInstance (encRouInstance p f n) = some (p, f, n) := by
  simp [decRouInstance, encRouInstance]

theorem encRouInstance_injective :
    Function.Injective fun t : ℕ × Terms × ℕ ↦ encRouInstance t.1 t.2.1 t.2.2 := by
  rintro ⟨p, f, n⟩ ⟨p', f', n'⟩ h
  have := congrArg decRouInstance h
  simp only [decRouInstance_encRouInstance, Option.some.injEq, Prod.mk.injEq] at this
  obtain ⟨rfl, rfl, rfl⟩ := this
  rfl

/-- Well-formed instances. -/
def WFRou (p : ℕ) (f : Terms) (n : ℕ) : Prop := p.Prime ∧ Normalized p f ∧ 1 ≤ n

def RouDomain : Language := {s | ∃ p f n, decRouInstance s = some (p, f, n) ∧ WFRou p f n}

/-- **Roots-of-unity detection**: `f` and `X^n - 1` are not coprime. -/
def RootsOfUnity : Language :=
  {s | ∃ p f n, decRouInstance s = some (p, f, n) ∧ WFRou p f n ∧
    ¬ IsCoprime (toPoly p f) (X ^ n - 1 : (ZMod p)[X])}

/-- The complementary side inside the domain: coprime. -/
def CoprimeRou : Language :=
  {s | ∃ p f n, decRouInstance s = some (p, f, n) ∧ WFRou p f n ∧
    IsCoprime (toPoly p f) (X ^ n - 1 : (ZMod p)[X])}

theorem disjoint_RootsOfUnity_CoprimeRou : Disjoint RootsOfUnity CoprimeRou := by
  rw [Set.disjoint_left]
  rintro s ⟨p, f, n, hs, _, hnc⟩ ⟨p', f', n', hs', _, hc⟩
  rw [hs, Option.some.injEq, Prod.mk.injEq, Prod.mk.injEq] at hs'
  obtain ⟨rfl, rfl, rfl⟩ := hs'
  exact hnc hc

/-- The promise problem (yes: not coprime; no: coprime). -/
def rouPromise : PromiseProblem := ⟨RootsOfUnity, CoprimeRou, disjoint_RootsOfUnity_CoprimeRou⟩

theorem rouPromise_promise : rouPromise.promise = RouDomain := by
  ext s
  simp only [PromiseProblem.promise, rouPromise, Set.mem_union, RootsOfUnity, CoprimeRou, RouDomain,
    Set.mem_setOf_eq]
  constructor
  · rintro (⟨p, f, n, hs, hwf, _⟩ | ⟨p, f, n, hs, hwf, _⟩) <;> exact ⟨p, f, n, hs, hwf⟩
  · rintro ⟨p, f, n, hs, hwf⟩
    by_cases hc : IsCoprime (toPoly p f) (X ^ n - 1 : (ZMod p)[X])
    · exact Or.inr ⟨p, f, n, hs, hwf, hc⟩
    · exact Or.inl ⟨p, f, n, hs, hwf, hc⟩

theorem mem_RootsOfUnity_encRouInstance_iff {p : ℕ} {f : Terms} {n : ℕ} :
    encRouInstance p f n ∈ RootsOfUnity ↔
      WFRou p f n ∧ ¬ IsCoprime (toPoly p f) (X ^ n - 1 : (ZMod p)[X]) := by
  constructor
  · rintro ⟨p', f', n', hs, hwf, hnc⟩
    rw [decRouInstance_encRouInstance, Option.some.injEq, Prod.mk.injEq, Prod.mk.injEq] at hs
    obtain ⟨rfl, rfl, rfl⟩ := hs
    exact ⟨hwf, hnc⟩
  · rintro ⟨hwf, hnc⟩
    exact ⟨p, f, n, decRouInstance_encRouInstance p f n, hwf, hnc⟩

theorem mem_CoprimeRou_encRouInstance_iff {p : ℕ} {f : Terms} {n : ℕ} :
    encRouInstance p f n ∈ CoprimeRou ↔
      WFRou p f n ∧ IsCoprime (toPoly p f) (X ^ n - 1 : (ZMod p)[X]) := by
  constructor
  · rintro ⟨p', f', n', hs, hwf, hc⟩
    rw [decRouInstance_encRouInstance, Option.some.injEq, Prod.mk.injEq, Prod.mk.injEq] at hs
    obtain ⟨rfl, rfl, rfl⟩ := hs
    exact ⟨hwf, hc⟩
  · rintro ⟨hwf, hc⟩
    exact ⟨p, f, n, decRouInstance_encRouInstance p f n, hwf, hc⟩

/-- "Not coprime" is "positive gcd degree" (`X^n - 1 ≠ 0`). -/
theorem not_isCoprime_iff_natDegree_pos {p : ℕ} [Fact p.Prime] (f : (ZMod p)[X]) {n : ℕ} (hn : 1 ≤ n) :
    ¬ IsCoprime f (X ^ n - 1 : (ZMod p)[X]) ↔ 0 < (monicGcd f (X ^ n - 1)).natDegree :=
  not_isCoprime_iff_natDegree_monicGcd_pos (Or.inr (by
    rw [← C_1]; exact X_pow_sub_C_ne_zero hn 1))

/-- The language is in the domain. -/
theorem RootsOfUnity_subset_RouDomain : RootsOfUnity ⊆ RouDomain := by
  rintro s ⟨p, f, n, hs, hwf, _⟩
  exact ⟨p, f, n, hs, hwf⟩

theorem CoprimeRou_subset_RouDomain : CoprimeRou ⊆ RouDomain := by
  rintro s ⟨p, f, n, hs, hwf, _⟩
  exact ⟨p, f, n, hs, hwf⟩

theorem RouDomain_eq_union : RouDomain = RootsOfUnity ∪ CoprimeRou :=
  rouPromise_promise.symm

/-- Membership of the language `RootsOfUnity` in `P` or `BPP` gives a promise-BPP solver. -/
theorem promiseBPP_rouPromise_of_mem_BPP (h : RootsOfUnity ∈ BPP) : SparseDiv.PromiseBPP rouPromise :=
  (promiseBPP_ofLanguage_of_mem_BPP h).mono (fun _ hx ↦ hx)
    fun _ hx ↦ Set.disjoint_right.mp disjoint_RootsOfUnity_CoprimeRou hx

theorem promiseBPP_rouPromise_of_mem_P (h : RootsOfUnity ∈ P) : SparseDiv.PromiseBPP rouPromise :=
  promiseBPP_rouPromise_of_mem_BPP (P_subset_BPP h)

end SparseGcd
