import Complexitylib.Classes.NP.Reduction
import Complexitylib.Classes.NP.CoNP
import Complexitylib.Classes.Randomized
import Complexitylib.Classes.EventProb
import Complexitylib.Classes.Promise
import Complexitylib.Classes.P.Cobham.Internal
import Mathlib.Data.Fin.Tuple.Take
import SparseDivComplexity.Languages

/-!
# Randomized (BPP) many-one reductions

complexitylib's `NPHard` is deterministic Karp hardness. The paper's Theorems 5 and 6 are about
NP-hardness *under BPP many-one reductions*, which we formalize here in the **random-tape** form:
a reduction is a deterministic polynomial-time function `f ∈ FP` applied to the input paired with a
uniformly random string `r` of length `ℓ(|x|)` (a polynomial), and it must be correct with probability
at least `2/3` on *every* input.

Targets are `PromiseProblem`s (complexitylib), because the paper's problems live on a well-formed
domain: the reduction must always output an instance on the correct side of the promise. Total
languages are the special case `PromiseProblem.ofLanguage`.

The connection with complexitylib's probabilistic Turing machine semantics (`NTM.acceptProb`,
`BPP`) is established in `Randomized/RandomTape.lean`:

* every polynomial-time PTM has an `FP` verdict function on `pair x choices`
  (via `Complexity.Cobham.acceptChoiceFn`);
* conversely a random-tape decider is realized by a PTM (`mem_BPP_of_randomTape`).

## Main definitions

* `SparseDiv.MapReducesBPP L Q` — random-tape BPP many-one reduction from a language to a promise
  problem; `SparseDiv.NPHardBPP Q`, `SparseDiv.coNPHardBPP Q`.
* `SparseDiv.PromiseBPP Q` — a polynomial-time PTM correct with bounded error on the promise.
* `SparseDiv.RandomTapeSolves Q V ℓ`, `SparseDiv.PromiseRandomTapeBPP Q` — random-tape solvers.
* `SparseDiv.RootDomain`, `SparseDiv.rootPromise`, `SparseDiv.nondivPromise` — the paper's
  problems as promise problems (yes = `SparseRoot`, resp. yes = `NONDIV`, no = `DIV`).
-/

open Complexity

namespace SparseDiv

open scoped Classical in
/-- The seeds of length `m` on which the random-tape map `f` sends `x` to the correct side of `Q`. -/
noncomputable def goodSeeds (L : Language) (Q : PromiseProblem) (f : List Bool → List Bool)
    (x : List Bool) (m : ℕ) : Finset (Fin m → Bool) :=
  Finset.univ.filter fun r ↦
    (x ∈ L → f (pair x (List.ofFn r)) ∈ Q.yesInstances) ∧
    (x ∉ L → f (pair x (List.ofFn r)) ∈ Q.noInstances)

/-- **Random-tape BPP many-one reduction** from the language `L` to the promise problem `Q`: a
polynomial-time function of `pair x r` which, for a uniformly random seed `r` of polynomial length
`ℓ(|x|)`, lands on the correct side of `Q` with probability at least `2/3`, for every `x`. -/
def MapReducesBPP (L : Language) (Q : PromiseProblem) : Prop :=
  ∃ (f : List Bool → List Bool) (ℓ : Polynomial ℕ), f ∈ FP ∧
    ∀ x : List Bool, (2 : ℚ) / 3 ≤ eventProb (goodSeeds L Q f x (ℓ.eval x.length))

/-- NP-hardness under BPP many-one reductions (the paper's "NP-hard under BPP many-one
reductions"). -/
def NPHardBPP (Q : PromiseProblem) : Prop := ∀ L ∈ NP, MapReducesBPP L Q

/-- coNP-hardness under BPP many-one reductions. -/
def coNPHardBPP (Q : PromiseProblem) : Prop := ∀ L ∈ coNP, MapReducesBPP L Q

/-- **Promise-BPP solver**: a polynomial-time PTM (all paths halt within a polynomial bound) that
accepts every yes-instance with probability `≥ 2/3` and every no-instance with probability `≤ 1/3`.
Its behaviour outside the promise is unconstrained. This is the paper's "randomized bounded-error
algorithm for `DIV`". -/
def PromiseBPP (Q : PromiseProblem) : Prop :=
  ∃ (k : ℕ) (tm : NTM k) (T : ℕ → ℕ) (d : ℕ), tm.AllPathsHaltIn T ∧ T =O (· ^ d) ∧
    (∀ x ∈ Q.yesInstances, (2 : ℚ) / 3 ≤ tm.acceptProb x (T x.length)) ∧
    (∀ x ∈ Q.noInstances, tm.acceptProb x (T x.length) ≤ 1 / 3)

open scoped Classical in
/-- The seeds on which the verdict function `V` answers `x`'s membership in the yes-side of `Q`
correctly (verdict `[true]` means "yes"). -/
noncomputable def goodVerdictSeeds (Q : PromiseProblem) (V : List Bool → List Bool)
    (x : List Bool) (m : ℕ) : Finset (Fin m → Bool) :=
  Finset.univ.filter fun r ↦ (V (pair x (List.ofFn r)) = [true] ↔ x ∈ Q.yesInstances)

/-- A verdict function `V` with seed length `ℓ` solves `Q` on its promise with error `≤ 1/3`. -/
def RandomTapeSolves (Q : PromiseProblem) (V : List Bool → List Bool) (ℓ : Polynomial ℕ) : Prop :=
  ∀ x ∈ Q.promise, (2 : ℚ) / 3 ≤ eventProb (goodVerdictSeeds Q V x (ℓ.eval x.length))

/-- Random-tape polynomial-time bounded-error solvability of a promise problem. -/
def PromiseRandomTapeBPP (Q : PromiseProblem) : Prop :=
  ∃ (V : List Bool → List Bool) (ℓ : Polynomial ℕ), V ∈ FP ∧ RandomTapeSolves Q V ℓ

/-! ## The paper's problems as promise problems -/

/-- Well-formed `SparseRoot` instances: encoded `(p, P)` with `p` prime and reduced coefficients. -/
def RootDomain : Language :=
  {s | ∃ p l, decRootInstance s = some (p, l) ∧ p.Prime ∧ WFTerms p l}

theorem SparseRoot_subset_RootDomain : SparseRoot ⊆ RootDomain := by
  rintro s ⟨p, l, hdec, hp, hl, -⟩
  exact ⟨p, l, hdec, hp, hl⟩

/-- The `SparseRoot` problem on its well-formed domain (yes = has a root, no = well formed without
root). -/
def rootPromise : PromiseProblem :=
  ⟨SparseRoot, RootDomain \ SparseRoot, Set.disjoint_sdiff_right⟩

theorem rootPromise_promise : rootPromise.promise = RootDomain := by
  show SparseRoot ∪ (RootDomain \ SparseRoot) = RootDomain
  exact Set.union_sdiff_cancel SparseRoot_subset_RootDomain

/-- The `NONDIV` problem on the well-formed domain: yes = `NONDIV`, no = `DIV`. -/
def nondivPromise : PromiseProblem :=
  ⟨NONDIV, DIV, disjoint_DIV_NONDIV.symm⟩

theorem nondivPromise_promise : nondivPromise.promise = DivDomain := by
  show NONDIV ∪ DIV = DivDomain
  rw [Set.union_comm]
  exact DIV_union_NONDIV

/-- Negating the single oracle answer: `nondivPromise` is the complement of `divPromise`. -/
theorem nondivPromise_eq_complement_divPromise : nondivPromise = divPromise.complement := by
  rfl

theorem divPromise_eq_complement_nondivPromise : divPromise = nondivPromise.complement := by
  rfl

/-! ## Elementary closure properties -/

/-- Membership in `goodSeeds`, unfolded. -/
private theorem mem_goodSeeds {L : Language} {Q : PromiseProblem} {f : List Bool → List Bool}
    {x : List Bool} {m : ℕ} {r : Fin m → Bool} :
    r ∈ goodSeeds L Q f x m ↔
      (x ∈ L → f (pair x (List.ofFn r)) ∈ Q.yesInstances) ∧
        (x ∉ L → f (pair x (List.ofFn r)) ∈ Q.noInstances) := by
  simp only [goodSeeds, Finset.mem_filter, Finset.mem_univ, true_and]

/-- If every seed of length `m` is good, the success probability is `1 ≥ 2/3`. -/
private theorem two_thirds_le_eventProb_goodSeeds {L : Language} {Q : PromiseProblem}
    {f : List Bool → List Bool} {x : List Bool} {m : ℕ}
    (h : ∀ r : Fin m → Bool, r ∈ goodSeeds L Q f x m) :
    (2 : ℚ) / 3 ≤ eventProb (goodSeeds L Q f x m) := by
  rw [Finset.eq_univ_iff_forall.mpr h, eventProb_univ]
  norm_num

/-- Restricting a uniformly random string of length `m ≥ k` to its first `k` bits is uniform: an
event depending only on that prefix has the probability of the prefix event. -/
private theorem eventProb_filter_take_mem {k m : ℕ} (hk : k ≤ m) (E : Finset (Fin k → Bool)) :
    eventProb (Finset.univ.filter fun w : Fin m → Bool ↦ Fin.take k hk w ∈ E) = eventProb E := by
  obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le hk
  have h := eventProb_block (fun s : Fin k → Bool ↦ s ∈ E) (fun _ : Fin j → Bool ↦ True)
  simp only [and_true, Finset.filter_true, eventProb_univ, mul_one, Finset.filter_mem_eq_inter,
    Finset.univ_inter] at h
  exact h

/-- A deterministic Karp reduction is a (trivially correct) BPP reduction. -/
theorem MapReducesPoly.mapReducesBPP {L L' : Language} (h : L ≤ₚ L') :
    MapReducesBPP L (PromiseProblem.ofLanguage L') := by
  obtain ⟨f, hf, hL⟩ := h
  refine ⟨f ∘ pairFst, 0, mem_FP_comp pairFst_mem_FP hf, fun x ↦ ?_⟩
  refine two_thirds_le_eventProb_goodSeeds fun r ↦ mem_goodSeeds.mpr ?_
  simp only [Function.comp_apply, pairFst_pair, PromiseProblem.ofLanguage, Set.mem_compl_iff]
  exact ⟨fun hx ↦ (hL x).mp hx, fun hx hx' ↦ hx ((hL x).mpr hx')⟩

/-- A deterministic side-preserving reduction into a promise problem is a BPP reduction. -/
theorem mapReducesBPP_of_mapReducesPoly {L : Language} {Q : PromiseProblem}
    (h : (PromiseProblem.ofLanguage L).MapReducesPoly Q) : MapReducesBPP L Q := by
  obtain ⟨f, hf, hyes, hno⟩ := h
  refine ⟨f ∘ pairFst, 0, mem_FP_comp pairFst_mem_FP hf, fun x ↦ ?_⟩
  refine two_thirds_le_eventProb_goodSeeds fun r ↦ mem_goodSeeds.mpr ?_
  simp only [Function.comp_apply, pairFst_pair]
  exact ⟨fun hx ↦ hyes x hx, fun hx ↦ hno x hx⟩

/-- **Postcomposition with a deterministic bridge.** A BPP reduction followed by a deterministic
polynomial-time side-preserving map is a BPP reduction, with the same seeds and the same success
probability. -/
theorem MapReducesBPP.trans_poly {L : Language} {Q Q' : PromiseProblem}
    (h : MapReducesBPP L Q) (h' : Q.MapReducesPoly Q') : MapReducesBPP L Q' := by
  obtain ⟨f, ℓ, hf, hgood⟩ := h
  obtain ⟨g, hg, hyes, hno⟩ := h'
  refine ⟨g ∘ f, ℓ, mem_FP_comp hf hg, fun x ↦ (hgood x).trans (eventProb_mono fun r hr ↦ ?_)⟩
  rw [mem_goodSeeds] at hr ⊢
  exact ⟨fun hx ↦ hyes _ (hr.1 hx), fun hx ↦ hno _ (hr.2 hx)⟩

/-- **Precomposition with a deterministic reduction.** -/
theorem MapReducesPoly.trans_bpp {L L' : Language} {Q : PromiseProblem}
    (h : L ≤ₚ L') (h' : MapReducesBPP L' Q) : MapReducesBPP L Q := by
  obtain ⟨g, hg, hL⟩ := h
  obtain ⟨f, ℓ, hf, hgood⟩ := h'
  -- `|g x|` is polynomially bounded, so `ℓ(|g x|) ≤ (ℓ ∘ p)(|x|)`.
  obtain ⟨p, hp⟩ := Cobham.output_length_poly_of_mem_FP hg
  -- The new map feeds `f` the image `g x` together with the first `ℓ(|g x|)` random bits.
  have hgp : g ∘ pairFst ∈ FP := mem_FP_comp pairFst_mem_FP hg
  have htake : (fun s ↦ (pairSnd s).take (ℓ.eval (g (pairFst s)).length)) ∈ FP := by
    apply CobhamFP_subset_FP
    have h1 : Cobham fun v : Fin 1 → List Bool ↦ (g ∘ pairFst) (v 0) := FP_subset_CobhamFP hgp
    have h2 : Cobham fun v : Fin 1 → List Bool ↦ pairSnd (v 0) :=
      FP_subset_CobhamFP pairSnd_mem_FP
    show Cobham fun v : Fin 1 → List Bool ↦ (pairSnd (v 0)).take (ℓ.eval (g (pairFst (v 0))).length)
    exact (Cobham.takeFn (Cobham.polyLen_mem ℓ h1) h2).of_eq fun v ↦ by simp
  refine ⟨fun s ↦ f (pair (g (pairFst s)) ((pairSnd s).take (ℓ.eval (g (pairFst s)).length))),
    ℓ.comp p, mem_FP_comp (mem_FP_pair hgp htake) hf, fun x ↦ ?_⟩
  have hk : ℓ.eval (g x).length ≤ (ℓ.comp p).eval x.length := by
    rw [Polynomial.eval_comp]
    exact polynomial_eval_mono_nat ℓ (hp x)
  refine (hgood (g x)).trans_eq ?_
  rw [← eventProb_filter_take_mem hk]
  congr 1
  ext r
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, mem_goodSeeds, pairFst_pair,
    pairSnd_pair, Fin.ofFn_take_eq_take_ofFn, hL x]

/-- Hardness under BPP reductions transfers along deterministic side-preserving reductions. -/
theorem NPHardBPP.of_mapReducesPoly {Q Q' : PromiseProblem} (h : NPHardBPP Q)
    (h' : Q.MapReducesPoly Q') : NPHardBPP Q' :=
  fun L hL ↦ (h L hL).trans_poly h'

theorem coNPHardBPP.of_mapReducesPoly {Q Q' : PromiseProblem} (h : coNPHardBPP Q)
    (h' : Q.MapReducesPoly Q') : coNPHardBPP Q' :=
  fun L hL ↦ (h L hL).trans_poly h'

/-- Deterministic NP-hardness implies NP-hardness under BPP reductions. -/
theorem NPHard.npHardBPP {L : Language} (h : NPHard L) : NPHardBPP (PromiseProblem.ofLanguage L) :=
  fun L' hL' ↦ MapReducesPoly.mapReducesBPP (h L' hL')

/-- **Complementation (single-query negation).** The same map reduces `Lᶜ` to the complemented
promise problem. -/
theorem MapReducesBPP.compl {L : Language} {Q : PromiseProblem} (h : MapReducesBPP L Q) :
    MapReducesBPP Lᶜ Q.complement := by
  obtain ⟨f, ℓ, hf, hgood⟩ := h
  refine ⟨f, ℓ, hf, fun x ↦ (hgood x).trans (eventProb_mono fun r hr ↦ ?_)⟩
  rw [mem_goodSeeds] at hr ⊢
  exact ⟨fun hx ↦ hr.2 hx, fun hx ↦ hr.1 (Set.notMem_compl_iff.mp hx)⟩

/-- NP-hardness of `Q` under BPP reductions is coNP-hardness of its complement. -/
theorem NPHardBPP.compl {Q : PromiseProblem} (h : NPHardBPP Q) : coNPHardBPP Q.complement := by
  intro L hL
  have hred := (h Lᶜ (mem_complClass.mp hL)).compl
  rwa [compl_compl] at hred

theorem coNPHardBPP.compl {Q : PromiseProblem} (h : coNPHardBPP Q) : NPHardBPP Q.complement := by
  intro L hL
  have hred := (h Lᶜ (compl_mem_coNP_iff.mpr hL)).compl
  rwa [compl_compl] at hred

/-- A total BPP language is a promise-BPP solver of its own promise problem. -/
theorem promiseBPP_ofLanguage_of_mem_BPP {L : Language} (h : L ∈ BPP) :
    PromiseBPP (PromiseProblem.ofLanguage L) := by
  obtain ⟨d, k, tm, T, hhalt, hacc, hrej, hT⟩ := Set.mem_iUnion.mp h
  exact ⟨k, tm, T, d, hhalt, hT, fun x hx ↦ hacc x hx, fun x hx ↦ hrej x hx⟩

/-- Conversely, a promise-BPP solver of a total promise problem witnesses `BPP` membership. -/
theorem mem_BPP_of_promiseBPP_ofLanguage {L : Language} (h : PromiseBPP (PromiseProblem.ofLanguage L)) :
    L ∈ BPP := by
  obtain ⟨k, tm, T, d, hhalt, hT, hyes, hno⟩ := h
  exact Set.mem_iUnion.mpr ⟨d, k, tm, T, hhalt, fun x hx ↦ hyes x hx, fun x hx ↦ hno x hx, hT⟩

/-- A promise-BPP solver of `Q` solves `Q.complement` after negating its answer — stated at the
level of acceptance probabilities: the *same* machine is a solver of `Q.complement` once its accept
condition is negated. Concretely we only need the consequence used later: membership of a total
language in `BPP` gives a solver for any promise problem it completes. -/
theorem promiseBPP_of_mem_promiseClass_BPP {Q : PromiseProblem} (h : Q ∈ PromiseClass BPP) :
    PromiseBPP Q := by
  obtain ⟨M, hM, hyes, hdisj⟩ := h
  obtain ⟨k, tm, T, d, hhalt, hT, hacc, hrej⟩ := promiseBPP_ofLanguage_of_mem_BPP hM
  exact ⟨k, tm, T, d, hhalt, hT, fun x hx ↦ hacc x (hyes hx),
    fun x hx ↦ hrej x (Set.disjoint_right.mp hdisj hx)⟩

/-- Promise solvers of `Q` are solvers of any promise problem with smaller yes- and no-sides. -/
theorem PromiseBPP.mono {Q Q' : PromiseProblem} (h : PromiseBPP Q)
    (hyes : Q'.yesInstances ⊆ Q.yesInstances) (hno : Q'.noInstances ⊆ Q.noInstances) :
    PromiseBPP Q' := by
  obtain ⟨k, tm, T, d, hhalt, hT, hacc, hrej⟩ := h
  exact ⟨k, tm, T, d, hhalt, hT, fun x hx ↦ hacc x (hyes hx), fun x hx ↦ hrej x (hno hx)⟩

end SparseDiv
