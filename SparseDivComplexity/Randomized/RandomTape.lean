import Complexitylib.Classes.P.Cobham.Internal.ChoiceSim
import Complexitylib.Classes.PH.SipserLautemann.Verdict
import SparseDivComplexity.Randomized.Defs
import SparseDivComplexity.Randomized.Machine

/-!
# Random-tape verdicts versus probabilistic Turing machines

The randomized notions of `Randomized/Defs.lean` are phrased with a deterministic `FP` verdict
function applied to `pair x r` for a uniformly random seed `r`. This module connects them with
complexitylib's probabilistic machine semantics (`NTM.acceptProb`, `PromiseBPP`, `BPP`):

* **PTM ⇒ random tape** (`promiseRandomTapeBPP_of_promiseBPP`): the deterministic simulation of a
  probabilistic machine along an explicit choice string is in Cobham's algebra
  (`Complexity.Cobham.acceptChoiceFn`, `acceptChoiceFn_eq_true_iff`), and since all paths halt
  within the polynomial bound, the acceptance probability over seeds of any longer polynomial
  length is the machine's acceptance probability (`NTM.acceptProb_eq_of_le_of_allChoicesHalt`).
* **random tape ⇒ PTM** (`mem_BPP_of_randomTape`): a random-tape decider is realized by a
  probabilistic machine that first guesses its seed and then runs the deterministic verdict
  machine. This is the only place where a new machine construction is required; see the docstring
  for the precise statement.
-/

open Complexity

namespace SparseDiv

/-- A ruler long enough for `Complexity.Cobham.acceptChoiceFn` on the pair `z = pair x c`:
`|z| + card Q + 3 ≥ |x| + |c| + card Q + 3`. -/
def verdictRuler (q : ℕ) (z : List Bool) : List Bool := z ++ List.replicate (q + 3) true

/-- The deterministic verdict of the probabilistic machine `tm` on `pair x c`: run `tm` along the
choice string `c` and report whether it halted accepting. -/
noncomputable def ptmVerdict {k : ℕ} (tm : NTM k) (z : List Bool) : List Bool :=
  Cobham.acceptChoiceFn tm (verdictRuler (Fintype.card tm.Q) z) (pairFst z) (pairSnd z)

theorem ptmVerdict_mem_FP {k : ℕ} (tm : NTM k) : ptmVerdict tm ∈ FP := by
  apply CobhamFP_subset_FP
  have hx : Cobham fun v : Fin 1 → List Bool ↦ pairFst (v 0) := FP_subset_CobhamFP pairFst_mem_FP
  have hc : Cobham fun v : Fin 1 → List Bool ↦ pairSnd (v 0) := FP_subset_CobhamFP pairSnd_mem_FP
  have hu : Cobham fun v : Fin 1 → List Bool ↦ verdictRuler (Fintype.card tm.Q) (v 0) :=
    Cobham.appendFn (Cobham.proj 0) (Cobham.const _)
  show Cobham fun v : Fin 1 → List Bool ↦ ptmVerdict tm (v 0)
  exact (Cobham.acceptChoiceFn_mem tm hu hx hc).of_eq fun _ ↦ rfl

/-- The verdict is the path's verdict. -/
theorem ptmVerdict_eq_true_iff {k : ℕ} (tm : NTM k) (x c : List Bool) :
    ptmVerdict tm (pair x c) = [true] ↔ Cobham.PathAccepts tm x c := by
  rw [ptmVerdict, pairFst_pair, pairSnd_pair]
  apply Cobham.acceptChoiceFn_eq_true_iff
  rw [verdictRuler, List.length_append, List.length_replicate, pair_length]
  omega

/-- Traces along choice sequences that agree up to a length cast are equal. -/
private theorem trace_congr {k : ℕ} (tm : NTM k) {n m : ℕ} (h : n = m) (choices : Fin n → Bool)
    (choices' : Fin m → Bool) (hc : ∀ j : Fin n, choices j = choices' (Fin.cast h j))
    (c : Cfg k tm.Q) : tm.trace n choices c = tm.trace m choices' c := by
  subst h
  congr
  funext j
  exact hc j

set_option linter.unusedVariables false in
/-- Along a seed at least as long as the halting bound, path acceptance is acceptance of the
`T`-step trace. (The hypotheses `hhalt` and `hm` are part of the interface: the statement is stated
over `m` directly, so the identification is purely definitional and does not use them.) -/
theorem pathAccepts_ofFn_iff {k : ℕ} (tm : NTM k) {T : ℕ → ℕ} (hhalt : tm.AllPathsHaltIn T)
    (x : List Bool) {m : ℕ} (hm : T x.length ≤ m) (r : Fin m → Bool) :
    Cobham.PathAccepts tm x (List.ofFn r) ↔
      (tm.trace m r (tm.initCfg x)).state = tm.qhalt ∧
        (tm.trace m r (tm.initCfg x)).output.cells 1 = Γ.one := by
  have htr : tm.trace (List.ofFn r).length (fun j ↦ (List.ofFn r)[j.val]'j.isLt) (tm.initCfg x)
      = tm.trace m r (tm.initCfg x) :=
    trace_congr tm List.length_ofFn _ r (fun j ↦ by simp [List.getElem_ofFn, Fin.cast]) _
  rw [Cobham.PathAccepts, htr]

/-- The probability that the verdict accepts, over seeds of length `m ≥ T(|x|)`, is the machine's
acceptance probability. -/
theorem eventProb_ptmVerdict {k : ℕ} (tm : NTM k) {T : ℕ → ℕ} (hhalt : tm.AllPathsHaltIn T)
    (x : List Bool) {m : ℕ} (hm : T x.length ≤ m) :
    eventProb (Finset.univ.filter fun r : Fin m → Bool ↦ ptmVerdict tm (pair x (List.ofFn r)) = [true])
      = tm.acceptProb x (T x.length) := by
  rw [← NTM.acceptProb_eq_of_le_of_allChoicesHalt tm x hm (hhalt x), NTM.acceptProb_eq_eventProb]
  congr 1
  exact Finset.filter_congr fun r _ ↦ by
    rw [ptmVerdict_eq_true_iff, pathAccepts_ofFn_iff tm hhalt x hm]

/-- **PTM ⇒ random tape.** A promise-BPP solver yields a random-tape solver. -/
theorem promiseRandomTapeBPP_of_promiseBPP {Q : PromiseProblem} (h : PromiseBPP Q) :
    PromiseRandomTapeBPP Q := by
  obtain ⟨k, tm, T, d, hhalt, hT, hyes, hno⟩ := h
  obtain ⟨ℓ, hℓ⟩ := BigO.pow_polynomial_bound hT
  refine ⟨ptmVerdict tm, ℓ, ptmVerdict_mem_FP tm, fun x hx ↦ ?_⟩
  have hm : T x.length ≤ ℓ.eval x.length := hℓ x.length
  rcases (PromiseProblem.mem_promise_iff Q x).mp hx with hy | hn
  · -- yes-instance: the good seeds are exactly the accepting seeds
    have hE : goodVerdictSeeds Q (ptmVerdict tm) x (ℓ.eval x.length) =
        Finset.univ.filter fun r : Fin (ℓ.eval x.length) → Bool ↦
          ptmVerdict tm (pair x (List.ofFn r)) = [true] := by
      classical
      unfold goodVerdictSeeds
      exact Finset.filter_congr fun r _ ↦ by simp [hy]
    rw [hE, eventProb_ptmVerdict tm hhalt x hm]
    exact hyes x hy
  · -- no-instance: the good seeds are exactly the rejecting seeds
    have hny : x ∉ Q.yesInstances := Q.not_mem_yes_of_mem_no hn
    have hE : goodVerdictSeeds Q (ptmVerdict tm) x (ℓ.eval x.length) =
        (Finset.univ.filter fun r : Fin (ℓ.eval x.length) → Bool ↦
          ptmVerdict tm (pair x (List.ofFn r)) = [true])ᶜ := by
      classical
      rw [Finset.compl_filter]
      unfold goodVerdictSeeds
      exact Finset.filter_congr fun r _ ↦ by simp [hny]
    rw [hE, eventProb_compl, eventProb_ptmVerdict tm hhalt x hm]
    have := hno x hn
    linarith

/-- Every `BPP` language has a random-tape decider. -/
theorem promiseRandomTapeBPP_ofLanguage_of_mem_BPP {L : Language} (h : L ∈ BPP) :
    PromiseRandomTapeBPP (PromiseProblem.ofLanguage L) :=
  promiseRandomTapeBPP_of_promiseBPP (promiseBPP_ofLanguage_of_mem_BPP h)

/-- **Random tape ⇒ PTM.** A polynomial-time verdict function `V` that decides `L` with error at most
`1/3` over uniform seeds of polynomial length `ℓ(|x|)` is realized by a polynomial-time probabilistic
Turing machine, so `L ∈ BPP`. -/
theorem mem_BPP_of_randomTape {L : Language} {V : List Bool → List Bool} {ℓ : Polynomial ℕ}
    (hV : V ∈ FP) (h : RandomTapeSolves (PromiseProblem.ofLanguage L) V ℓ) : L ∈ BPP :=
  mem_BPP_of_randomTape_machine hV h

end SparseDiv
