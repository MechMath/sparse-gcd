import Complexitylib.Classes.P.Cobham.Internal
import Complexitylib.Classes.PH.SipserLautemann.Verdict
import SparseDivComplexity.Randomized.Defs
import SparseDivComplexity.Randomized.Majority
import SparseDivComplexity.Randomized.RandomTape

/-!
# Composing BPP reductions with BPP solvers

Everything here is explicit error accounting over independent random blocks; no machine is built.

Given a random-tape reduction `f` from `L` to `Q` (error `≤ 1/3`) and a random-tape solver `V` of
`Q` (error `≤ 1/3`), the naive composition `V (pair (f (pair x r)) s)` errs with probability up to
`2/3`. We therefore

1. **amplify the solver** to error `≤ 1/16` by a majority vote over `49 = 12·4 + 1` independent seed
   blocks (`amplifyVerdict`, complexitylib's `eventProb_blockMajority_*_two_pow`);
2. run the pipeline on one fresh `(r, s)` pair: it is correct unless `r` is bad *or* `s` is bad, so
   by the union bound with probability at least `1 - 1/3 - 1/16 = 29/48 ≥ 3/5`;
3. take the **majority of eleven independent trials**, which brings the success probability back to
   `≥ 2/3` (`Randomized/Majority.lean`).

The seed of the composed verdict is the concatenation of the eleven trial blocks, each consisting of
the reduction seed followed by the amplified solver seed; the solver seed length is fixed from a
polynomial bound on `|f (pair x r)|` (`FP` functions have polynomially bounded outputs), and the
solver only reads the prefix it needs, so uniformity of the sub-seeds is a constant-fibers argument
(`eventProb_filter_of_constant_fibers`).

## Main results

* `amplifyVerdict_mem_FP`, `eventProb_amplifyVerdict_ge`, `eventProb_amplifyVerdict_le`.
* `promiseRandomTapeBPP_amplified` — a random-tape solver with error `≤ 1/16`.
* `promiseRandomTapeBPP_ofLanguage_of_mapReducesBPP` — **closure**: the source of a BPP reduction
  to a random-tape-solvable promise problem is random-tape solvable.
* `mem_BPP_of_mapReducesBPP` — with the machine bridge of `RandomTape.lean`: the source is in `BPP`.
-/

open Complexity

namespace SparseDiv

/-- The verdicts of `V` on `x` with the `reps` consecutive width-`w` blocks of the seed `S`. -/
def blockVerdicts (V : List Bool → List Bool) (x w : List Bool) (reps : ℕ) (S : List Bool) :
    List (List Bool) :=
  (List.range reps).map fun i ↦ V (pair x (blockAt w S i))

/-- Majority (as a flag) of the block verdicts. -/
def majorityOfBlocks (V : List Bool → List Bool) (x w : List Bool) (reps : ℕ) (S : List Bool) :
    List Bool :=
  [decide (reps < 2 * ((blockVerdicts V x w reps S).filter fun b ↦ b = [true]).length)]

/-- **The amplified verdict**: on `pair x S`, the majority of `reps` runs of `V` on `x` with the
`reps` consecutive seed blocks of width `ℓ(|x|)`. -/
noncomputable def amplifyVerdict (V : List Bool → List Bool) (ℓ : Polynomial ℕ) (reps : ℕ)
    (z : List Bool) : List Bool :=
  majorityOfBlocks V (pairFst z) (Cobham.polyLen ℓ (pairFst z)) reps (pairSnd z)

/-! ### The amplified verdict in Cobham's algebra

The majority over a *fixed* number `reps` of blocks is a finite composition: a unary tally string
collects one bit per accepting block (`tally`), and the majority test compares the doubled tally
against a constant ruler of length `reps + 1` (`Cobham.lenLeFlag`). -/

/-- The list count of `[true]` values over `List.range reps` is a sum of indicators. -/
private theorem length_filter_range_eq_sum (g : ℕ → List Bool) (reps : ℕ) :
    (((List.range reps).map g).filter fun b ↦ b = [true]).length =
      ∑ i ∈ Finset.range reps, if g i = [true] then 1 else 0 := by
  induction reps with
  | zero => simp
  | succ n ih =>
    rw [List.range_succ, List.map_append, List.filter_append, List.length_append, ih,
      Finset.sum_range_succ]
    congr 1
    by_cases h : g n = [true] <;> simp [h]

/-- The list count of `[true]` verdicts is the `Finset` count of good block indices. -/
private theorem length_filter_range_eq_card (g : ℕ → List Bool) (reps : ℕ) :
    (((List.range reps).map g).filter fun b ↦ b = [true]).length =
      (Finset.univ.filter fun i : Fin reps ↦ g i.val = [true]).card := by
  rw [length_filter_range_eq_sum, Finset.card_filter,
    Fin.sum_univ_eq_sum_range (fun j ↦ if g j = [true] then 1 else 0) reps]

/-- The unary tally of the `[true]` verdicts among the first `i` blocks: one bit per accepting
block. -/
private def tally (V : List Bool → List Bool) (x w S : List Bool) : ℕ → List Bool
  | 0 => []
  | i + 1 =>
    tally V x w S i ++ caseBit₀ (Cobham.eqFlag (V (pair x (blockAt w S i))) [true]) [true] []

/-- The tally has as many bits as there are accepting blocks. -/
private theorem tally_length (V : List Bool → List Bool) (x w S : List Bool) (i : ℕ) :
    (tally V x w S i).length = ((blockVerdicts V x w i S).filter fun b ↦ b = [true]).length := by
  induction i with
  | zero => simp [tally, blockVerdicts]
  | succ n ih =>
    rw [tally, List.length_append, ih, blockVerdicts, blockVerdicts, List.range_succ,
      List.map_append, List.filter_append, List.length_append]
    congr 1
    by_cases h : V (pair x (blockAt w S n)) = [true]
    · have hf : Cobham.eqFlag (V (pair x (blockAt w S n))) [true] = [true] :=
        (Cobham.eqFlag_eq_true_iff _ _).mpr h
      rw [hf]
      simp [h]
    · have hf : Cobham.eqFlag (V (pair x (blockAt w S n))) [true] = [false] := by
        rcases Cobham.eqFlag_flag (V (pair x (blockAt w S n))) [true] with hf | hf
        · exact absurd ((Cobham.eqFlag_eq_true_iff _ _).mp hf) h
        · exact hf
      rw [hf]
      simp [h]

/-- The majority flag is a length comparison of the doubled tally against a constant ruler. -/
private theorem majorityOfBlocks_eq_lenLeFlag (V : List Bool → List Bool) (x w : List Bool)
    (reps : ℕ) (S : List Bool) :
    majorityOfBlocks V x w reps S =
      Cobham.lenLeFlag (tally V x w S reps ++ tally V x w S reps)
        (List.replicate (reps + 1) false) := by
  have hlen : (List.replicate (reps + 1) false).length ≤
      (tally V x w S reps ++ tally V x w S reps).length ↔
      reps < 2 * ((blockVerdicts V x w reps S).filter fun b ↦ b = [true]).length := by
    rw [List.length_replicate, List.length_append, tally_length]
    omega
  rw [majorityOfBlocks]
  rcases Cobham.lenLeFlag_flag (tally V x w S reps ++ tally V x w S reps)
      (List.replicate (reps + 1) false) with hf | hf
  · rw [hf, decide_eq_true (hlen.mp ((Cobham.lenLeFlag_eq_true_iff _ _).mp hf))]
  · rw [hf, decide_eq_false]
    intro h
    have := (Cobham.lenLeFlag_eq_true_iff _ _).mpr (hlen.mpr h)
    rw [hf] at this
    simp at this

/-- The tally of the amplified verdict is in Cobham's algebra (a finite composition, by induction
on the fixed number of blocks). -/
private theorem tally_cobham {V : List Bool → List Bool} (hV : V ∈ FP) (ℓ : Polynomial ℕ)
    (i : ℕ) :
    Cobham fun v : Fin 1 → List Bool ↦
      tally V (pairFst (v 0)) (Cobham.polyLen ℓ (pairFst (v 0))) (pairSnd (v 0)) i := by
  have hx : Cobham fun v : Fin 1 → List Bool ↦ pairFst (v 0) := FP_subset_CobhamFP pairFst_mem_FP
  have hS : Cobham fun v : Fin 1 → List Bool ↦ pairSnd (v 0) := FP_subset_CobhamFP pairSnd_mem_FP
  induction i with
  | zero => exact Cobham.empty
  | succ n ih =>
    have hblock : Cobham fun v : Fin 1 → List Bool ↦
        V (pair (pairFst (v 0)) (blockAt (Cobham.polyLen ℓ (pairFst (v 0))) (pairSnd (v 0)) n)) :=
      (Cobham.comp (FP_subset_CobhamFP hV) fun _ : Fin 1 ↦
        Cobham.comp₂ Cobham.pairing hx (Cobham.blockFn (Cobham.polyLen_mem ℓ hx) hS n)).of_eq
        fun v ↦ by simp
    exact (Cobham.appendFn ih (Cobham.iteFn (Cobham.eqFlag_mem hblock (Cobham.const [true]))
      (Cobham.const [true]) (Cobham.const []))).of_eq fun v ↦ rfl

/-- The amplified verdict of a polynomial-time verdict is polynomial-time. -/
theorem amplifyVerdict_mem_FP {V : List Bool → List Bool} (hV : V ∈ FP) (ℓ : Polynomial ℕ)
    (reps : ℕ) : amplifyVerdict V ℓ reps ∈ FP := by
  apply CobhamFP_subset_FP
  show Cobham fun v : Fin 1 → List Bool ↦ amplifyVerdict V ℓ reps (v 0)
  have ht := tally_cobham hV ℓ reps
  exact (Cobham.lenLeFlag_mem (Cobham.appendFn ht ht) (Cobham.const _)).of_eq fun v ↦
    (majorityOfBlocks_eq_lenLeFlag V _ _ reps _).symm

open scoped Classical in
/-- The single-trial accepting event of a verdict on `x` with seeds of length `w`. -/
noncomputable def verdictEvent (V : List Bool → List Bool) (x : List Bool) (w : ℕ) :
    Finset (Fin w → Bool) :=
  Finset.univ.filter fun r ↦ V (pair x (List.ofFn r)) = [true]

/-- The `i`-th width-`T` block of the string `List.ofFn S` is `List.ofFn` of the `i`-th block of
the seed function `S` (`blocksEquiv`). -/
private theorem ofFn_blocksEquiv {reps T : ℕ} (S : Fin (reps * T) → Bool) (i : Fin reps)
    {r : List Bool} (hr : r.length = T) :
    List.ofFn (blocksEquiv reps T S i) = blockAt r (List.ofFn S) i := by
  have hle : (i.val + 1) * T ≤ reps * T := Nat.mul_le_mul_right T i.isLt
  rw [Nat.succ_mul] at hle
  apply List.ext_getElem
  · simp only [List.length_ofFn, blockAt, List.length_take, List.length_drop, hr]
    omega
  · intro n h1 h2
    simp only [blockAt, List.getElem_ofFn, List.getElem_take, List.getElem_drop,
      blocksEquiv_apply, hr]
    congr 1
    ext
    simp only [finProdFinEquiv_apply_val]
    ring

/-- **The amplified verdict is the block majority** of the single-trial event. -/
theorem amplifyVerdict_eq_true_iff (V : List Bool → List Bool) (ℓ : Polynomial ℕ) (reps : ℕ)
    (x : List Bool) (S : Fin (reps * ℓ.eval x.length) → Bool) :
    amplifyVerdict V ℓ reps (pair x (List.ofFn S)) = [true] ↔
      blockMajority (verdictEvent V x (ℓ.eval x.length)) S = true := by
  simp only [amplifyVerdict, pairFst_pair, pairSnd_pair, majorityOfBlocks, blockVerdicts,
    List.cons.injEq, and_true, decide_eq_true_eq]
  rw [blockMajority, blockEventCount, decide_eq_true_eq, length_filter_range_eq_card]
  have hcard : (Finset.univ.filter fun i : Fin reps ↦
      V (pair x (blockAt (Cobham.polyLen ℓ x) (List.ofFn S) i.val)) = [true]) =
      Finset.univ.filter fun i : Fin reps ↦
        blocksEquiv reps (ℓ.eval x.length) S i ∈ verdictEvent V x (ℓ.eval x.length) := by
    refine Finset.filter_congr fun i _ ↦ ?_
    simp only [verdictEvent, Finset.mem_filter, Finset.mem_univ, true_and]
    rw [ofFn_blocksEquiv S i (Cobham.polyLen_length ℓ x)]
  rw [hcard]

/-- The accepting event of the amplified verdict is the block majority of the single-trial event. -/
private theorem filter_amplifyVerdict_eq (V : List Bool → List Bool) (ℓ : Polynomial ℕ)
    (reps : ℕ) (x : List Bool) :
    (Finset.univ.filter fun S : Fin (reps * ℓ.eval x.length) → Bool ↦
        amplifyVerdict V ℓ reps (pair x (List.ofFn S)) = [true]) =
      Finset.univ.filter fun S ↦ blockMajority (verdictEvent V x (ℓ.eval x.length)) S = true :=
  Finset.filter_congr fun S _ ↦ amplifyVerdict_eq_true_iff V ℓ reps x S

/-- Amplified yes-side: single-trial probability `≥ 2/3` becomes `≥ 1 - 2⁻ᵏ` after `12k + 1` blocks. -/
theorem eventProb_amplifyVerdict_ge (V : List Bool → List Bool) (ℓ : Polynomial ℕ) (k : ℕ)
    (x : List Bool) (h : 2 / 3 ≤ eventProb (verdictEvent V x (ℓ.eval x.length))) :
    1 - 1 / (2 : ℚ) ^ k ≤
      eventProb (Finset.univ.filter fun S : Fin ((12 * k + 1) * ℓ.eval x.length) → Bool ↦
        amplifyVerdict V ℓ (12 * k + 1) (pair x (List.ofFn S)) = [true]) := by
  rw [filter_amplifyVerdict_eq]
  exact eventProb_blockMajority_true_ge_one_sub_two_pow _ k _ h

/-- Amplified no-side: single-trial probability `≤ 1/3` becomes `≤ 2⁻ᵏ`. -/
theorem eventProb_amplifyVerdict_le (V : List Bool → List Bool) (ℓ : Polynomial ℕ) (k : ℕ)
    (x : List Bool) (h : eventProb (verdictEvent V x (ℓ.eval x.length)) ≤ 1 / 3) :
    eventProb (Finset.univ.filter fun S : Fin ((12 * k + 1) * ℓ.eval x.length) → Bool ↦
        amplifyVerdict V ℓ (12 * k + 1) (pair x (List.ofFn S)) = [true]) ≤ 1 / (2 : ℚ) ^ k := by
  rw [filter_amplifyVerdict_eq]
  exact eventProb_blockMajority_true_le_two_pow _ k _ h

/-! ### Good seeds versus accepting seeds -/

/-- On a yes-instance, the good seeds are the accepting seeds. -/
private theorem goodVerdictSeeds_eq_verdictEvent {Q : PromiseProblem} {V : List Bool → List Bool}
    {x : List Bool} (hx : x ∈ Q.yesInstances) (m : ℕ) :
    goodVerdictSeeds Q V x m = verdictEvent V x m := by
  ext r
  simp [goodVerdictSeeds, verdictEvent, hx]

/-- Off the yes-side, the good seeds are the rejecting seeds. -/
private theorem goodVerdictSeeds_eq_compl_verdictEvent {Q : PromiseProblem}
    {V : List Bool → List Bool} {x : List Bool} (hx : x ∉ Q.yesInstances) (m : ℕ) :
    goodVerdictSeeds Q V x m = (verdictEvent V x m)ᶜ := by
  ext r
  simp [goodVerdictSeeds, verdictEvent, hx]

/-- The accepting event of the amplified verdict, in `verdictEvent` form. -/
private theorem verdictEvent_amplifyVerdict (V : List Bool → List Bool) (ℓ : Polynomial ℕ)
    (reps : ℕ) (x : List Bool) :
    verdictEvent (amplifyVerdict V ℓ reps) x (reps * ℓ.eval x.length) =
      Finset.univ.filter fun S ↦ blockMajority (verdictEvent V x (ℓ.eval x.length)) S = true := by
  rw [← filter_amplifyVerdict_eq]
  ext S
  simp [verdictEvent]

/-- Amplified verdicts read only the first `reps · ℓ(|x|)` seed bits: every block they inspect lies
within that prefix. -/
private theorem amplifyVerdict_take (V : List Bool → List Bool) (ℓ : Polynomial ℕ) (reps : ℕ)
    (x r : List Bool) :
    amplifyVerdict V ℓ reps (pair x r) =
      amplifyVerdict V ℓ reps (pair x (r.take ((Polynomial.C reps * ℓ).eval x.length))) := by
  simp only [amplifyVerdict, pairFst_pair, pairSnd_pair, majorityOfBlocks, blockVerdicts,
    Polynomial.eval_mul, Polynomial.eval_C]
  have hmap : ((List.range reps).map fun i ↦ V (pair x (blockAt (Cobham.polyLen ℓ x) r i))) =
      (List.range reps).map fun i ↦
        V (pair x (blockAt (Cobham.polyLen ℓ x) (r.take (reps * ℓ.eval x.length)) i)) := by
    refine List.map_congr_left fun i hi ↦ ?_
    rw [List.mem_range] at hi
    have hle : (i + 1) * ℓ.eval x.length ≤ reps * ℓ.eval x.length :=
      Nat.mul_le_mul_right _ hi
    rw [Nat.succ_mul] at hle
    rw [blockAt, blockAt, Cobham.polyLen_length, List.drop_take, List.take_take,
      Nat.min_eq_left (by omega)]
  rw [hmap]

/-- **Amplification with the prefix property**: the amplified verdict has error `≤ 1/16` on the
promise and reads only its designed seed prefix. -/
private theorem exists_amplified {Q : PromiseProblem} (h : PromiseRandomTapeBPP Q) :
    ∃ (V : List Bool → List Bool) (ℓ : Polynomial ℕ), V ∈ FP ∧
      (∀ x r, V (pair x r) = V (pair x (r.take (ℓ.eval x.length)))) ∧
      ∀ x ∈ Q.promise, 15 / 16 ≤ eventProb (goodVerdictSeeds Q V x (ℓ.eval x.length)) := by
  obtain ⟨V, ℓ, hV, hsolve⟩ := h
  refine ⟨amplifyVerdict V ℓ (12 * 4 + 1), Polynomial.C (12 * 4 + 1) * ℓ,
    amplifyVerdict_mem_FP hV ℓ _, amplifyVerdict_take V ℓ _, fun x hx ↦ ?_⟩
  have hm : (Polynomial.C (12 * 4 + 1) * ℓ).eval x.length = (12 * 4 + 1) * ℓ.eval x.length := by
    rw [Polynomial.eval_mul, Polynomial.eval_C]
  rw [hm]
  have hgood := hsolve x hx
  rcases (PromiseProblem.mem_promise_iff Q x).mp hx with hy | hn
  · rw [goodVerdictSeeds_eq_verdictEvent hy] at hgood ⊢
    rw [verdictEvent_amplifyVerdict]
    have := eventProb_blockMajority_true_ge_one_sub_two_pow _ 4 _ hgood
    norm_num at this ⊢
    exact this
  · have hny : x ∉ Q.yesInstances := Q.not_mem_yes_of_mem_no hn
    rw [goodVerdictSeeds_eq_compl_verdictEvent hny, eventProb_compl] at hgood ⊢
    rw [verdictEvent_amplifyVerdict]
    have h13 : eventProb (verdictEvent V x (ℓ.eval x.length)) ≤ 1 / 3 := by linarith
    have := eventProb_blockMajority_true_le_two_pow _ 4 _ h13
    norm_num at this ⊢
    linarith

/-- **Amplification.** A random-tape solver can be assumed to have error at most `1/16`. -/
theorem promiseRandomTapeBPP_amplified {Q : PromiseProblem} (h : PromiseRandomTapeBPP Q) :
    ∃ (V : List Bool → List Bool) (ℓ : Polynomial ℕ), V ∈ FP ∧
      ∀ x ∈ Q.promise, 15 / 16 ≤ eventProb (goodVerdictSeeds Q V x (ℓ.eval x.length)) := by
  obtain ⟨V, ℓ, hV, -, hgood⟩ := exists_amplified h
  exact ⟨V, ℓ, hV, hgood⟩

/-- The output length of a polynomial-time function is polynomially bounded. -/
theorem exists_polynomial_length_bound_of_mem_FP {f : List Bool → List Bool} (hf : f ∈ FP) :
    ∃ q : Polynomial ℕ, ∀ x, (f x).length ≤ q.eval x.length :=
  Cobham.output_length_poly_of_mem_FP hf

/-- Restricting a uniformly random string of length `m ≥ k` to its first `k` bits is uniform: an
event depending only on that prefix has the probability of the prefix event. -/
private theorem eventProb_filter_take_mem {k m : ℕ} (hk : k ≤ m) (E : Finset (Fin k → Bool)) :
    eventProb (Finset.univ.filter fun w : Fin m → Bool ↦ Fin.take k hk w ∈ E) = eventProb E := by
  obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le hk
  have h := eventProb_block (fun s : Fin k → Bool ↦ s ∈ E) (fun _ : Fin j → Bool ↦ True)
  simp only [and_true, Finset.filter_true, eventProb_univ, mul_one, Finset.filter_mem_eq_inter,
    Finset.univ_inter] at h
  exact h

/-- A verdict only reads the seed prefix of the length it was designed for: padding the seed with
extra random bits does not change its success probability. -/
theorem eventProb_goodVerdictSeeds_of_le (Q : PromiseProblem) (V : List Bool → List Bool)
    (ℓ : Polynomial ℕ) (x : List Bool) {m : ℕ} (hm : ℓ.eval x.length ≤ m)
    (hV : ∀ r : List Bool, V (pair x r) = V (pair x (r.take (ℓ.eval x.length)))) :
    eventProb (goodVerdictSeeds Q V x m) = eventProb (goodVerdictSeeds Q V x (ℓ.eval x.length)) := by
  rw [← eventProb_filter_take_mem hm]
  congr 1
  ext r
  rw [Finset.mem_filter]
  simp only [goodVerdictSeeds, Finset.mem_filter, Finset.mem_univ, true_and]
  rw [Fin.ofFn_take_eq_take_ofFn, ← hV]

/-! ### The composed per-trial verdict -/

/-- The per-trial verdict of the composition: split the seed into the reduction seed (the first
`ℓ₁(|x|)` bits) and the solver seed (the rest), apply the reduction, then the solver. -/
private noncomputable def trialVerdict (f V : List Bool → List Bool) (ℓ₁ : Polynomial ℕ)
    (z : List Bool) : List Bool :=
  V (pair (f (pair (pairFst z) ((pairSnd z).take (Cobham.polyLen ℓ₁ (pairFst z)).length)))
    ((pairSnd z).drop (Cobham.polyLen ℓ₁ (pairFst z)).length))

/-- The per-trial verdict is polynomial-time. -/
private theorem trialVerdict_mem_FP {f V : List Bool → List Bool} (hf : f ∈ FP) (hV : V ∈ FP)
    (ℓ₁ : Polynomial ℕ) : trialVerdict f V ℓ₁ ∈ FP := by
  apply CobhamFP_subset_FP
  have hx : Cobham fun v : Fin 1 → List Bool ↦ pairFst (v 0) := FP_subset_CobhamFP pairFst_mem_FP
  have hs : Cobham fun v : Fin 1 → List Bool ↦ pairSnd (v 0) := FP_subset_CobhamFP pairSnd_mem_FP
  have hℓ := Cobham.polyLen_mem ℓ₁ hx
  have hy : Cobham fun v : Fin 1 → List Bool ↦
      f (pair (pairFst (v 0)) ((pairSnd (v 0)).take (Cobham.polyLen ℓ₁ (pairFst (v 0))).length)) :=
    (Cobham.comp (FP_subset_CobhamFP hf) fun _ : Fin 1 ↦
      Cobham.comp₂ Cobham.pairing hx (Cobham.takeFn hℓ hs)).of_eq fun v ↦ by simp
  show Cobham fun v : Fin 1 → List Bool ↦ trialVerdict f V ℓ₁ (v 0)
  exact (Cobham.comp (FP_subset_CobhamFP hV) fun _ : Fin 1 ↦
    Cobham.comp₂ Cobham.pairing hy (Cobham.dropFn hℓ hs)).of_eq fun v ↦ by simp [trialVerdict]

/-- A seed string splits as its prefix and suffix blocks. -/
private theorem ofFn_eq_ofFn_blockFst_append (a b : ℕ) (w : Fin (a + b) → Bool) :
    List.ofFn w = List.ofFn (blockFst a b w) ++ List.ofFn (blockSnd a b w) := by
  rw [List.ofFn_add]
  rfl

/-- The per-trial verdict on a split seed. -/
private theorem trialVerdict_pair_ofFn (f V : List Bool → List Bool) (ℓ₁ : Polynomial ℕ)
    (x : List Bool) {a b : ℕ} (ha : ℓ₁.eval x.length = a) (w : Fin (a + b) → Bool) :
    trialVerdict f V ℓ₁ (pair x (List.ofFn w)) =
      V (pair (f (pair x (List.ofFn (blockFst a b w)))) (List.ofFn (blockSnd a b w))) := by
  subst ha
  rw [trialVerdict, pairFst_pair, pairSnd_pair, Cobham.polyLen_length,
    ofFn_eq_ofFn_blockFst_append, List.take_left' List.length_ofFn,
    List.drop_left' List.length_ofFn]

/-! ### Conditioning on the prefix block -/

/-- An event depending only on the prefix block has the prefix event's probability. -/
private theorem eventProb_filter_blockFst {a b : ℕ} (P : (Fin a → Bool) → Prop)
    [DecidablePred P] :
    eventProb (Finset.univ.filter fun w : Fin (a + b) → Bool ↦ P (blockFst a b w)) =
      eventProb (Finset.univ.filter P) := by
  have h := eventProb_block P (fun _ : Fin b → Bool ↦ True)
  simp only [and_true, Finset.filter_true, eventProb_univ, mul_one] at h
  exact h

/-- Singletons partition an event: the sum of the point probabilities is the probability. -/
private theorem sum_eventProb_filter_eq {a : ℕ} (G : Finset (Fin a → Bool)) :
    ∑ u ∈ G, eventProb (Finset.univ.filter fun v : Fin a → Bool ↦ v = u) = eventProb G := by
  simp only [Finset.filter_eq', Finset.mem_univ, ite_true, eventProb, Finset.card_singleton,
    Nat.cast_one, Finset.sum_const, nsmul_eq_mul]
  ring

/-- **Conditioning on the prefix.** If for every prefix `u ∈ G` the suffix event `F u` has
probability at most `ε`, then the joint event `{u ∈ G, v ∈ F u}` has probability at most `ε`. -/
private theorem eventProb_filter_blockFst_mem_and_le {a b : ℕ} (G : Finset (Fin a → Bool))
    (F : (Fin a → Bool) → Finset (Fin b → Bool)) {ε : ℚ} (hε : 0 ≤ ε)
    (hF : ∀ u ∈ G, eventProb (F u) ≤ ε) :
    eventProb (Finset.univ.filter fun w : Fin (a + b) → Bool ↦
      blockFst a b w ∈ G ∧ blockSnd a b w ∈ F (blockFst a b w)) ≤ ε := by
  set E := Finset.univ.filter fun w : Fin (a + b) → Bool ↦
      blockFst a b w ∈ G ∧ blockSnd a b w ∈ F (blockFst a b w) with hE
  have hmaps : (E : Set (Fin (a + b) → Bool)).MapsTo (blockFst a b) G := by
    intro w hw
    simp only [hE, Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq] at hw
    exact hw.1
  rw [eventProb_eq_sum_fiberwise E G (blockFst a b) hmaps]
  have hfiber : ∀ u ∈ G, eventProb (E.filter fun w ↦ blockFst a b w = u) ≤
      eventProb (Finset.univ.filter fun v : Fin a → Bool ↦ v = u) * ε := by
    intro u hu
    have heq : (E.filter fun w ↦ blockFst a b w = u) =
        Finset.univ.filter fun w : Fin (a + b) → Bool ↦
          blockFst a b w = u ∧ blockSnd a b w ∈ F u := by
      ext w
      simp only [hE, Finset.mem_filter, Finset.mem_univ, true_and]
      constructor
      · rintro ⟨⟨-, h2⟩, rfl⟩
        exact ⟨rfl, h2⟩
      · rintro ⟨rfl, h2⟩
        exact ⟨⟨hu, h2⟩, rfl⟩
    rw [heq, eventProb_block (fun v : Fin a → Bool ↦ v = u) (fun v ↦ v ∈ F u),
      Finset.filter_mem_eq_inter, Finset.univ_inter]
    exact mul_le_mul_of_nonneg_left (hF u hu) (eventProb_nonneg _)
  calc ∑ u ∈ G, eventProb (E.filter fun w ↦ blockFst a b w = u)
      ≤ ∑ u ∈ G, eventProb (Finset.univ.filter fun v : Fin a → Bool ↦ v = u) * ε :=
        Finset.sum_le_sum hfiber
    _ = eventProb G * ε := by rw [← Finset.sum_mul, sum_eventProb_filter_eq]
    _ ≤ ε := mul_le_of_le_one_left hε (eventProb_le_one G)

/-! ### The per-trial error bound -/

/-- **One trial of the composition succeeds with probability at least `29/48`.** The reduction seed
is bad with probability `≤ 1/3`; given a good reduction seed, the (amplified) solver seed is bad
with probability `≤ 1/16`. Here `a = ℓ₁(|x|)` is the reduction seed length and `b` bounds the
solver seed length `ℓ₂(|f (pair x r)|)` over all reduction seeds `r`. -/
private theorem eventProb_trial_ge {L : Language} {Q : PromiseProblem} {f V : List Bool → List Bool}
    {ℓ₁ ℓ₂ : Polynomial ℕ} (x : List Bool) {a b : ℕ} (ha : ℓ₁.eval x.length = a)
    (hred : 2 / 3 ≤ eventProb (goodSeeds L Q f x a))
    (hVpre : ∀ y r, V (pair y r) = V (pair y (r.take (ℓ₂.eval y.length))))
    (hVgood : ∀ y ∈ Q.promise, 15 / 16 ≤ eventProb (goodVerdictSeeds Q V y (ℓ₂.eval y.length)))
    (hb : ∀ u : Fin a → Bool, ℓ₂.eval (f (pair x (List.ofFn u))).length ≤ b) :
    29 / 48 ≤ eventProb (goodVerdictSeeds (PromiseProblem.ofLanguage L) (trialVerdict f V ℓ₁) x
      (a + b)) := by
  classical
  set G := goodSeeds L Q f x a with hG
  set y : (Fin a → Bool) → List Bool := fun u ↦ f (pair x (List.ofFn u)) with hy
  set F : (Fin a → Bool) → Finset (Fin b → Bool) := fun u ↦ (goodVerdictSeeds Q V (y u) b)ᶜ
    with hF
  -- Membership in the good reduction seeds, unfolded.
  have hmemG : ∀ u ∈ G, (x ∈ L → y u ∈ Q.yesInstances) ∧ (x ∉ L → y u ∈ Q.noInstances) := by
    intro u hu
    have hmem : u ∈ goodSeeds L Q f x a := hu
    simpa only [goodSeeds, Finset.mem_filter, Finset.mem_univ, true_and] using hmem
  -- Given a good reduction seed, the solver seed is bad with probability `≤ 1/16`.
  have hF_le : ∀ u ∈ G, eventProb (F u) ≤ 1 / 16 := by
    intro u hu
    have hmem := hmemG u hu
    have hprom : y u ∈ Q.promise := by
      rw [PromiseProblem.mem_promise_iff]
      by_cases hx : x ∈ L
      · exact Or.inl (hmem.1 hx)
      · exact Or.inr (hmem.2 hx)
    have h1 := hVgood (y u) hprom
    rw [← eventProb_goodVerdictSeeds_of_le Q V ℓ₂ (y u) (hb u) (hVpre (y u))] at h1
    simp only [hF, eventProb_compl]
    linarith
  -- The failure event is covered by the two bad events.
  have hcover : (goodVerdictSeeds (PromiseProblem.ofLanguage L) (trialVerdict f V ℓ₁) x (a + b))ᶜ ⊆
      (Finset.univ.filter fun w : Fin (a + b) → Bool ↦ ¬ blockFst a b w ∈ G) ∪
        (Finset.univ.filter fun w : Fin (a + b) → Bool ↦
          blockFst a b w ∈ G ∧ blockSnd a b w ∈ F (blockFst a b w)) := by
    intro w hw
    rw [Finset.mem_compl, goodVerdictSeeds, Finset.mem_filter, trialVerdict_pair_ofFn f V ℓ₁ x ha]
      at hw
    rw [Finset.mem_union, Finset.mem_filter, Finset.mem_filter]
    simp only [Finset.mem_univ, true_and]
    by_cases hu : blockFst a b w ∈ G
    · refine Or.inr ⟨hu, ?_⟩
      simp only [hF, Finset.mem_compl, goodVerdictSeeds, Finset.mem_filter, Finset.mem_univ,
        true_and]
      intro hv
      apply hw
      refine ⟨Finset.mem_univ _, ?_⟩
      change V (pair (y (blockFst a b w)) (List.ofFn (blockSnd a b w))) = [true] ↔ x ∈ L
      rw [hv]
      have hmem := hmemG _ hu
      constructor
      · intro hyes
        by_contra hx
        exact Q.not_mem_yes_of_mem_no (hmem.2 hx) hyes
      · exact hmem.1
    · exact Or.inl hu
  have h1 : eventProb (Finset.univ.filter fun w : Fin (a + b) → Bool ↦ ¬ blockFst a b w ∈ G) ≤
      1 / 3 := by
    rw [eventProb_filter_blockFst (fun u ↦ ¬ u ∈ G), Finset.filter_not, Finset.filter_mem_eq_inter,
      Finset.univ_inter, ← Finset.compl_eq_univ_sdiff, eventProb_compl]
    linarith
  have h2 := eventProb_filter_blockFst_mem_and_le G F (by norm_num) hF_le
  have h3 := (eventProb_mono hcover).trans (eventProb_union_le _ _)
  rw [eventProb_compl] at h3
  linarith

/-! ### The eleven-trial majority -/

/-- **Eleven-trial majority.** A polynomial-time verdict correct with probability `≥ 3/5` on the
promise yields a random-tape solver (error `≤ 1/3`). -/
private theorem promiseRandomTapeBPP_of_three_fifths {Q : PromiseProblem}
    {W : List Bool → List Bool} {ℓ : Polynomial ℕ} (hW : W ∈ FP)
    (h : ∀ x ∈ Q.promise, 3 / 5 ≤ eventProb (goodVerdictSeeds Q W x (ℓ.eval x.length))) :
    PromiseRandomTapeBPP Q := by
  refine ⟨amplifyVerdict W ℓ 11, Polynomial.C 11 * ℓ, amplifyVerdict_mem_FP hW ℓ 11, ?_⟩
  intro x hx
  have hm : (Polynomial.C 11 * ℓ).eval x.length = 11 * ℓ.eval x.length := by
    rw [Polynomial.eval_mul, Polynomial.eval_C]
  rw [hm]
  have hgood := h x hx
  rcases (PromiseProblem.mem_promise_iff Q x).mp hx with hy | hn
  · rw [goodVerdictSeeds_eq_verdictEvent hy] at hgood ⊢
    rw [verdictEvent_amplifyVerdict]
    exact eventProb_blockMajority_true_ge_two_thirds _ _ hgood
  · have hny : x ∉ Q.yesInstances := Q.not_mem_yes_of_mem_no hn
    rw [goodVerdictSeeds_eq_compl_verdictEvent hny, eventProb_compl] at hgood ⊢
    rw [verdictEvent_amplifyVerdict]
    have h25 : eventProb (verdictEvent W x (ℓ.eval x.length)) ≤ 2 / 5 := by linarith
    have := eventProb_blockMajority_true_le_one_third _ _ h25
    linarith

/-- **Closure of random-tape solvability under BPP reductions.** -/
theorem promiseRandomTapeBPP_ofLanguage_of_mapReducesBPP {L : Language} {Q : PromiseProblem}
    (hred : MapReducesBPP L Q) (hQ : PromiseRandomTapeBPP Q) :
    PromiseRandomTapeBPP (PromiseProblem.ofLanguage L) := by
  obtain ⟨f, ℓ₁, hf, hred⟩ := hred
  obtain ⟨V, ℓ₂, hV, hVpre, hVgood⟩ := exists_amplified hQ
  obtain ⟨q, hq⟩ := exists_polynomial_length_bound_of_mem_FP hf
  -- The solver seed length: `ℓ₂` of the polynomial bound `q ∘ p` on `|f (pair x r)|`, where
  -- `p(|x|) = |pair x r| = 2|x| + 2 + ℓ₁(|x|)`.
  set p : Polynomial ℕ := Polynomial.C 2 * Polynomial.X + Polynomial.C 2 + ℓ₁ with hp
  set ℓ₃ : Polynomial ℕ := ℓ₂.comp (q.comp p) with hℓ₃
  refine promiseRandomTapeBPP_of_three_fifths (ℓ := ℓ₁ + ℓ₃) (trialVerdict_mem_FP hf hV ℓ₁)
    fun x _ ↦ ?_
  have hb : ∀ u : Fin (ℓ₁.eval x.length) → Bool,
      ℓ₂.eval (f (pair x (List.ofFn u))).length ≤ ℓ₃.eval x.length := by
    intro u
    have hlen : (pair x (List.ofFn u)).length = p.eval x.length := by
      rw [pair_length, List.length_ofFn, hp]
      simp [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_X]
    have h1 : (f (pair x (List.ofFn u))).length ≤ (q.comp p).eval x.length := by
      rw [Polynomial.eval_comp, ← hlen]
      exact hq _
    rw [hℓ₃, Polynomial.eval_comp]
    exact polynomial_eval_mono_nat ℓ₂ h1
  rw [Polynomial.eval_add]
  have := eventProb_trial_ge x rfl (hred x) hVpre hVgood hb
  linarith

/-- **BPP reductions to promise-BPP-solvable problems put the source in BPP.** Combines the random
tape closure with the machine bridges of `RandomTape.lean`. -/
theorem mem_BPP_of_mapReducesBPP {L : Language} {Q : PromiseProblem} (hred : MapReducesBPP L Q)
    (hQ : PromiseBPP Q) : L ∈ BPP := by
  obtain ⟨V, ℓ, hV, hsolve⟩ :=
    promiseRandomTapeBPP_ofLanguage_of_mapReducesBPP hred (promiseRandomTapeBPP_of_promiseBPP hQ)
  exact mem_BPP_of_randomTape hV hsolve

end SparseDiv
