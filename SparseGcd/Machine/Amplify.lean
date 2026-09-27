import SparseGcd.Machine.StageLemmas
import SparseGcd.Machine.ArithStr
import SparseDivComplexity.Randomized.RandomTape
import SparseDivComplexity.Randomized.Closure

/-!
# The amplified roots-of-unity decider (Theorem 19, oracle side)

From a promise-BPP solver of `rouPromise` (equivalently a random-tape verdict `V` with error
`≤ 1/3`, seed length `ℓ(|z|)`), the majority of `12c + 1` independent runs has error `≤ 2^{-c}`
(complexitylib's `eventProb_blockMajority_*_two_pow`). The count `c` is supplied in unary as part
of the input, so a single `FP` function serves every error target.

## Construction

The input is `pair cu (pair x r)`. A ruler of length `12|cu| + 1` (`majRuler`) clocks a Cobham
iteration (`Cobham.iterFn`) whose state is `pair tally rest`: each step consumes one block of
width `|polyLen ℓ x|` from `rest` and appends one bit to the unary `tally` when the verdict of
`V` on that block is `[true]` (`majStep`, `majLoop`). The majority is the length comparison of the
doubled tally against the ruler plus one bit (`Cobham.lenLeFlag`), exactly as the `SparseDivComplexity` support modules'
`majorityOfBlocks`.
-/

open Complexity SparseDiv SparseDiv.StringArith Polynomial

namespace SparseGcd

/-! ### The majority loop -/

/-- One step of the amplification loop on the state `pair tally rest`: consume a block of width
`|w|` from `rest` and append one bit to `tally` when the verdict is `[true]`. -/
def majStep (V : List Bool → List Bool) (x w s : List Bool) : List Bool :=
  pair (pairFst s ++
      caseBit₀ (Cobham.eqFlag (V (pair x ((pairSnd s).take w.length))) [true]) [true] [])
    ((pairSnd s).drop w.length)

/-- `k` steps of the loop from the state `pair [] r`. -/
def majLoop (V : List Bool → List Bool) (x w r : List Bool) (k : ℕ) : List Bool :=
  (majStep V x w)^[k] (pair [] r)

/-- The unary tally of the accepting blocks among the first `k` width-`|w|` blocks of `r`. -/
def majTally (V : List Bool → List Bool) (x w r : List Bool) : ℕ → List Bool
  | 0 => []
  | k + 1 =>
    majTally V x w r k ++ caseBit₀ (Cobham.eqFlag (V (pair x (blockAt w r k))) [true]) [true] []

/-- The ruler of length `12 |cu| + 1` clocking the loop. -/
def majRuler (cu : List Bool) : List Bool := (List.replicate 12 cu).flatten ++ [true]

theorem majRuler_length (cu : List Bool) : (majRuler cu).length = 12 * cu.length + 1 := by
  simp [majRuler]
  omega

/-- The loop state after `k` steps: the tally and the unread suffix. -/
theorem majLoop_eq (V : List Bool → List Bool) (x w r : List Bool) (k : ℕ) :
    majLoop V x w r k = pair (majTally V x w r k) (r.drop (k * w.length)) := by
  induction k with
  | zero => simp [majLoop, majTally]
  | succ k ih =>
    rw [majLoop, Function.iterate_succ_apply', ← majLoop, ih, majStep, pairFst_pair, pairSnd_pair,
      majTally, blockAt, List.drop_drop, Nat.succ_mul]

/-- The tally has at most one bit per step. -/
theorem majTally_length_le (V : List Bool → List Bool) (x w r : List Bool) (k : ℕ) :
    (majTally V x w r k).length ≤ k := by
  induction k with
  | zero => simp [majTally]
  | succ k ih =>
    rw [majTally, List.length_append]
    have := caseBit₀_length_le (Cobham.eqFlag (V (pair x (blockAt w r k))) [true]) [true] []
    simp only [List.length_append, List.length_singleton, List.length_nil] at this
    omega

/-- The tally counts the accepting blocks (as a sum of indicators). -/
private theorem majTally_length_sum (V : List Bool → List Bool) (x w r : List Bool) (k : ℕ) :
    (majTally V x w r k).length =
      ∑ i ∈ Finset.range k, if V (pair x (blockAt w r i)) = [true] then 1 else 0 := by
  induction k with
  | zero => simp [majTally]
  | succ k ih =>
    rw [majTally, List.length_append, ih, Finset.sum_range_succ]
    congr 1
    by_cases h : V (pair x (blockAt w r k)) = [true]
    · rw [(Cobham.eqFlag_eq_true_iff _ _).mpr h]
      simp [h]
    · have hf : Cobham.eqFlag (V (pair x (blockAt w r k))) [true] = [false] := by
        rcases Cobham.eqFlag_flag (V (pair x (blockAt w r k))) [true] with hf | hf
        · exact absurd ((Cobham.eqFlag_eq_true_iff _ _).mp hf) h
        · exact hf
      rw [hf]
      simp [h]

/-- The tally counts the accepting blocks (as a `Finset` card over block indices). -/
theorem majTally_length (V : List Bool → List Bool) (x w r : List Bool) (k : ℕ) :
    (majTally V x w r k).length =
      (Finset.univ.filter fun i : Fin k ↦ V (pair x (blockAt w r i.val)) = [true]).card := by
  rw [majTally_length_sum, Finset.card_filter,
    Fin.sum_univ_eq_sum_range (fun j ↦ if V (pair x (blockAt w r j)) = [true] then 1 else 0) k]

/-- The first `K` blocks lie within the first `K · |w|` bits. -/
theorem majTally_take (V : List Bool → List Bool) (x w r : List Bool) {k K : ℕ} (hk : k ≤ K) :
    majTally V x w (r.take (K * w.length)) k = majTally V x w r k := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [majTally, majTally, ih (by omega)]
    have hle : (k + 1) * w.length ≤ K * w.length := Nat.mul_le_mul_right _ hk
    rw [Nat.succ_mul] at hle
    rw [blockAt, blockAt, List.drop_take, List.take_take, Nat.min_eq_left (by omega)]

/-- Majority over `12|cu| + 1` blocks of width `|w|` of the verdict `V (pair z block)`;
input `pair cu (pair z r)`. -/
noncomputable def majStr (V : List Bool → List Bool) (ℓ : Polynomial ℕ) (z : List Bool) : List Bool :=
  Cobham.lenLeFlag
    (pairFst (majLoop V (pairFst (pairSnd z)) (Cobham.polyLen ℓ (pairFst (pairSnd z)))
        (pairSnd (pairSnd z)) (majRuler (pairFst z)).length) ++
      pairFst (majLoop V (pairFst (pairSnd z)) (Cobham.polyLen ℓ (pairFst (pairSnd z)))
        (pairSnd (pairSnd z)) (majRuler (pairFst z)).length))
    (majRuler (pairFst z) ++ [true])

theorem majStr_eq_true_iff (V : List Bool → List Bool) (ℓ : Polynomial ℕ) (c : ℕ) (x : List Bool)
    (S : BitString ((12 * c + 1) * ℓ.eval x.length)) :
    majStr V ℓ (pair (unaryN c) (pair x (List.ofFn S))) = [true] ↔
      blockMajority (SparseDiv.verdictEvent V x (ℓ.eval x.length)) S = true := by
  have hcu : (unaryN c).length = c := List.length_replicate
  rw [majStr, pairFst_pair, pairSnd_pair, pairFst_pair, pairSnd_pair, majRuler_length, hcu,
    majLoop_eq, pairFst_pair, Cobham.lenLeFlag_eq_true_iff, List.length_append,
    List.length_append, majRuler_length, hcu, List.length_singleton, majTally_length,
    blockMajority, decide_eq_true_eq, blockEventCount]
  have hcard : (Finset.univ.filter fun i : Fin (12 * c + 1) ↦
      V (pair x (blockAt (Cobham.polyLen ℓ x) (List.ofFn S) i.val)) = [true]) =
      Finset.univ.filter fun i : Fin (12 * c + 1) ↦
        blocksEquiv (12 * c + 1) (ℓ.eval x.length) S i ∈
          SparseDiv.verdictEvent V x (ℓ.eval x.length) := by
    refine Finset.filter_congr fun i _ ↦ ?_
    simp only [SparseDiv.verdictEvent, Finset.mem_filter, Finset.mem_univ, true_and]
    rw [ofFn_blocksEquiv, blockAt, Cobham.polyLen_length]
  rw [hcard]
  omega

theorem majStr_prefix (V : List Bool → List Bool) (ℓ : Polynomial ℕ) (c : ℕ) (x r : List Bool) :
    majStr V ℓ (pair (unaryN c) (pair x r)) =
      majStr V ℓ (pair (unaryN c) (pair x (r.take ((12 * c + 1) * ℓ.eval x.length)))) := by
  have hcu : (unaryN c).length = c := List.length_replicate
  simp only [majStr, pairFst_pair, pairSnd_pair, majLoop_eq, majRuler_length, hcu]
  rw [← Cobham.polyLen_length ℓ x, majTally_take V x _ r le_rfl]

theorem majStr_mem_FP {V : List Bool → List Bool} (hV : V ∈ FP) (ℓ : Polynomial ℕ) :
    majStr V ℓ ∈ FP := by
  apply CobhamFP_subset_FP
  show Cobham fun v : Fin 1 → List Bool ↦ majStr V ℓ (v 0)
  have hfst : Cobham fun v : Fin 1 → List Bool ↦ pairFst (v 0) :=
    FP_subset_CobhamFP pairFst_mem_FP
  have hsnd : Cobham fun v : Fin 1 → List Bool ↦ pairSnd (v 0) :=
    FP_subset_CobhamFP pairSnd_mem_FP
  -- two-argument versions (`v 0` is the loop state / clock, `v 1` the input)
  have hz : Cobham fun v : Fin 2 → List Bool ↦ pairSnd (v 1) :=
    (Cobham.comp hsnd fun _ : Fin 1 ↦ Cobham.proj 1).of_eq fun _ ↦ rfl
  have hx : Cobham fun v : Fin 2 → List Bool ↦ pairFst (pairSnd (v 1)) :=
    (Cobham.comp hfst fun _ : Fin 1 ↦ hz).of_eq fun _ ↦ rfl
  have hr : Cobham fun v : Fin 2 → List Bool ↦ pairSnd (pairSnd (v 1)) :=
    (Cobham.comp hsnd fun _ : Fin 1 ↦ hz).of_eq fun _ ↦ rfl
  have hw : Cobham fun v : Fin 2 → List Bool ↦ Cobham.polyLen ℓ (pairFst (pairSnd (v 1))) :=
    Cobham.polyLen_mem ℓ hx
  have hs1 : Cobham fun v : Fin 2 → List Bool ↦ pairFst (v 0) :=
    (Cobham.comp hfst fun _ : Fin 1 ↦ Cobham.proj 0).of_eq fun _ ↦ rfl
  have hs2 : Cobham fun v : Fin 2 → List Bool ↦ pairSnd (v 0) :=
    (Cobham.comp hsnd fun _ : Fin 1 ↦ Cobham.proj 0).of_eq fun _ ↦ rfl
  have hverdict : Cobham fun v : Fin 2 → List Bool ↦
      V (pair (pairFst (pairSnd (v 1)))
        ((pairSnd (v 0)).take (Cobham.polyLen ℓ (pairFst (pairSnd (v 1)))).length)) :=
    (Cobham.comp (FP_subset_CobhamFP hV) fun _ : Fin 1 ↦
      Cobham.comp₂ Cobham.pairing hx (Cobham.takeFn hw hs2)).of_eq fun v ↦ by simp
  have hstep : Cobham fun v : Fin 2 → List Bool ↦
      majStep V (pairFst (pairSnd (v 1))) (Cobham.polyLen ℓ (pairFst (pairSnd (v 1)))) (v 0) :=
    (Cobham.comp₂ Cobham.pairing
      (Cobham.appendFn hs1 (Cobham.iteFn (Cobham.eqFlag_mem hverdict (Cobham.const [true]))
        (Cobham.const [true]) (Cobham.const [])))
      (Cobham.dropFn hw hs2)).of_eq fun v ↦ by simp [majStep]
  have hinit : Cobham fun v : Fin 1 → List Bool ↦ pair [] (pairSnd (pairSnd (v 0))) :=
    (Cobham.comp₂ Cobham.pairing Cobham.empty
      ((Cobham.comp hsnd fun _ : Fin 1 ↦ hsnd).of_eq fun _ ↦ rfl)).of_eq fun v ↦ by simp
  have hbnd : Cobham fun v : Fin 2 → List Bool ↦
      v 0 ++ v 0 ++ pairSnd (pairSnd (v 1)) ++ [false, false] :=
    Cobham.appendFn (Cobham.appendFn (Cobham.appendFn (Cobham.proj 0) (Cobham.proj 0)) hr)
      (Cobham.const _)
  have hloop : Cobham fun v : Fin 2 → List Bool ↦
      majLoop V (pairFst (pairSnd (v 1))) (Cobham.polyLen ℓ (pairFst (pairSnd (v 1))))
        (pairSnd (pairSnd (v 1))) (v 0).length := by
    refine (Cobham.iterFn hinit hstep hbnd ?_).of_eq fun v ↦ rfl
    intro c v
    show (majLoop V (pairFst (pairSnd (v 0))) (Cobham.polyLen ℓ (pairFst (pairSnd (v 0))))
      (pairSnd (pairSnd (v 0))) c.length).length ≤ _
    rw [majLoop_eq, pair_length]
    have h1 := majTally_length_le V (pairFst (pairSnd (v 0)))
      (Cobham.polyLen ℓ (pairFst (pairSnd (v 0)))) (pairSnd (pairSnd (v 0))) c.length
    simp only [List.length_append, List.length_cons, List.length_nil, List.length_drop,
      Fin.cons_zero, Fin.cons_one]
    omega
  have hR : Cobham fun v : Fin 1 → List Bool ↦ majRuler (pairFst (v 0)) :=
    Cobham.appendFn (Cobham.repeatFn hfst 12) (Cobham.const [true])
  have hloop1 : Cobham fun v : Fin 1 → List Bool ↦
      majLoop V (pairFst (pairSnd (v 0))) (Cobham.polyLen ℓ (pairFst (pairSnd (v 0))))
        (pairSnd (pairSnd (v 0))) (majRuler (pairFst (v 0))).length :=
    (Cobham.comp₂ hloop hR (Cobham.proj 0)).of_eq fun v ↦ by simp
  have ht : Cobham fun v : Fin 1 → List Bool ↦
      pairFst (majLoop V (pairFst (pairSnd (v 0))) (Cobham.polyLen ℓ (pairFst (pairSnd (v 0))))
        (pairSnd (pairSnd (v 0))) (majRuler (pairFst (v 0))).length) :=
    (Cobham.comp hfst fun _ : Fin 1 ↦ hloop1).of_eq fun _ ↦ rfl
  exact (Cobham.lenLeFlag_mem (Cobham.appendFn ht ht)
    (Cobham.appendFn hR (Cobham.const [true]))).of_eq fun _ ↦ rfl

/-! ### Instance rearrangement -/

/-- Instance rearrangement `(p, R, H) ↦ (p, H, E)` where `E` is the exponent of the second term
of `R`. -/
def rouInst (p : ℕ) (R H : Terms) : List Bool := encRouInstance p H ((R.getD 1 (0, 0)).2)

/-- String-level rearrangement: on `pair (encNat p) (pair (encTerms R) (encTerms H))`, output
`pair (encNat p) (pair (encTerms H) e)` where `e` is the exponent code of the second framed term
of `encTerms R` (and `[] = encNat 0` when there is none). -/
def rouInstStr (z : List Bool) : List Bool :=
  pair (pairFst z)
    (pair (pairSnd (pairSnd z)) (pairSnd (pairFst (pairSnd (pairFst (pairSnd z))))))

private theorem pairFst_nil : pairFst [] = [] := rfl

private theorem pairSnd_nil : pairSnd [] = [] := rfl

/-- The exponent code of the second term of a framed term list. -/
private theorem pairSnd_pairFst_pairSnd_encTerms (R : Terms) :
    pairSnd (pairFst (pairSnd (encTerms R))) = encNat ((R.getD 1 (0, 0)).2) := by
  match R with
  | [] => simp [pairFst_nil, pairSnd_nil, encNat, Nat.zero_bits]
  | [t] =>
    rw [encTerms_cons_eq_pair, pairSnd_pair, encTerms_nil, pairFst_nil, pairSnd_nil]
    simp [encNat, Nat.zero_bits]
  | t₁ :: t₂ :: R' =>
    rw [encTerms_cons_eq_pair, pairSnd_pair, encTerms_cons_eq_pair, pairFst_pair, encTerm,
      pairSnd_pair]
    rfl

theorem rouInstStr_eq (p : ℕ) (R H : Terms) : rouInstStr (encDivInstance p R H) = rouInst p R H := by
  rw [rouInstStr, rouInst, encDivInstance, encRouInstance, pairFst_pair, pairSnd_pair, pairFst_pair,
    pairSnd_pair, pairSnd_pairFst_pairSnd_encTerms]

theorem rouInstStr_mem_FP : rouInstStr ∈ FP := by
  apply CobhamFP_subset_FP
  show Cobham fun v : Fin 1 → List Bool ↦ rouInstStr (v 0)
  have hfst : Cobham fun v : Fin 1 → List Bool ↦ pairFst (v 0) :=
    FP_subset_CobhamFP pairFst_mem_FP
  have hsnd : Cobham fun v : Fin 1 → List Bool ↦ pairSnd (v 0) :=
    FP_subset_CobhamFP pairSnd_mem_FP
  have h1 : Cobham fun v : Fin 1 → List Bool ↦ pairSnd (pairSnd (v 0)) :=
    (Cobham.comp hsnd fun _ : Fin 1 ↦ hsnd).of_eq fun _ ↦ rfl
  have h2 : Cobham fun v : Fin 1 → List Bool ↦ pairFst (pairSnd (v 0)) :=
    (Cobham.comp hfst fun _ : Fin 1 ↦ hsnd).of_eq fun _ ↦ rfl
  have h3 : Cobham fun v : Fin 1 → List Bool ↦ pairSnd (pairFst (pairSnd (v 0))) :=
    (Cobham.comp hsnd fun _ : Fin 1 ↦ h2).of_eq fun _ ↦ rfl
  have h4 : Cobham fun v : Fin 1 → List Bool ↦ pairFst (pairSnd (pairFst (pairSnd (v 0)))) :=
    (Cobham.comp hfst fun _ : Fin 1 ↦ h3).of_eq fun _ ↦ rfl
  have h5 : Cobham fun v : Fin 1 → List Bool ↦
      pairSnd (pairFst (pairSnd (pairFst (pairSnd (v 0))))) :=
    (Cobham.comp hsnd fun _ : Fin 1 ↦ h4).of_eq fun _ ↦ rfl
  exact (Cobham.comp₂ Cobham.pairing hfst (Cobham.comp₂ Cobham.pairing h1 h5)).of_eq fun v ↦ by
    simp [rouInstStr]

/-- The exponent of the second term is no longer than the whole term-list code. -/
private theorem size_getD_le_length_encTerms (R : Terms) :
    Nat.size ((R.getD 1 (0, 0)).2) ≤ (encTerms R).length := by
  match R with
  | [] => simp
  | [_] => simp
  | t₁ :: t₂ :: R' =>
    simp only [List.getD_cons_succ, List.getD_cons_zero, length_encTerms, List.map_cons,
      List.sum_cons, length_encTerm]
    omega

/-- The seed-length polynomial `(12 X + 1) ℓ`. -/
noncomputable def σPoly (ℓ : Polynomial ℕ) : Polynomial ℕ := (12 * Polynomial.X + 1) * ℓ

theorem σPoly_eval_ge (ℓ : Polynomial ℕ) (c n : ℕ) : (12 * c + 1) * ℓ.eval n ≤ (σPoly ℓ).eval (c + n) := by
  simp only [σPoly, Polynomial.eval_mul, Polynomial.eval_add, Polynomial.eval_X, Polynomial.eval_one,
    Polynomial.eval_ofNat]
  exact Nat.mul_le_mul (by omega) (polynomial_eval_mono_nat ℓ (by omega : n ≤ c + n))

/-! ### Correctness of the oracle -/

/-- On a yes-instance, the good seeds are the accepting seeds. -/
private theorem goodVerdictSeeds_eq_verdictEvent {Q : PromiseProblem} {V : List Bool → List Bool}
    {x : List Bool} (hx : x ∈ Q.yesInstances) (m : ℕ) :
    goodVerdictSeeds Q V x m = SparseDiv.verdictEvent V x m := by
  ext r
  simp [goodVerdictSeeds, SparseDiv.verdictEvent, hx]

/-- Off the yes-side, the good seeds are the rejecting seeds. -/
private theorem goodVerdictSeeds_eq_compl_verdictEvent {Q : PromiseProblem}
    {V : List Bool → List Bool} {x : List Bool} (hx : x ∉ Q.yesInstances) (m : ℕ) :
    goodVerdictSeeds Q V x m = (SparseDiv.verdictEvent V x m)ᶜ := by
  ext r
  simp [goodVerdictSeeds, SparseDiv.verdictEvent, hx]

/-- The amplified verdict reads only its designed prefix, so its correctness event over a longer
seed has the probability of the event over the prefix. -/
private theorem eventProb_majStr_prefix (V : List Bool → List Bool) (ℓ : Polynomial ℕ) (c : ℕ)
    (x : List Bool) (N : ℕ) (hN : (12 * c + 1) * ℓ.eval x.length ≤ N) (P : Prop) [Decidable P] :
    eventProb (Finset.univ.filter fun r : BitString N ↦
        (majStr V ℓ (pair (unaryN c) (pair x (List.ofFn r))) = [true] ↔ P)) =
      eventProb (Finset.univ.filter fun S : BitString ((12 * c + 1) * ℓ.eval x.length) ↦
        (majStr V ℓ (pair (unaryN c) (pair x (List.ofFn S))) = [true] ↔ P)) := by
  obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le hN
  refine Eq.trans ?_ (eventProb_filter_blockFst (b := j) _)
  congr 1
  ext r
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  rw [ofFn_blockFst, ← majStr_prefix]

/-- **Correctness of the amplified decider** on the instances `(p, H, E)` of the reduction, for
any seed length at least `(12c + 1) · ℓ(|z|)`. -/
theorem majStr_correct {V : List Bool → List Bool} (ℓ : Polynomial ℕ)
    (hsolve : SparseDiv.RandomTapeSolves rouPromise V ℓ) (c : ℕ) (d : RootData) (H : Terms)
    (hH : Normalized d.p H) (N : ℕ)
    (hN : (12 * c + 1) * ℓ.eval (encRouInstance d.p H d.E).length ≤ N) :
    1 - 1 / (2 : ℚ) ^ c ≤ eventProb (Finset.univ.filter fun r : BitString N ↦
      (majStr V ℓ (pair (unaryN c) (pair (encRouInstance d.p H d.E) (List.ofFn r))) = [true] ↔
        0 < (monicGcd d.R (toPoly d.p H)).natDegree)) := by
  rw [eventProb_majStr_prefix V ℓ c _ N hN]
  have hprom := hsolve _ (mem_rouPromise_promise d H hH)
  by_cases hyes : 0 < (monicGcd d.R (toPoly d.p H)).natDegree
  · have hmem : encRouInstance d.p H d.E ∈ rouPromise.yesInstances :=
      (mem_RootsOfUnity_iff d H hH).mpr hyes
    rw [goodVerdictSeeds_eq_verdictEvent hmem] at hprom
    refine le_trans (eventProb_blockMajority_true_ge_one_sub_two_pow _ c _ hprom) (le_of_eq ?_)
    congr 1
    exact Finset.filter_congr fun S _ ↦ by rw [majStr_eq_true_iff]; simp [hyes]
  · have hmem : encRouInstance d.p H d.E ∉ rouPromise.yesInstances :=
      fun h ↦ hyes ((mem_RootsOfUnity_iff d H hH).mp h)
    rw [goodVerdictSeeds_eq_compl_verdictEvent hmem, eventProb_compl] at hprom
    have h13 : eventProb (SparseDiv.verdictEvent V (encRouInstance d.p H d.E)
        (ℓ.eval (encRouInstance d.p H d.E).length)) ≤ 1 / 3 := by linarith
    have hle := eventProb_blockMajority_true_le_two_pow _ c _ h13
    have hset : (Finset.univ.filter fun S : BitString ((12 * c + 1) *
          ℓ.eval (encRouInstance d.p H d.E).length) ↦
        (majStr V ℓ (pair (unaryN c) (pair (encRouInstance d.p H d.E) (List.ofFn S))) = [true] ↔
          0 < (monicGcd d.R (toPoly d.p H)).natDegree)) =
        Finset.univ.filter fun S ↦ ¬ (blockMajority (SparseDiv.verdictEvent V
          (encRouInstance d.p H d.E) (ℓ.eval (encRouInstance d.p H d.E).length)) S = true) :=
      Finset.filter_congr fun S _ ↦ by rw [majStr_eq_true_iff]; simp [hyes]
    rw [hset, eventProb_filter_not]
    linarith

/-- **The degree oracle of Theorem 19** from a random-tape solver of `rouPromise`. -/
noncomputable def rouOracle (V : List Bool → List Bool) (ℓ : Polynomial ℕ) (hV : V ∈ FP)
    (hsolve : SparseDiv.RandomTapeSolves rouPromise V ℓ) : DegreeOracle where
  inst := rouInst
  instStr := rouInstStr
  O := majStr V ℓ
  σ := σPoly ℓ
  O_mem_FP := majStr_mem_FP hV ℓ
  instStr_mem_FP := rouInstStr_mem_FP
  instStr_eq := rouInstStr_eq
  inst_length_le := by
    intro p R H
    have h := size_getD_le_length_encTerms R
    simp only [rouInst, encRouInstance, encDivInstance, pair_length, length_encNat]
    omega
  O_prefix := by
    intro c z r
    rw [majStr_prefix V ℓ c z r, majStr_prefix V ℓ c z (r.take ((σPoly ℓ).eval (c + z.length))),
      List.take_take, Nat.min_eq_left (σPoly_eval_ge ℓ c z.length)]
  correct := by
    intro c d ψ us _ _ _ _
    exact majStr_correct ℓ hsolve c d _ (normalized_normalize d.hp.pos _) _
      (σPoly_eval_ge ℓ c _)

end SparseGcd
