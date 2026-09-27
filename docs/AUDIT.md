# AUDIT — SparseGcd (arXiv 2606.12144)

(Build result and `#print axioms` output are produced by `bash scripts/audit.sh` and written to `docs/AXIOMS.txt`;
this file explains what the main declarations say and what their hypotheses mean.)

## 1. Main declarations (file `SparseGcd/Main.lean`)

| Declaration | Type (informal) | Paper |
|---|---|---|
| `SAT_mem_BPP_of_gcdSolver (C : PrimeConstruction) (S : GcdSolver) : SAT.language ∈ BPP` | an output-sensitive sparse gcd solver + the BCR/AIRR construction give SAT ∈ BPP | Thm 18 = Thm 3 |
| `NP_subset_BPP_of_gcdSolver C S : NP ⊆ BPP` | via Cook–Levin and BPP closure | Thm 18 |
| `no_gcdSolver_of_NP_not_subset_BPP C (h : ¬ NP ⊆ BPP) : IsEmpty GcdSolver` | contrapositive | Thm 3 (second sentence) |
| `SAT_mem_BPP_of_promiseBPP_rou C (h : PromiseBPP rouPromise) : SAT.language ∈ BPP` | a bounded-error polynomial-time decider of roots-of-unity detection gives SAT ∈ BPP | Thm 19 = Thm 4 |
| `NP_subset_BPP_of_promiseBPP_rou`, `NP_subset_BPP_of_rou_mem_P`, `NP_subset_BPP_of_rou_mem_BPP` | same, with `RootsOfUnity ∈ P` / `∈ BPP` as special cases | Thm 19 |
| `rou_not_promiseBPP_of_NP_not_subset_BPP`, `rou_not_mem_P_of_NP_not_subset_BPP` | contrapositives | Thm 4 (second sentence) |

`NP ⊄ BPP` itself is never asserted; both contrapositives are conditional theorems.

## 2. The hypotheses, precisely

### `PrimeConstruction` (Lemma 14, external, not closed)
A function `build : List Bool → List Bool` in complexitylib's `FP` (deterministic polynomial time on
all inputs), polynomials `seedLen`, `bitBound`, such that on input `pair (unaryN N) seed`:
* `sound`: whatever decodes as a package `(ℓ, c)` is valid: `|ℓ| = N`, distinct primes, `c ≥ 1`,
  `p = 1 + c ∏ ℓ` prime, `bitLength p ≤ bitBound(N)`;
* `success`: for `N ≥ 4`, over uniform seeds of length `seedLen(N)`, a valid package is produced with
  probability ≥ 1/2.
This is the bounded-cutoff form of the Las Vegas procedure of Bi–Cheng–Rojas; its proof needs effective
prime density in arithmetic progressions and polynomial-time primality testing (see DEPENDENCIES.md).
The paper's `c ≥ 11` is not needed.

### `GcdSolver` (hypothesis of Theorem 18)
A deterministic TM `tm` with a polynomial `time` such that for every *well-formed* instance
(`p` prime, `f`, `g` canonical term lists) it halts within `time(T + bitLength Δ + bitLength p)` steps with
the canonical term list of the monic gcd on its output tape (`OutputsWithin`), where
`T = max(|f|, |g|, |supp gcd|)` (the answer's size is part of `T`: output-sensitivity) and
`Δ = max(deg f, deg g)`. Nothing is assumed off the well-formed domain (no totality, no uniform time):
the reduction runs the machine under a clock computed from the instance and the promised answer size 2,
via complexitylib's `Cobham.simFn` (`Machine/Clock.lean`). Convention: `gcd(0,0) = 0`, empty support;
the gcd is monic otherwise; canonical term lists have strictly increasing exponents and residues in `[1,p)`.

### `PromiseBPP rouPromise` (hypothesis of Theorem 19)
the support modules' `PromiseBPP`: a probabilistic TM, all paths halting within a polynomial bound, accepting
yes-instances with probability ≥ 2/3 and no-instances with probability ≤ 1/3. `rouPromise` has
yes-instances `RootsOfUnity` = well-formed `(p, f, n)` (`p` prime, `f` canonical, `n ≥ 1`) with
`¬ IsCoprime f (X^n - 1)` (equivalently `deg gcd(f, X^n-1) > 0`, `Instances.not_isCoprime_iff_natDegree_pos`),
and no-instances the coprime well-formed instances. Polarity: "not coprime" is the *yes* side, matching the
paper's "accept when deg gcd > 0". `RootsOfUnity ∈ P` or `∈ BPP` implies the promise hypothesis.

## 3. Probability semantics
All probabilities are `Complexity.eventProb` over uniform bit strings of a fixed length (finite counting).
The final statement uses the support modules' `RandomTapeSolves (ofLanguage SAT.language) V ℓ`: a deterministic
`FP` verdict `V` on `pair x r` with `Pr_r[V correct] ≥ 2/3` for every `x`, converted to a `BPP` machine by
`mem_BPP_of_randomTape` (the support modules' guess-and-copy machine). Error accounting per trial (`Machine/Analysis`):
unsatisfiable input: `≤ 2/2^cnt + 1/2^cnt ≤ 1/(100 r)`; satisfiable: `≥ (1/A)(15/16)(9/10)(1-2/2^cnt)(1-1/2^cnt) ≥ 1/(2A)`,
with `A = 16(s+4)`, `r = 8A`, `2^cnt > 400 r`; over `r` trials: false accept `≤ 1/100`, all-reject `≤ 1/5`.
The per-trial bounds are `Machine/TrialUnsat.eventProb_trialAccept_le_of_unsat` and
`Machine/TrialSat.eventProb_trialAccept_ge_of_sat`, built on the six-segment seed decomposition of
`Machine/SeedSplit.lean`; the verdict level is `Machine/Analysis.lean`.
Isolation success is only `1/A(s)` per trial, so there is **no single BPP many-one reduction** in the
formalisation; the paper's abstract/conclusion phrase "NP-hard under BPP reductions" is realised only as the
BPP-consequence statements above.

## 4. Time semantics
Every string function of the reduction is shown to be in `FP` through Cobham's algebra
(`CobhamFP_eq_FP` of complexitylib), including modular exponentiation, term-list construction and
normalisation, the CNF parser, and the seed-block bookkeeping. The gcd solver is simulated for a clock of
`time(T' + bitLength Δ + bitLength p)` steps with `T' = max(|f|,|g|,2)`; on promised instances this equals the
machine's own run (`simFn_eq_of_outputsWithin`), off promise the simulation still stops in the same
polynomial time. Randomized deciders (Theorem 19) are amplified by majority over `12c+1` runs.

## 5. Paper inaccuracies / deviations found
See PAPER_MAP.md "Deviations". Summary: Lemma 14 citation numbering (1.11 vs 1.10); `c ≥ 11` unused;
`φ(E)/E ≥ (n+1)^{-2}` improved to `1/(m+1)`; uniform field sampling replaced by near-uniform sampling with
explicit bias; Las Vegas subroutines replaced by bounded-cutoff versions counted in the error budget; the
degree bound `D` of Theorem 19's instance is implicit; "many-one hardness" wording vs BPP consequence.

## 6. Not formalised
* The randomized (bounded-error, worst-case-time or expected-time) variant of the gcd solver in Theorem 18
  (the paper's "if `A_gcd` is randomized, amplify"). Theorem 19 covers randomized deciders.
* Any claim about fixed fields, deterministic Karp hardness, or `deg f ≤ n` (explicitly excluded by Remark 20).
