# DEPENDENCIES — external mathematics and machine-complexity inputs of `SparseGcd`

Status legend: **closed** = fully proved in Lean here or in the pinned libraries; **hypothesis** = stated as an
explicit structure/parameter and *not* proved; **reused** = imported from a pinned library.

## Pinned libraries (lake-manifest.json)

| Library | Commit | Role |
|---|---|---|
| Lean toolchain | `leanprover/lean4:v4.34.0-rc2` | — |
| mathlib | `e06eff5f95374108acfaf19f1ff7473aa7771df2` | polynomials over `ZMod p`, roots of unity, CRT, totient, `Nat.size` |
| complexitylib (SamuelSchlesinger) | `edd0e9ec3d7d2eb00afa978338e8585a4eab8152` | TM model, `FP`/`P`/`NP`/`BPP`, Cobham algebra, `eventProb`, affine pairwise-independent hashing, SAT + Cook–Levin |
| cslib | as pinned by complexitylib | transitive |
| `SparseDivComplexity/` support modules (from the companion formalization of arXiv:2606.12130) | vendored in this repository | random-tape ⇔ PTM bridges, `mem_BPP_of_randomTape`, string arithmetic in Cobham's algebra, `Terms`/`normalize`/encodings |

## Mathematical dependencies

| Item | Where used | Status |
|---|---|---|
| Valiant–Vazirani isolation with a pairwise-independent affine family | Lemma 12/13/21 (`Cnf/Isolation`, `Cnf/Reduce`) | **closed** (own proof from `PairwiseIndependentHash.uniform/pairwise`) |
| Parsimonious CNF gadgets (OR/XOR chains) | Lemma 13/21 item 3 (`Cnf/Gadgets`) | **closed** |
| Cook–Levin (`SAT.NPHard_language`) | `Main.NP_subset_BPP_of_SAT_mem_BPP` | **reused** (complexitylib) |
| Closure of BPP under deterministic many-one reductions | `Main` | **reused** (the `SparseDivComplexity` support modules `mem_BPP_of_mapReducesBPP`) |
| BCR/AIRR prime construction (Lemma 14): distinct primes `ℓ_1..ℓ_N`, `p = 1 + c∏ℓ` prime, `log p = poly(N)`, Las Vegas poly time | `Field/Construction.PrimeConstruction`; both main theorems take it as a parameter | **hypothesis, not closed**. Blockers: effective density of primes in arithmetic progressions (BCR use it for `p`), polynomial-time primality testing (not in mathlib as an algorithm with a time bound), and a machine-level implementation. The same blocker keeps Theorem 5 of the companion divisibility paper (arXiv:2606.12130) unformalised. |
| Structure of `𝔽_p^*` (cyclic), counting elements of exact order `E` (`φ(E)(p-1)/E`) | Lemma 15/22 (`Field/PrimitiveRoot`) | **closed** (mathlib `IsCyclic`, `Nat.totient`) |
| Telescoping density `∏(1-1/ℓ_i) ≥ 1/(m+1)` | Lemma 15/22 | **closed** (`Field/Package.prod_one_sub_inv_ge`) |
| CRT bijection residues ↔ Boolean assignments | Lemma 16/23 (`Poly/Roots`) | **closed** (`Nat.chineseRemainderOfList`) |
| `X^E - 1` splits with distinct roots when `E ∣ p-1` | Lemma 17/24 (`Poly/Compression.R_eq_prod`) | **closed** (mathlib `X_pow_sub_one_eq_prod`) |
| Monic gcd theory (`IsMonicGcd`, product over common roots) | `Poly/Gcd` | **closed** |
| Near-uniformity of `a mod p` for `a` uniform on `n` bits (bias `≤ 2^{-n}`) | `Field/Sampling` | **closed** |
| Bernoulli-type bound `(1-x)^n ≤ 1/(1+nx)` | `Basic/Bernoulli` | **closed** |

## Machine-complexity dependencies

| Item | Where used | Status |
|---|---|---|
| `CobhamFP = FP` (Cobham's characterisation of polynomial time on complexitylib's TMs) | every `*_mem_FP` | **reused** |
| Deterministic simulation of a TM inside Cobham's algebra for a clock's worth of steps (`Cobham.simFn`, `simFn_eq`) | clocked gcd solver (`Machine/Clock`) | **reused**; per-input variant `simFn_eq_of_outputsWithin` proved here |
| Random-tape verdict in `FP` with error ≤ 1/3 ⇒ `BPP` (`mem_BPP_of_randomTape`) | `Machine/Analysis.SAT_mem_BPP` | **reused** (the `SparseDivComplexity` support modules) |
| PTM promise-BPP ⇒ random-tape verdict (`promiseRandomTapeBPP_of_promiseBPP`) | Theorem 19 hypothesis | **reused** (the `SparseDivComplexity` support modules) |
| Majority amplification `12c+1` blocks ⇒ error `2^{-c}` | `Machine/Amplify` | **reused** (complexitylib `eventProb_blockMajority_*_two_pow`) |
| Binary arithmetic (`add/sub/mul/div/mod`) in Cobham's algebra | `Machine/ArithStr` | **reused** (the `SparseDivComplexity` support modules `StringArith`); modular exponentiation added here |
| Term-list normalisation in Cobham's algebra (`normalizeStr`) | `Machine/TermsStr` | **reused** (the `SparseDivComplexity` support modules) |
| The randomized gcd-solver variant of Theorem 18 (bounded-error output) | not formalised | **out of scope** (see AUDIT.md); Theorem 19 already covers randomized deciders |

## What is *not* assumed

No axioms beyond `propext`, `Classical.choice`, `Quot.sound`; no `sorry`; the prime construction is a
*parameter* of the main theorems, never an `axiom`. No fixed-field hardness, no deterministic Karp hardness,
no `deg f ≤ n` strengthening are claimed (Remark 20 of the paper).
