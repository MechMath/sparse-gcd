# SparseGcd Lean Formalization

This repository contains the Lean 4 formalization of the complexity results in
the paper _Output-sensitive Sparse Polynomial GCD over Finite Fields is NP-hard_
(arXiv:2606.12144v1). It proves both main theorems of the paper:

- **Theorem 3 / Theorem 18.** An algorithm computing the sparse GCD of
  `f, g ∈ F_p[x]` in time polynomial in `T`, `log D` and `log p`, where `T`
  bounds the supports of `f`, `g` **and** `gcd(f, g)`, would give `SAT ∈ BPP`,
  hence `NP ⊆ BPP`.
- **Theorem 4 / Theorem 19.** A bounded-error polynomial-time algorithm deciding
  `deg gcd(f, x^n − 1) > 0` (roots-of-unity detection) would give `NP ⊆ BPP`.

Both results are conditional on one external theorem that is stated as an
explicit hypothesis rather than proved: the Bi–Cheng–Rojas randomized prime
construction (Lemma 14 of the paper), see [Axiom Boundary](#axiom-boundary).

The development is checked with Lean `v4.34.0-rc2` on top of
[complexitylib](https://github.com/SamuelSchlesinger/complexitylib) at commit
`edd0e9ec3d7d2eb00afa978338e8585a4eab8152`, which pins mathlib at
`e06eff5f95374108acfaf19f1ff7473aa7771df2`. `lake-manifest.json` locks every
dependency. Complexity classes (`FP`, `P`, `NP`, `BPP`), the Turing-machine
model, SAT and the Cook–Levin theorem are complexitylib's own definitions.

## Build

```bash
lake exe cache get
lake build
```

The first build compiles the needed part of complexitylib. The build succeeds
with no `sorry`, no `admit` and no custom `axiom`. Some linter warnings remain
(unused variables, a deprecated lemma name).

Axiom audit and small-instance tests:

```bash
bash scripts/audit.sh              # build, forbidden-token scan, #print axioms → docs/AXIOMS.txt
lake env lean SparseGcd/Tests.lean # decide/rfl boundary checks
```

## Layout

- `SparseGcd.lean`: root import for the formalization.
- `SparseGcd/Main.lean`: the paper-facing theorems and their contrapositives.
- `SparseGcd/Instances.lean`: the problems and the solver hypotheses —
  `GcdSolver` (output-sensitive GCD solver), `RootsOfUnity`, `rouPromise`.
- `SparseGcd/Basic/`: probability calculus on random seeds, elementary bounds.
- `SparseGcd/Cnf/`: parsimonious CNF gadgets, Valiant–Vazirani isolation, and
  the isolation reduction (Lemmas 12, 13, 21).
- `SparseGcd/Field/`: prime-field package, elements of exact order,
  near-uniform sampling from fair bits, and the prime-construction hypothesis
  (Lemmas 14, 15, 22).
- `SparseGcd/Poly/`: sparse encoding of a CNF, the Chinese-remainder bijection
  between satisfying assignments and common roots, monic GCDs, and random
  compression (Lemmas 16, 17, 23, 24, 25).
- `SparseGcd/Machine/`: one trial of the reduction at the data level
  (`TrialData`), its implementation in Cobham's algebra, which gives membership
  in `FP` (`CnfStr`, `ArithStr`, `TermsStr`, `TrialStr`), the clocked GCD
  solver (`Clock`), the amplified roots-of-unity decider (`Amplify`), and the
  error analysis (`SeedSplit`, `TrialUnsat`, `TrialSat`, `Analysis`, Lemma 26).
- `SparseGcd/Tests.lean`: small-instance sanity checks; not used by any proof.
- `SparseDivComplexity/`: support modules shared with the companion
  formalization of arXiv:2606.12130 (sparse term lists and their binary
  encoding, binary arithmetic in Cobham's algebra, randomized reductions and
  the random-tape ⇔ probabilistic-machine bridge).
- `docs/PAPER_MAP.md`: every numbered statement of the paper with its Lean
  declaration and status, plus the list of deliberate deviations.
- `docs/AUDIT.md`: the main declarations, the meaning of each hypothesis, and
  the probability and time semantics.
- `docs/DEPENDENCIES.md`: external mathematical and machine-model inputs.
- `docs/AXIOMS.txt`: output of `scripts/audit.sh`.

## Paper Correspondence

- Theorem 3 / Theorem 18: `SparseGcd.SAT_mem_BPP_of_gcdSolver`,
  `SparseGcd.NP_subset_BPP_of_gcdSolver`, and the contrapositive
  `SparseGcd.no_gcdSolver_of_NP_not_subset_BPP`.
- Theorem 4 / Theorem 19: `SparseGcd.SAT_mem_BPP_of_promiseBPP_rou`,
  `SparseGcd.NP_subset_BPP_of_promiseBPP_rou`,
  `SparseGcd.NP_subset_BPP_of_rou_mem_P`,
  `SparseGcd.NP_subset_BPP_of_rou_mem_BPP`, and the contrapositives
  `SparseGcd.rou_not_promiseBPP_of_NP_not_subset_BPP`,
  `SparseGcd.rou_not_mem_P_of_NP_not_subset_BPP`.
- Lemma 12 (Valiant–Vazirani): `SparseGcd.eventProb_isolatingSeeds_ge`.
- Lemma 13 / Lemma 21: `SparseGcd.isolate_unsat`,
  `SparseGcd.card_solutions_isolate`,
  `SparseGcd.eventProb_isolateSeed_unique_ge`.
- Lemma 15 / Lemma 22: `SparseGcd.PrimePackage.E_div_p_le`,
  `SparseGcd.card_goodBases_ge`, `SparseGcd.totient_div_ge`.
- Lemma 16 / Lemma 23: `SparseGcd.RootData.commonZeros_constraintPolys`.
- Lemma 17 / Lemma 24: `SparseGcd.RootData.existsUnique_coeff`,
  `SparseGcd.RootData.monicGcd_of_success`,
  `SparseGcd.eventProb_compressionFail_le`.
- Lemma 25: `SparseGcd.RootData.length_Hterms_le` and the exponent bounds in
  `SparseGcd/Poly/Encoding.lean`.
- Lemma 26: `SparseGcd.DegreeOracle.eventProb_trialAccept_le_of_unsat`,
  `SparseGcd.DegreeOracle.eventProb_trialAccept_ge_of_sat`,
  `SparseGcd.DegreeOracle.randomTapeSolves_SAT`.

The sections of the paper that repeat the same construction (Sections 2 and 3)
share a single implementation. The GCD solver hypothesis is stated for prime
fields `F_p`; since it is an assumption about an algorithm, this only makes the
theorem stronger. The randomized variant of the GCD solver in Theorem 18 is not
formalized; Theorem 19 covers randomized deciders.

The paper's abstract describes the result as NP-hardness under BPP many-one
reductions. The proof does not produce a single such reduction (the isolation
step succeeds only with inverse-polynomial probability), so the formalization
states the BPP consequences `SAT ∈ BPP` and `NP ⊆ BPP`. The remaining
deviations (bounded-cutoff versions of the Las Vegas subroutines, near-uniform
field sampling with explicit bias, verified constants) are listed in
`docs/PAPER_MAP.md`.

## Axiom Boundary

The development declares no `axiom`. Every headline theorem depends only on
`propext`, `Classical.choice` and `Quot.sound` (see `docs/AXIOMS.txt`).

One external result is taken as a hypothesis instead of being proved:

- `SparseGcd.PrimeConstruction` — the Bi–Cheng–Rojas / AIRR randomized
  construction of distinct primes `ℓ_1, …, ℓ_N` with `p = 1 + c ∏ ℓ_j` prime and
  `log p = poly(N)` (Lemma 14 of the paper). It is a structure passed as an
  explicit argument to every main theorem, so each theorem reads "given such a
  construction, …". Its proof needs effective density of primes in arithmetic
  progressions and a polynomial-time primality test with a proved time bound,
  neither of which is available in mathlib.

All other declarations are definitions, lemmas, or theorems proved inside the
project.
