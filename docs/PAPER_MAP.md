# PAPER_MAP — arXiv 2606.12144v1, *Output-sensitive Sparse Polynomial GCD over Finite Fields is NP-hard*

Lean library `SparseGcd` (namespace `SparseGcd`), built on the vendored `SparseDivComplexity/` support modules
(from the companion formalization of arXiv 2606.12130) and `complexitylib edd0e9ec`. Unified notation: `m` variables, `k` clauses,
`E = ∏_{i<m} ℓ_i`, `Δ = 2E`, `T = max 2 (3m+8k)`, `s = |encode φ|`.

Status: **proved** = sorry-free in Lean, standard axioms only · **hypothesis** = an explicit structure that is a
parameter of the theorems, not proved · **reused** = imported from a pinned library.

| Paper item | Statement as formalised | Lean declaration | Status |
|---|---|---|---|
| Def 5–7 | literals, clauses, CNF, satisfiability | complexitylib `SAT.Lit/Clause/CNF/CNF.eval/CNF.Satisfiable`, `SAT.language` | reused |
| Thm 8 (Cook–Levin) | SAT is NP-hard | `Complexity.SAT.NPHard_language` | reused |
| Def 9 (parsimonious) | exact solution-count preservation via a uniquely forced auxiliary window | `WindowExt`, `card_solutions_of_windowExt`, `DefGadget`, `DefGadget.windowExt_append` (`Cnf/Gadgets`) | proved |
| Def 10 (Unique-3SAT promise) | clause size ≤ 3, all variables `< n`, `solutions φ n`, `UniqueSat φ n` | `BoundedClauses`, `CNF.VarsLt`, `solutions`, `UniqueSat` (`Cnf/Basic`) | proved |
| Lemma 12 (Valiant–Vazirani) | for `S ≠ ∅` with `2^k ≤ 4\|S\|` and `2\|S\| ≤ 2^k`, a uniform affine seed isolates one element of `S` in the zero cell with probability `≥ 1/8` | `eventProb_isolating_ge_of_pairwise`, `eventProb_isolatingSeeds_ge`, `exists_k_of_card` (`Cnf/Isolation`) | proved |
| Lemma 13 = 21 | randomized map `φ ↦ (ψ, n')`: clauses of size ≤ 3; unsat ⇒ unsat for every seed; sat ⇒ `Pr[UniqueSat] ≥ 1/(16(m₀+3))`; all gadget conversions parsimonious | `isolate`, `isolateSeed`, `isolate_unsat`, `isolateSeed_unsat`, `card_solutions_isolate`, `eventProb_isolateSeed_unique_ge`, `isolate_boundedClauses`, `isolate_varsLt` (`Cnf/Reduce`); gadgets `orGadget`, `xorGadget`, `xorChain`, `parityCnf`, `shortenClause` with `*_spec` (`Cnf/Gadgets`) | proved |
| Lemma 14 (BCR/AIRR) | poly-time procedure producing distinct primes `ℓ_1..ℓ_N`, `c ≥ 1`, prime `p = 1 + c∏ℓ_j`, `bitLength p ≤ poly(N)`, success `≥ 1/2` for `N ≥ 4` | `PrimeConstruction` (`Field/Construction`), with `firstPackage`, `firstPackage_sound`, `eventProb_firstPackage_none_le` | **hypothesis** |
| Lemma 15 = 22 | `E ∣ p−1`, `E/p ≤ 2^{-(N-m)}`, `bitLength E ≤ bitLength p`; ω of exact order `E` found by `ω = a^{(p-1)/E}` with the order test; success fraction `φ(E)/E ≥ 1/(m+1)`; `z_i` of order `ℓ_i` | `PrimePackage` with `E_dvd_p_sub_one`, `E_div_p_le`, `E_lt_p`, `size_E_le_size_p`, `totient_div_ge`, `prod_one_sub_inv_ge` (`Field/Package`); `OrderTest`, `orderOf_eq_iff_orderTest`, `goodBases`, `card_goodBases_mul`, `card_goodBases_ge` (`Field/PrimitiveRoot`); `RootData.orderOf_z` (`Poly/Encoding`) | proved |
| Lemma 16 = 23 | `R = X^E−1`, `B_i`, literal factors, `P_C`; common roots of `R` and all constraints ↔ satisfying assignments (CRT bijection); `\|supp R\| ≤ 2`, `\|supp B_i\| ≤ 3`, `\|supp P_C\| ≤ 8`, `deg ≤ 2E` | `RootData` with `R`, `B`, `litPoly`, `clausePoly`, `constraintPolys` and term-level `Rterms`/`Bterms`/`clauseTerms`/`constraintTerms`; `assignRoot`, `assignRoot_injective`, `commonZeros_constraintPolys`, `card_commonZeros_constraintPolys`, `commonZeros_eq_singleton_of_uniqueSat` (`Poly/Roots`); bounds `length_*`, `exponent_*`, `natDegree_*` (`Poly/Encoding`) | proved |
| Lemma 17 = 24 | `H = Σ u_j F_j`; `S ⊆ Z(R,H)` always; exactly one bad coefficient value per stray root; `Pr[Z(R,H) ≠ S] ≤ E/p`; `R` splits with distinct roots; monic `gcd(R,H) = ∏_{β ∈ Z(R), H(β)=0}(X−β)`; unsat ⇒ `gcd = 1`, unique ⇒ `gcd = X−α` | `Hpoly`, `commonZeros_subset_Hpoly`, `existsUnique_coeff`, `card_bad_coeffs_le`, `R_eq_prod`, `monicGcd_R_eq`, `monicGcd_of_success`, `length_termsOf_monicGcd_of_success` (`Poly/Compression`); `IsMonicGcd`, `monicGcd`, `termsOf` (`Poly/Gcd`) | proved |
| Lemma 25 | `\|supp H\| ≤ 3m+8k`, `deg H ≤ 2E`, polynomial bit length, computable in polynomial time | `length_Hterms_le`, `exponent_Hterms_le`, `natDegree_Hpoly_le` (`Poly/Encoding`); `length_encDivInstance_le`, `length_inst_le` (`Machine/StageLemmas`); `buildHStr_eq`, `cobham_buildHStr` (`Machine/TermsStr`) | proved |
| Machine sampling | near-uniform residues from fair bits, bias `≤ 2^{-n}`; per-attempt ω success `≥ 1/(4(m+1))`; compression failure `≤ 2E/p` | `eventProb_bitsVal_mod_le/ge` (`Field/Sampling`); `eventProb_omegaGood_ge`, `eventProb_findOmega_none_le_tenth`, `eventProb_compressionFail_le` (`Machine/SamplingProb`) | proved |
| Thm 18 = Thm 3 | an output-sensitive sparse gcd solver (deterministic TM, correct on well-formed instances within `time(T + bitLength Δ + bitLength p)` steps) gives `SAT ∈ BPP`, hence `NP ⊆ BPP` | `GcdSolver` (`Instances`), `clockedSolver`, `gcdOracle` (`Machine/Clock`), `SAT_mem_BPP_of_gcdSolver`, `NP_subset_BPP_of_gcdSolver` (`Main`) | proved (given `PrimeConstruction`) |
| Thm 19 = Thm 4 | deciding `¬ IsCoprime f (X^n−1)` (equivalently `deg gcd > 0`) for well-formed `(p,f,n)` in bounded-error polynomial time gives `SAT ∈ BPP`, hence `NP ⊆ BPP`; constructed instances have `n = E`, `deg ≤ 2E` | `RootsOfUnity`, `CoprimeRou`, `rouPromise`, `not_isCoprime_iff_natDegree_pos` (`Instances`), `rouOracle` (`Machine/Amplify`), `SAT_mem_BPP_of_promiseBPP_rou`, `NP_subset_BPP_of_rou_mem_P`, `NP_subset_BPP_of_rou_mem_BPP` (`Main`) | proved (given `PrimeConstruction`) |
| Lemma 26 (amplification) | `r = 8A(s)` trials; per-trial unsat `≤ 1/(100r)`, sat `≥ 1/(2A)`; verdict errors `≤ 1/100` and `≤ 1/5` | `trialOf`, `trialAccept`, `eventProb_trialAccept_le_of_stages`, `eventProb_trialAccept_ge_of_prefix` (`Machine/SeedSplit`); `eventProb_trialAccept_le_of_unsat` (`Machine/TrialUnsat`); `eventProb_trialAccept_ge_of_sat` (`Machine/TrialSat`); `eventProb_verdictAccept_le_of_not_mem`, `eventProb_verdictAccept_ge_of_mem`, `randomTapeSolves_SAT`, `SAT_mem_BPP` (`Machine/Analysis`) | proved |
| Contrapositives | under `NP ⊄ BPP`: no such solver, and no bounded-error polynomial-time decider | `no_gcdSolver_of_NP_not_subset_BPP`, `rou_not_promiseBPP_of_NP_not_subset_BPP`, `rou_not_mem_P_of_NP_not_subset_BPP` (`Main`) | proved |
| Remark 20 (scope) | variable prime fields, BPP consequence, `g = X^n−1`, `D = 2n`; no Karp hardness, no fixed field, no `deg f ≤ n` | nothing stronger is claimed anywhere in `Main.lean` | documented |

## Shared implementation

Sections 2 and 3 of the paper repeat the same construction; each is implemented once: isolation (13/21),
prime package (14–15/22), root encoding (16/23), compression (17/24), sparsity bounds (25). Both main
theorems run the same trial pipeline (`Machine/TrialData.trialData`, realised in Cobham's algebra by
`Machine/TrialStr.trialCore`) and differ only in the positive-degree oracle: Theorem 18 uses a clocked
gcd solver (`gcdOracle`), Theorem 19 an amplified promise-BPP decider (`rouOracle`). Both are instances of
the single interface `DegreeOracle`.

## Deviations from the paper (all deliberate, none weakening a claim)

1. **No BPP many-one reduction is claimed.** Isolation succeeds only with inverse-polynomial probability, so
   the abstract's "NP-hard under BPP many-one reductions" is realised as the BPP-consequence statements only.
2. **Isolation constant.** `k` is drawn from `bitLength(m₀+2)` fair bits, giving success `≥ 1/(16(m₀+3))`;
   the paper only asserts `1/P(|F|)`.
3. **Field sampling.** Uniform `𝔽_p` elements are replaced by `a mod p` for `a` uniform on `bitLength p + 1`
   bits; the bias `≤ 2^{-B}` is carried through every bound instead of being ignored.
4. **Las Vegas ⇒ bounded cutoff.** The prime construction gets 4 attempts and the ω search `36(Vmax+1)`;
   cutoff failures are charged to the error budget, as the paper's Lemma 26 remark suggests.
5. **Constants.** `e^{-4}` is replaced by the verified `(1-x)^n ≤ 1/(1+nx)`; `φ(E)/E ≥ 1/(m+1)` improves the
   paper's `(n+1)^{-2}`; `c ≥ 11` of Lemma 14/22 is unused (`c ≥ 1` suffices).
6. **Citation.** The paper cites Bi–Cheng–Rojas "Theorem 1.11"; the author version at hand numbers it 1.10.
7. **Theorem 19 instances.** The degree bound `D` is not part of the encoded instance; it is implied by `f`
   and `n`. The language is stated with `¬ IsCoprime` and proved equivalent to `deg gcd > 0`.
8. **Seed length.** The verdict's seed length `r(s)·L(s)` is not a polynomial (it contains a bit length), so
   `seedPoly` is a polynomial upper bound and the verdict is proved to read only its first `r(s)·L(s)` bits.
9. **`Zmax`.** The instance-length reservation was enlarged during proof: each encoded term of `H` costs
   `4·size c + 2·size e + 6` bits and `H` has up to `3m+8k` terms.
