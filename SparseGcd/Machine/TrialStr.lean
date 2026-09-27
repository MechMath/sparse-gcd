import SparseGcd.Machine.CnfStr
import SparseGcd.Machine.ArithStr
import SparseGcd.Machine.TermsStr

/-!
# The trial and the verdict as strings (Cobham layer)

`trialStr C Or (pair x seed)` computes `[trialData C Or |x| φ seed]` when `x = CNF.encode φ`, and
`verdictStr C Or (pair x seed)` computes `[verdictData C Or x seed]`. All block lengths are
polynomial-length rulers computed from `x` (`polyUnary`), so both are in `FP`.

## Implementation notes

* Every parameter of `Machine/TrialData.lean` (`A`, `r`, `cnt`, `Vmax`, …, `L`) is computed as a
  unary ruler from the unary ruler `su = unaryN s`: sums are concatenations, products are
  `Complexity.smash`, the polynomial evaluations `C.seedLen`, `C.bitBound`, `Or.σ` are `polyUnary`,
  and `cnt s = Nat.size (400 r s)` is the length of the binary numeral `unaryToBinStr`.
* `trialCore` is a composition of the imported string functions (no loop of its own), split into
  three stages so that each correctness proof is a chain of rewrites; `verdictStr` iterates
  `trialCore` over the `r s` consecutive seed blocks with a clocked iteration (`Cobham.iterFn`)
  on the state `pair rem acc`.
-/

open Complexity SAT SparseDiv SparseDiv.StringArith

namespace SparseGcd

/-! ### Elementary helpers -/

theorem smash_unaryN (a b : ℕ) : Complexity.smash (unaryN a) (unaryN b) = unaryN (a * b) := by
  simp [Complexity.smash, unaryN]

theorem unaryN_append (a b : ℕ) : unaryN a ++ unaryN b = unaryN (a + b) := (unaryN_add a b).symm

/-- The all-`true` string of the length of `x`. -/
theorem smash_unaryN_one (x : List Bool) : Complexity.smash x (unaryN 1) = unaryN x.length := by
  simp [Complexity.smash, unaryN]

theorem eqFlag_eq_decide (a b : List Bool) : Cobham.eqFlag a b = [decide (a = b)] := by
  rcases Cobham.eqFlag_flag a b with h | h
  · rw [h, decide_eq_true ((Cobham.eqFlag_eq_true_iff a b).mp h)]
  · rw [h]
    have hne : ¬ a = b := fun heq ↦ by
      rw [(Cobham.eqFlag_eq_true_iff a b).mpr heq] at h
      simp at h
    rw [decide_eq_false hne]

theorem caseBit₀_pair_true (x a b : List Bool) : caseBit₀ (pair [true] x) a b = a := by
  rw [pair_cons_eq]
  rfl

theorem caseBit₀_false (a b : List Bool) : caseBit₀ [false] a b = b := rfl

/-- A block of `seed` at a unary offset with a unary length. -/
def blockStr (off len seed : List Bool) : List Bool := (seed.drop off.length).take len.length

theorem blockStr_unaryN (a b : ℕ) (seed : List Bool) :
    blockStr (unaryN a) (unaryN b) seed = block seed a b := by
  simp [blockStr, block]

theorem cobham_blockStr_comp {n : ℕ} {g₀ g₁ g₂ : (Fin n → List Bool) → List Bool}
    (h₀ : Cobham g₀) (h₁ : Cobham g₁) (h₂ : Cobham g₂) :
    Cobham fun v : Fin n → List Bool ↦ blockStr (g₀ v) (g₁ v) (g₂ v) :=
  Cobham.takeFn h₁ (Cobham.dropFn h₀ h₂)

/-- The encoded divisibility instance, as nested pairs. -/
theorem pair_encNat_eq_encDivInstance (p : ℕ) (f g : Terms) :
    pair (encNat p) (pair (encTerms f) (encTerms g)) = encDivInstance p f g := rfl

/-! ### Composition helpers of higher arity -/

theorem cobham_comp₄ {n : ℕ} {f : (Fin 4 → List Bool) → List Bool}
    {g₀ g₁ g₂ g₃ : (Fin n → List Bool) → List Bool}
    (hf : Cobham f) (h₀ : Cobham g₀) (h₁ : Cobham g₁) (h₂ : Cobham g₂) (h₃ : Cobham g₃) :
    Cobham fun v : Fin n → List Bool ↦ f ![g₀ v, g₁ v, g₂ v, g₃ v] := by
  refine (Cobham.comp hf (gs := ![g₀, g₁, g₂, g₃]) ?_).of_eq fun v ↦ ?_
  · intro i; fin_cases i <;> assumption
  · congr 1
    funext i
    fin_cases i <;> rfl

theorem cobham_comp₅ {n : ℕ} {f : (Fin 5 → List Bool) → List Bool}
    {g₀ g₁ g₂ g₃ g₄ : (Fin n → List Bool) → List Bool}
    (hf : Cobham f) (h₀ : Cobham g₀) (h₁ : Cobham g₁) (h₂ : Cobham g₂) (h₃ : Cobham g₃)
    (h₄ : Cobham g₄) :
    Cobham fun v : Fin n → List Bool ↦ f ![g₀ v, g₁ v, g₂ v, g₃ v, g₄ v] := by
  refine (Cobham.comp hf (gs := ![g₀, g₁, g₂, g₃, g₄]) ?_).of_eq fun v ↦ ?_
  · intro i; fin_cases i <;> assumption
  · congr 1
    funext i
    fin_cases i <;> rfl

theorem cobham_comp₆ {n : ℕ} {f : (Fin 6 → List Bool) → List Bool}
    {g₀ g₁ g₂ g₃ g₄ g₅ : (Fin n → List Bool) → List Bool}
    (hf : Cobham f) (h₀ : Cobham g₀) (h₁ : Cobham g₁) (h₂ : Cobham g₂) (h₃ : Cobham g₃)
    (h₄ : Cobham g₄) (h₅ : Cobham g₅) :
    Cobham fun v : Fin n → List Bool ↦ f ![g₀ v, g₁ v, g₂ v, g₃ v, g₄ v, g₅ v] := by
  refine (Cobham.comp hf (gs := ![g₀, g₁, g₂, g₃, g₄, g₅]) ?_).of_eq fun v ↦ ?_
  · intro i; fin_cases i <;> assumption
  · congr 1
    funext i
    fin_cases i <;> rfl

theorem cobham_comp₈ {n : ℕ} {f : (Fin 8 → List Bool) → List Bool}
    {g₀ g₁ g₂ g₃ g₄ g₅ g₆ g₇ : (Fin n → List Bool) → List Bool}
    (hf : Cobham f) (h₀ : Cobham g₀) (h₁ : Cobham g₁) (h₂ : Cobham g₂) (h₃ : Cobham g₃)
    (h₄ : Cobham g₄) (h₅ : Cobham g₅) (h₆ : Cobham g₆) (h₇ : Cobham g₇) :
    Cobham fun v : Fin n → List Bool ↦ f ![g₀ v, g₁ v, g₂ v, g₃ v, g₄ v, g₅ v, g₆ v, g₇ v] := by
  refine (Cobham.comp hf (gs := ![g₀, g₁, g₂, g₃, g₄, g₅, g₆, g₇]) ?_).of_eq fun v ↦ ?_
  · intro i; fin_cases i <;> assumption
  · congr 1
    funext i
    fin_cases i <;> rfl

/-! ### The parameters of the reduction as unary strings

Each `XStr su` computes `unaryN (X s)` on `su = unaryN s`. -/

def AStr (su : List Bool) : List Bool := Complexity.smash (unaryN 16) (su ++ unaryN 4)

def rStr (su : List Bool) : List Bool := Complexity.smash (unaryN 8) (AStr su)

def cntStr (su : List Bool) : List Bool :=
  Complexity.smash (unaryToBinStr (Complexity.smash (unaryN 400) (rStr su))) (unaryN 1)

def VmaxStr (su : List Bool) : List Bool :=
  (su ++ unaryN 1) ++ su ++ Complexity.smash (su ++ unaryN 3) (su ++ unaryN 1)

def KmaxStr (su : List Bool) : List Bool :=
  Complexity.smash (unaryN 3) su ++ su ++
    Complexity.smash (su ++ unaryN 3) (Complexity.smash (unaryN 4) (su ++ unaryN 1) ++ unaryN 1)

def NnStr (su : List Bool) : List Bool := VmaxStr su ++ cntStr su ++ unaryN 4

def taStr (su : List Bool) : List Bool := Complexity.smash (unaryN 36) (VmaxStr su ++ unaryN 1)

def TmaxStr (su : List Bool) : List Bool := VmaxStr su ++ KmaxStr su

def KBStr (su : List Bool) : List Bool := kBitsStr (su ++ unaryN 1)

def HBStr (su : List Bool) : List Bool := hashBitsStr (su ++ unaryN 1)

theorem AStr_unaryN (s : ℕ) : AStr (unaryN s) = unaryN (A s) := by
  simp only [AStr, unaryN_append, smash_unaryN, A]

theorem rStr_unaryN (s : ℕ) : rStr (unaryN s) = unaryN (r s) := by
  simp only [rStr, AStr_unaryN, smash_unaryN, r]

theorem cntStr_unaryN (s : ℕ) : cntStr (unaryN s) = unaryN (cnt s) := by
  rw [cntStr, rStr_unaryN, smash_unaryN, unaryToBinStr_unaryN, smash_unaryN_one, length_encNat, cnt]

theorem VmaxStr_unaryN (s : ℕ) : VmaxStr (unaryN s) = unaryN (Vmax s) := by
  simp only [VmaxStr, unaryN_append, smash_unaryN, Vmax]

theorem KmaxStr_unaryN (s : ℕ) : KmaxStr (unaryN s) = unaryN (Kmax s) := by
  simp only [KmaxStr, unaryN_append, smash_unaryN, Kmax]

theorem NnStr_unaryN (s : ℕ) : NnStr (unaryN s) = unaryN (Nn s) := by
  simp only [NnStr, VmaxStr_unaryN, cntStr_unaryN, unaryN_append, Nn]

theorem taStr_unaryN (s : ℕ) : taStr (unaryN s) = unaryN (ta s) := by
  simp only [taStr, VmaxStr_unaryN, unaryN_append, smash_unaryN, ta]

theorem TmaxStr_unaryN (s : ℕ) : TmaxStr (unaryN s) = unaryN (Tmax s) := by
  simp only [TmaxStr, VmaxStr_unaryN, KmaxStr_unaryN, unaryN_append, Tmax]

theorem KBStr_unaryN (s : ℕ) : KBStr (unaryN s) = unaryN (KB s) := by
  rw [KBStr, unaryN_append, kBitsStr_unaryN, KB]

theorem HBStr_unaryN (s : ℕ) : HBStr (unaryN s) = unaryN (HB s) := by
  rw [HBStr, unaryN_append, hashBitsStr_unaryN, HB]

section CobhamParams

variable {n : ℕ} {g : (Fin n → List Bool) → List Bool} (hg : Cobham g)
include hg

theorem cobham_AStr_comp : Cobham fun v ↦ AStr (g v) :=
  cobham_smash_comp (Cobham.const _) (Cobham.appendFn hg (Cobham.const _))

theorem cobham_rStr_comp : Cobham fun v ↦ rStr (g v) :=
  cobham_smash_comp (Cobham.const _) (cobham_AStr_comp hg)

theorem cobham_cntStr_comp : Cobham fun v ↦ cntStr (g v) :=
  cobham_smash_comp (cobham_comp₁ cobham_unaryToBinStr
    (cobham_smash_comp (Cobham.const _) (cobham_rStr_comp hg))) (Cobham.const _)

theorem cobham_VmaxStr_comp : Cobham fun v ↦ VmaxStr (g v) :=
  Cobham.appendFn (Cobham.appendFn (Cobham.appendFn hg (Cobham.const _)) hg)
    (cobham_smash_comp (Cobham.appendFn hg (Cobham.const _)) (Cobham.appendFn hg (Cobham.const _)))

theorem cobham_KmaxStr_comp : Cobham fun v ↦ KmaxStr (g v) :=
  Cobham.appendFn (Cobham.appendFn (cobham_smash_comp (Cobham.const _) hg) hg)
    (cobham_smash_comp (Cobham.appendFn hg (Cobham.const _))
      (Cobham.appendFn (cobham_smash_comp (Cobham.const _) (Cobham.appendFn hg (Cobham.const _)))
        (Cobham.const _)))

theorem cobham_NnStr_comp : Cobham fun v ↦ NnStr (g v) :=
  Cobham.appendFn (Cobham.appendFn (cobham_VmaxStr_comp hg) (cobham_cntStr_comp hg)) (Cobham.const _)

theorem cobham_taStr_comp : Cobham fun v ↦ taStr (g v) :=
  cobham_smash_comp (Cobham.const _) (Cobham.appendFn (cobham_VmaxStr_comp hg) (Cobham.const _))

theorem cobham_TmaxStr_comp : Cobham fun v ↦ TmaxStr (g v) :=
  Cobham.appendFn (cobham_VmaxStr_comp hg) (cobham_KmaxStr_comp hg)

theorem cobham_KBStr_comp : Cobham fun v ↦ KBStr (g v) :=
  cobham_comp₁ (FP_subset_CobhamFP kBitsStr_mem_FP) (Cobham.appendFn hg (Cobham.const _))

theorem cobham_HBStr_comp : Cobham fun v ↦ HBStr (g v) :=
  cobham_comp₁ (FP_subset_CobhamFP hashBitsStr_mem_FP) (Cobham.appendFn hg (Cobham.const _))

end CobhamParams

namespace PrimeConstruction

variable (C : PrimeConstruction)

noncomputable def LpStr (su : List Bool) : List Bool := polyUnary C.seedLen (NnStr su)

noncomputable def BbStr (su : List Bool) : List Bool := polyUnary C.bitBound (NnStr su) ++ unaryN 1

def o2Str (_C : PrimeConstruction) (su : List Bool) : List Bool := KBStr su ++ HBStr su

noncomputable def o3Str (su : List Bool) : List Bool :=
  C.o2Str su ++ Complexity.smash (unaryN tp) (C.LpStr su)

noncomputable def o4Str (su : List Bool) : List Bool :=
  C.o3Str su ++ Complexity.smash (taStr su) (C.BbStr su)

noncomputable def o5Str (su : List Bool) : List Bool :=
  C.o4Str su ++ Complexity.smash (TmaxStr su) (C.BbStr su)

noncomputable def ZmaxStr (su : List Bool) : List Bool :=
  Complexity.smash (unaryN 4)
    (Complexity.smash (unaryN 2) (C.BbStr su) ++ unaryN 2 ++
      (Complexity.smash (unaryN 2) (Complexity.smash (unaryN 8) (C.BbStr su ++ unaryN 4)) ++ unaryN 2 ++
        Complexity.smash
          (Complexity.smash (unaryN 3) (VmaxStr su) ++ Complexity.smash (unaryN 8) (KmaxStr su))
          (Complexity.smash (unaryN 8) (C.BbStr su ++ unaryN 4)))) ++ unaryN 4

theorem LpStr_unaryN (s : ℕ) : C.LpStr (unaryN s) = unaryN (C.Lp s) := by
  rw [LpStr, polyUnary_eq, NnStr_unaryN, length_unaryN, Lp]

theorem BbStr_unaryN (s : ℕ) : C.BbStr (unaryN s) = unaryN (C.Bb s) := by
  rw [BbStr, polyUnary_eq, NnStr_unaryN, length_unaryN, unaryN_append, Bb]

theorem o2Str_unaryN (s : ℕ) : C.o2Str (unaryN s) = unaryN (C.o2 s) := by
  rw [o2Str, KBStr_unaryN, HBStr_unaryN, unaryN_append, o2]

theorem o3Str_unaryN (s : ℕ) : C.o3Str (unaryN s) = unaryN (C.o3 s) := by
  rw [o3Str, o2Str_unaryN, LpStr_unaryN, smash_unaryN, unaryN_append, o3]

theorem o4Str_unaryN (s : ℕ) : C.o4Str (unaryN s) = unaryN (C.o4 s) := by
  rw [o4Str, o3Str_unaryN, taStr_unaryN, BbStr_unaryN, smash_unaryN, unaryN_append, o4]

theorem o5Str_unaryN (s : ℕ) : C.o5Str (unaryN s) = unaryN (C.o5 s) := by
  rw [o5Str, o4Str_unaryN, TmaxStr_unaryN, BbStr_unaryN, smash_unaryN, unaryN_append, o5]

theorem ZmaxStr_unaryN (s : ℕ) : C.ZmaxStr (unaryN s) = unaryN (C.Zmax s) := by
  simp only [ZmaxStr, BbStr_unaryN, VmaxStr_unaryN, KmaxStr_unaryN, unaryN_append, smash_unaryN, Zmax]

section CobhamParams

variable {n : ℕ} {g : (Fin n → List Bool) → List Bool} (hg : Cobham g)
include hg

theorem cobham_LpStr_comp : Cobham fun v ↦ C.LpStr (g v) :=
  cobham_polyUnary _ (cobham_NnStr_comp hg)

theorem cobham_BbStr_comp : Cobham fun v ↦ C.BbStr (g v) :=
  Cobham.appendFn (cobham_polyUnary _ (cobham_NnStr_comp hg)) (Cobham.const _)

theorem cobham_o2Str_comp : Cobham fun v ↦ C.o2Str (g v) :=
  Cobham.appendFn (cobham_KBStr_comp hg) (cobham_HBStr_comp hg)

theorem cobham_o3Str_comp : Cobham fun v ↦ C.o3Str (g v) :=
  Cobham.appendFn (cobham_o2Str_comp C hg) (cobham_smash_comp (Cobham.const _) (cobham_LpStr_comp C hg))

theorem cobham_o4Str_comp : Cobham fun v ↦ C.o4Str (g v) :=
  Cobham.appendFn (cobham_o3Str_comp C hg)
    (cobham_smash_comp (cobham_taStr_comp hg) (cobham_BbStr_comp C hg))

theorem cobham_o5Str_comp : Cobham fun v ↦ C.o5Str (g v) :=
  Cobham.appendFn (cobham_o4Str_comp C hg)
    (cobham_smash_comp (cobham_TmaxStr_comp hg) (cobham_BbStr_comp C hg))

theorem cobham_ZmaxStr_comp : Cobham fun v ↦ C.ZmaxStr (g v) := by
  have hBb := cobham_BbStr_comp C hg
  have hBb4 := Cobham.appendFn hBb (Cobham.const (unaryN 4))
  have h8 := cobham_smash_comp (Cobham.const (unaryN 8)) hBb4
  exact Cobham.appendFn (cobham_smash_comp (Cobham.const _)
    (Cobham.appendFn (Cobham.appendFn (cobham_smash_comp (Cobham.const _) hBb) (Cobham.const _))
      (Cobham.appendFn (Cobham.appendFn (cobham_smash_comp (Cobham.const _) h8) (Cobham.const _))
        (cobham_smash_comp (Cobham.appendFn (cobham_smash_comp (Cobham.const _) (cobham_VmaxStr_comp hg))
          (cobham_smash_comp (Cobham.const _) (cobham_KmaxStr_comp hg))) h8)))) (Cobham.const _)

end CobhamParams

end PrimeConstruction

namespace DegreeOracle

variable (Or : DegreeOracle) (C : PrimeConstruction)

noncomputable def σOrStr (su : List Bool) : List Bool := polyUnary Or.σ (cntStr su ++ C.ZmaxStr su)

noncomputable def LStr (su : List Bool) : List Bool := C.o5Str su ++ Or.σOrStr C su

theorem σOrStr_unaryN (s : ℕ) : Or.σOrStr C (unaryN s) = unaryN (Or.σOr C s) := by
  rw [σOrStr, polyUnary_eq, cntStr_unaryN, PrimeConstruction.ZmaxStr_unaryN, unaryN_append,
    length_unaryN, σOr]

theorem LStr_unaryN (s : ℕ) : Or.LStr C (unaryN s) = unaryN (Or.L C s) := by
  rw [LStr, PrimeConstruction.o5Str_unaryN, σOrStr_unaryN, unaryN_append, L]

theorem cobham_σOrStr_comp {n : ℕ} {g : (Fin n → List Bool) → List Bool} (hg : Cobham g) :
    Cobham fun v ↦ Or.σOrStr C (g v) :=
  cobham_polyUnary _ (Cobham.appendFn (cobham_cntStr_comp hg) (PrimeConstruction.cobham_ZmaxStr_comp C hg))

theorem cobham_LStr_comp {n : ℕ} {g : (Fin n → List Bool) → List Bool} (hg : Cobham g) :
    Cobham fun v ↦ Or.LStr C (g v) :=
  Cobham.appendFn (PrimeConstruction.cobham_o5Str_comp C hg) (cobham_σOrStr_comp Or C hg)

/-! ### The trial -/

/-- Third stage: build `H`, the instance, and query the oracle. Arguments: `su`, `encCNFU ψ`,
`unaryN m`, `encNat p`, `encNat E`, framed `ℓm`, `encNat w`, the seed. -/
noncomputable def trialStage3 (Or : DegreeOracle) (C : PrimeConstruction)
    (su ψs ms p E ℓm w seed : List Bool) : List Bool :=
  let H := buildHStr p E ℓm w ms ψs (C.BbStr su)
    (blockStr (C.o4Str su) (Complexity.smash (TmaxStr su) (C.BbStr su)) seed)
  let z := Or.instStr (pair p (pair (RtermsStr p E) H))
  Cobham.eqFlag (Or.O (pair (cntStr su) (pair z (blockStr (C.o5Str su) (Or.σOrStr C su) seed)))) [true]

/-- Second stage: the prime, `E`, and the search for `ω`. Arguments: `su`, `encCNFU ψ`,
`unaryN m`, `encPackage ℓ c`, the seed. -/
noncomputable def trialStage2 (Or : DegreeOracle) (C : PrimeConstruction)
    (su ψs ms pk seed : List Bool) : List Bool :=
  let ℓ := pairFst pk
  let p := canonBits (succBits (mulBits (pairSnd pk) (prodStr ℓ)))
  let ℓm := takeBlocksStr ms ℓ
  let E := canonBits (prodStr ℓm)
  let ω := findOmegaStr p E ℓm (taStr su) (C.BbStr su)
    (blockStr (C.o3Str su) (Complexity.smash (taStr su) (C.BbStr su)) seed)
  caseBit₀ ω (Or.trialStage3 C su ψs ms p E ℓm (pairSnd ω) seed) [false]

/-- The trial on the internal formula encoding `t = encCNFU φ`, with `s = |x|` given as the
unary ruler `su`. -/
noncomputable def trialCore (Or : DegreeOracle) (C : PrimeConstruction) (su t seed : List Bool) :
    List Bool :=
  let m₀ := numVarsStr t
  let ψn := isolateStr (pair t (pair (blockStr (unaryN 0) (kBitsStr m₀) seed)
    (blockStr (KBStr su) (hashBitsStr m₀) seed)))
  let pkg := packageStr C (NnStr su) (unaryN tp) (C.LpStr su)
    (blockStr (C.o2Str su) (Complexity.smash (unaryN tp) (C.LpStr su)) seed)
  caseBit₀ pkg (Or.trialStage2 C su (pairFst ψn) (pairSnd ψn) (pairSnd pkg) seed) [false]

theorem trialStage3_eq (s : ℕ) (ψ : CNF) (m p E : ℕ) (ℓm : List ℕ) (w : ℕ) (seed : List Bool)
    (hp : 0 < p) (hψ : BoundedClauses ψ) :
    Or.trialStage3 C (unaryN s) (encCNFU ψ) (unaryN m) (encNat p) (encNat E) (frame (ℓm.map encNat))
        (encNat w) seed =
      [decide (Or.O (pair (unaryN (cnt s)) (pair (Or.inst p (rawRterms p E)
        (buildH p E ℓm w m ψ (C.Bb s) (block seed (C.o4 s) (Tmax s * C.Bb s))))
        (block seed (C.o5 s) (Or.σOr C s)))) = [true])] := by
  simp only [trialStage3]
  rw [PrimeConstruction.o4Str_unaryN, TmaxStr_unaryN, PrimeConstruction.BbStr_unaryN, smash_unaryN,
    blockStr_unaryN, buildHStr_eq _ _ _ _ _ _ _ _ hp hψ, RtermsStr_eq, pair_encNat_eq_encDivInstance,
    Or.instStr_eq, cntStr_unaryN, PrimeConstruction.o5Str_unaryN, σOrStr_unaryN, blockStr_unaryN,
    eqFlag_eq_decide]

theorem trialStage2_eq (s : ℕ) (ψ : CNF) (m : ℕ) (ℓ : List ℕ) (c : ℕ) (seed : List Bool)
    (hψ : BoundedClauses ψ) :
    Or.trialStage2 C (unaryN s) (encCNFU ψ) (unaryN m) (encPackage ℓ c) seed =
      match findOmega (1 + c * ℓ.prod) (ℓ.take m).prod (ℓ.take m) (ta s) (C.Bb s)
          (block seed (C.o3 s) (ta s * C.Bb s)) with
      | none => [false]
      | some w => [decide (Or.O (pair (unaryN (cnt s)) (pair (Or.inst (1 + c * ℓ.prod)
          (rawRterms (1 + c * ℓ.prod) (ℓ.take m).prod)
          (buildH (1 + c * ℓ.prod) (ℓ.take m).prod (ℓ.take m) w m ψ (C.Bb s)
            (block seed (C.o4 s) (Tmax s * C.Bb s))))
          (block seed (C.o5 s) (Or.σOr C s)))) = [true])] := by
  have hp : canonBits (succBits (mulBits (pairSnd (encPackage ℓ c)) (prodStr (pairFst (encPackage ℓ c))))) =
      encNat (1 + c * ℓ.prod) := by
    rw [encPackage, pairFst_pair, pairSnd_pair, canonBits, decNat_succBits, decNat_mulBits,
      decNat_encNat, decNat_prodStr, Nat.add_comm]
  have hℓm : takeBlocksStr (unaryN m) (pairFst (encPackage ℓ c)) = frame ((ℓ.take m).map encNat) := by
    rw [encPackage, pairFst_pair, takeBlocksStr_frame, List.map_take]
  have hE : canonBits (prodStr (frame ((ℓ.take m).map encNat))) = encNat (ℓ.take m).prod := by
    rw [canonBits, decNat_prodStr]
  have hp0 : decNat (encNat (1 + c * ℓ.prod)) ≠ 0 := by
    rw [decNat_encNat]
    omega
  simp only [trialStage2]
  rw [hp, hℓm, hE, taStr_unaryN, PrimeConstruction.BbStr_unaryN, PrimeConstruction.o3Str_unaryN,
    smash_unaryN, blockStr_unaryN, findOmegaStr_eq _ _ _ _ _ _ hp0, decNat_encNat, decNat_encNat]
  rcases findOmega (1 + c * ℓ.prod) (ℓ.take m).prod (ℓ.take m) (ta s) (C.Bb s)
      (block seed (C.o3 s) (ta s * C.Bb s)) with _ | w
  · rfl
  · rw [caseBit₀_pair_true, pairSnd_pair, trialStage3_eq _ _ _ _ _ _ _ _ _ _ (by omega) hψ]

theorem trialCore_eq (s : ℕ) (φ : CNF) (seed : List Bool) :
    Or.trialCore C (unaryN s) (encCNFU φ) seed = [Or.trialData C s φ seed] := by
  simp only [trialCore]
  rw [numVarsStr_encCNFU, kBitsStr_unaryN, hashBitsStr_unaryN, KBStr_unaryN, blockStr_unaryN,
    blockStr_unaryN, isolateStr_encCNFU, pairFst_pair, pairSnd_pair, NnStr_unaryN,
    PrimeConstruction.LpStr_unaryN, PrimeConstruction.o2Str_unaryN, smash_unaryN, blockStr_unaryN,
    packageStr_eq]
  unfold trialData
  rcases C.firstPackage (Nn s) tp (C.Lp s) (block seed (C.o2 s) (tp * C.Lp s)) with _ | ⟨ℓ, c⟩
  · rfl
  · simp only [caseBit₀_pair_true, pairSnd_pair]
    rw [trialStage2_eq _ _ _ _ _ _ _ _ (isolateSeed_boundedClauses _ _ _)]
    rcases findOmega (1 + c * ℓ.prod) (ℓ.take (isolateSeed φ (block seed 0 (kBits (φ.maxVar + 1)))
        (block seed (KB s) (hashBits (φ.maxVar + 1)))).2).prod
        (ℓ.take (isolateSeed φ (block seed 0 (kBits (φ.maxVar + 1)))
        (block seed (KB s) (hashBits (φ.maxVar + 1)))).2) (ta s) (C.Bb s)
        (block seed (C.o3 s) (ta s * C.Bb s)) with _ | w <;> rfl

theorem cobham_trialStage3 : Cobham fun v : Fin 8 → List Bool ↦
    Or.trialStage3 C (v 0) (v 1) (v 2) (v 3) (v 4) (v 5) (v 6) (v 7) := by
  have hsu : Cobham fun v : Fin 8 → List Bool ↦ v 0 := .proj 0
  have hBb := PrimeConstruction.cobham_BbStr_comp C hsu
  have hbits := cobham_blockStr_comp (PrimeConstruction.cobham_o4Str_comp C hsu)
    (cobham_smash_comp (cobham_TmaxStr_comp hsu) hBb) (Cobham.proj (n := 8) 7)
  have hH := cobham_comp₈ cobham_buildHStr (Cobham.proj (n := 8) 3) (Cobham.proj (n := 8) 4)
    (Cobham.proj (n := 8) 5) (Cobham.proj (n := 8) 6) (Cobham.proj (n := 8) 2)
    (Cobham.proj (n := 8) 1) hBb hbits
  have hR := Cobham.comp₂ cobham_RtermsStr (Cobham.proj (n := 8) 3) (Cobham.proj (n := 8) 4)
  have hz := cobham_comp₁ (FP_subset_CobhamFP Or.instStr_mem_FP)
    (cobham_pair_comp (Cobham.proj (n := 8) 3) (cobham_pair_comp hR hH))
  have hres := cobham_comp₁ (FP_subset_CobhamFP Or.O_mem_FP)
    (cobham_pair_comp (cobham_cntStr_comp hsu) (cobham_pair_comp hz
      (cobham_blockStr_comp (PrimeConstruction.cobham_o5Str_comp C hsu) (cobham_σOrStr_comp Or C hsu)
        (Cobham.proj (n := 8) 7))))
  exact (Cobham.eqFlag_mem hres (Cobham.const [true])).of_eq fun v ↦ rfl

theorem cobham_trialStage2 : Cobham fun v : Fin 5 → List Bool ↦
    Or.trialStage2 C (v 0) (v 1) (v 2) (v 3) (v 4) := by
  have hsu : Cobham fun v : Fin 5 → List Bool ↦ v 0 := .proj 0
  have hℓ := cobham_pairFst_comp (Cobham.proj (3 : Fin 5))
  have hp := cobham_canonBits_comp (cobham_succBits_comp (cobham_mulBits_comp
    (cobham_pairSnd_comp (.proj 3)) (cobham_comp₁ cobham_prodStr hℓ)))
  have hℓm := Cobham.comp₂ cobham_takeBlocksStr (.proj 2) hℓ
  have hE := cobham_canonBits_comp (cobham_comp₁ cobham_prodStr hℓm)
  have hta := cobham_taStr_comp hsu
  have hBb := PrimeConstruction.cobham_BbStr_comp C hsu
  have hω := cobham_comp₆ cobham_findOmegaStr hp hE hℓm hta hBb
    (cobham_blockStr_comp (PrimeConstruction.cobham_o3Str_comp C hsu) (cobham_smash_comp hta hBb)
      (.proj 4))
  have h3 := cobham_comp₈ (cobham_trialStage3 Or C) hsu (.proj 1) (.proj 2) hp hE hℓm
    (cobham_pairSnd_comp hω) (.proj 4)
  exact (Cobham.iteFn hω h3 (Cobham.const [false])).of_eq fun v ↦ rfl

theorem cobham_trialCore : Cobham fun v : Fin 3 → List Bool ↦ Or.trialCore C (v 0) (v 1) (v 2) := by
  have hsu : Cobham fun v : Fin 3 → List Bool ↦ v 0 := .proj 0
  have ht : Cobham fun v : Fin 3 → List Bool ↦ v 1 := .proj 1
  have hseed : Cobham fun v : Fin 3 → List Bool ↦ v 2 := .proj 2
  have hm₀ := cobham_comp₁ (FP_subset_CobhamFP numVarsStr_mem_FP) ht
  have hkb := cobham_blockStr_comp (Cobham.const (unaryN 0))
    (cobham_comp₁ (FP_subset_CobhamFP kBitsStr_mem_FP) hm₀) hseed
  have hhb := cobham_blockStr_comp (cobham_KBStr_comp hsu)
    (cobham_comp₁ (FP_subset_CobhamFP hashBitsStr_mem_FP) hm₀) hseed
  have hψn := cobham_comp₁ (FP_subset_CobhamFP isolateStr_mem_FP)
    (cobham_pair_comp ht (cobham_pair_comp hkb hhb))
  have hLp := PrimeConstruction.cobham_LpStr_comp C hsu
  have hpkg := cobham_comp₄ (cobham_packageStr C) (cobham_NnStr_comp hsu) (Cobham.const (unaryN tp))
    hLp (cobham_blockStr_comp (PrimeConstruction.cobham_o2Str_comp C hsu)
      (cobham_smash_comp (Cobham.const (unaryN tp)) hLp) hseed)
  have h2 := cobham_comp₅ (cobham_trialStage2 Or C) hsu (cobham_pairFst_comp hψn)
    (cobham_pairSnd_comp hψn) (cobham_pairSnd_comp hpkg) hseed
  exact (Cobham.iteFn hpkg h2 (Cobham.const [false])).of_eq fun v ↦ rfl

theorem cobham_trialCore_comp {n : ℕ} {g₀ g₁ g₂ : (Fin n → List Bool) → List Bool}
    (h₀ : Cobham g₀) (h₁ : Cobham g₁) (h₂ : Cobham g₂) :
    Cobham fun v : Fin n → List Bool ↦ Or.trialCore C (g₀ v) (g₁ v) (g₂ v) :=
  (Cobham.comp₃ (cobham_trialCore Or C) h₀ h₁ h₂).of_eq fun _ ↦ rfl

/-! ### The verdict -/

/-- One step of the verdict loop on the state `pair rem acc`: run the trial on the next block of
width `|L|` and OR its verdict into the accumulator. -/
noncomputable def verdictStep (Or : DegreeOracle) (C : PrimeConstruction) (su t L st : List Bool) :
    List Bool :=
  pair ((pairFst st).drop L.length)
    (orBit (pairSnd st) (Or.trialCore C su t ((pairFst st).take L.length)))

/-- The loop over `|clock|` blocks. -/
noncomputable def verdictLoop (Or : DegreeOracle) (C : PrimeConstruction)
    (su t L seed clock : List Bool) : List Bool :=
  pairSnd ((Or.verdictStep C su t L)^[clock.length] (pair seed [false]))

/-- The full verdict on `pair x seed`. -/
noncomputable def verdictStr (Or : DegreeOracle) (C : PrimeConstruction) (z : List Bool) : List Bool :=
  let x := pairFst z
  let su := Complexity.smash x (unaryN 1)
  let pc := parseCnfStr x
  caseBit₀ pc (Or.verdictLoop C su (pairSnd pc) (Or.LStr C su) (pairSnd z) (rStr su)) [false]

theorem verdictStep_iterate (su t L : List Bool) (F : List Bool → Bool)
    (hg : ∀ blk, Or.trialCore C su t blk = [F blk]) :
    ∀ (k : ℕ) (bits : List Bool) (a : Bool),
      (Or.verdictStep C su t L)^[k] (pair bits [a]) =
        pair (bits.drop (k * L.length))
          [a || (List.range k).any fun i ↦ F (block bits (i * L.length) L.length)] := by
  intro k
  induction k with
  | zero => intro bits a; simp
  | succ k ih =>
    intro bits a
    rw [Function.iterate_succ_apply', ih, verdictStep, pairFst_pair, pairSnd_pair, hg, orBit_single,
      List.drop_drop]
    simp [List.range_succ, block, Nat.succ_mul, Bool.or_assoc]

theorem verdictStr_eq (x seed : List Bool) : Or.verdictStr C (pair x seed) = [Or.verdictData C x seed] := by
  simp only [verdictStr, pairFst_pair, pairSnd_pair, smash_unaryN_one, parseCnfStr_eq, verdictData]
  cases hd : CNF.decode? x with
  | none => rfl
  | some φ =>
    simp only [caseBit₀_pair_true, pairSnd_pair, verdictLoop, rStr_unaryN, length_unaryN, LStr_unaryN]
    rw [verdictStep_iterate Or C _ _ _ (Or.trialData C x.length φ)
      (fun blk ↦ trialCore_eq Or C x.length φ blk), pairSnd_pair]
    simp only [length_unaryN, Bool.false_or]

theorem verdictStep_iterate_length_le (su t L seed : List Bool) (k : ℕ) :
    ((Or.verdictStep C su t L)^[k] (pair seed [false])).length ≤ 2 * seed.length + 3 := by
  suffices h : ∀ k, ∃ rem acc : List Bool,
      (Or.verdictStep C su t L)^[k] (pair seed [false]) = pair rem acc ∧
        rem.length ≤ seed.length ∧ acc.length = 1 by
    obtain ⟨rem, acc, h1, h2, h3⟩ := h k
    rw [h1, pair_length]
    omega
  intro k
  induction k with
  | zero => exact ⟨seed, [false], rfl, le_rfl, rfl⟩
  | succ k ih =>
    obtain ⟨rem, acc, h1, h2, h3⟩ := ih
    rw [Function.iterate_succ_apply', h1, verdictStep, pairFst_pair, pairSnd_pair]
    refine ⟨_, _, rfl, ?_, Cobham.orBit_length _ _⟩
    simp only [List.length_drop]
    omega

theorem cobham_verdictLoop : Cobham fun v : Fin 5 → List Bool ↦
    Or.verdictLoop C (v 1) (v 2) (v 3) (v 4) (v 0) := by
  have he : Cobham fun u : Fin 4 → List Bool ↦ pair (u 3) [false] :=
    cobham_pair_comp (.proj 3) (Cobham.const [false])
  have hf : Cobham fun w : Fin 5 → List Bool ↦ Or.verdictStep C (w 1) (w 2) (w 3) (w 0) :=
    cobham_pair_comp (Cobham.dropFn (.proj 3) (cobham_pairFst_comp (.proj 0)))
      (Cobham.orFn (cobham_pairSnd_comp (.proj 0))
        (cobham_trialCore_comp Or C (.proj 1) (.proj 2)
          (Cobham.takeFn (.proj 3) (cobham_pairFst_comp (.proj 0)))))
  have hj : Cobham fun w : Fin 5 → List Bool ↦ w 4 ++ w 4 ++ [false, false, false] :=
    Cobham.appendFn (Cobham.appendFn (.proj 4) (.proj 4)) (Cobham.const _)
  have hiter := Cobham.iterFn he hf hj (by
    intro c v
    show ((Or.verdictStep C (v 0) (v 1) (v 2))^[c.length] (pair (v 3) [false])).length ≤
      (v 3 ++ v 3 ++ [false, false, false]).length
    refine le_trans (verdictStep_iterate_length_le Or C _ _ _ _ _) ?_
    simp only [List.length_append, List.length_cons, List.length_nil]
    omega)
  exact (cobham_pairSnd_comp hiter).of_eq fun v ↦ rfl

theorem verdictStr_mem_FP : Or.verdictStr C ∈ FP := by
  rw [← CobhamFP_eq_FP]
  show Cobham fun v : Fin 1 → List Bool ↦ Or.verdictStr C (v 0)
  have hx : Cobham fun v : Fin 1 → List Bool ↦ pairFst (v 0) := cobham_pairFst_comp (.proj 0)
  have hsu := cobham_smash_comp hx (Cobham.const (unaryN 1))
  have hpc := cobham_comp₁ (FP_subset_CobhamFP parseCnfStr_mem_FP) hx
  have hloop := cobham_comp₅ (cobham_verdictLoop Or C) (cobham_rStr_comp hsu) hsu
    (cobham_pairSnd_comp hpc) (cobham_LStr_comp Or C hsu) (cobham_pairSnd_comp (.proj 0))
  exact (Cobham.iteFn hpc hloop (Cobham.const [false])).of_eq fun v ↦ rfl

end DegreeOracle

end SparseGcd
