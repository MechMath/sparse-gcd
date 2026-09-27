import SparseGcd.Cnf.Reduce
import SparseGcd.Field.Construction
import SparseGcd.Field.Sampling
import SparseGcd.Poly.Compression
import SparseGcd.Instances
import Complexitylib.SAT.Verifier

/-!
# One trial of the reduction, at the data level

`trialData C Or s φ seed` is a pure Lean function: it reads the seed blocks, isolates `φ`
(Lemma 13/21), obtains a prime package from the assumed construction `C` (Lemma 14/15/22),
searches an element `ω` of exact order `E` (Lemma 15/22), builds the sparse instance
`(R, H)` (Lemmas 16/23, 17/24, 25) and queries the *degree oracle* `Or` (the "does the gcd have
positive degree?" test, which Theorem 18 derives from a clocked output-sensitive gcd solver and
Theorem 19 from a promise-BPP decider). The machine layer (`Machine/*Str.lean`) implements the
same function in Cobham's algebra; the probability analysis (`Machine/Analysis.lean`) is carried
out on this function.

All arithmetic is on `ℕ`; the field structure is only used in the analysis.

## Seed layout of one trial (all block lengths depend only on `s = |x|` and `C`, `Or`)

`[k bits | hash bits | package attempts | ω attempts | coefficients | oracle seed]`
-/

open Complexity SAT SparseDiv Finset

namespace SparseGcd

/-! ### Elementary data-level operations -/

/-- `b^e mod p`. -/
def powMod (b e p : ℕ) : ℕ := b ^ e % p

/-- The executable order test on residues. -/
def orderTestNat (p E : ℕ) (ℓ : List ℕ) (w : ℕ) : Bool :=
  (powMod w E p == 1 % p) && ℓ.all fun q ↦ powMod w (E / q) p != 1 % p

/-- A block of a bit list. -/
def block (bits : List Bool) (off len : ℕ) : List Bool := (bits.drop off).take len

/-- The `i`-th `B`-bit sample reduced modulo `p`. -/
def sampleMod (p B : ℕ) (bits : List Bool) (i : ℕ) : ℕ := decNat (block bits (i * B) B) % p

/-- Search for `ω` of exact order `E` among `t` samples: `ω = a^{(p-1)/E}`. -/
def findOmega (p E : ℕ) (ℓ : List ℕ) (t B : ℕ) (bits : List Bool) : Option ℕ :=
  (List.range t).findSome? fun i ↦
    let w := powMod (sampleMod p B bits i) ((p - 1) / E) p
    if orderTestNat p E ℓ w then some w else none

/-- `R = X^E - 1` as canonical terms. -/
def rawRterms (p E : ℕ) : Terms := [(p - 1, 0), (1, E)]

/-- `B_i` as three terms (residue arithmetic). -/
def rawBterms (p E : ℕ) (ℓ : List ℕ) (w i : ℕ) : Terms :=
  let e := E / ℓ.getD i 2
  let z := powMod w e p
  [(1, 2 * e), ((p - (1 + z) % p) % p, e), (z, 0)]

/-- Literal factor as two terms. -/
def rawLitTerms (p E : ℕ) (ℓ : List ℕ) (w : ℕ) (l : Lit) : Terms :=
  let e := E / ℓ.getD l.var 2
  let z := if l.sign then powMod w e p else 1
  [(1, e), ((p - z % p) % p, 0)]

/-- Clause polynomial as terms. -/
def rawClauseTerms (p E : ℕ) (ℓ : List ℕ) (w : ℕ) (c : Clause) : Terms :=
  (c.map (rawLitTerms p E ℓ w)).foldr (RootData.mulTerms p) [(1, 0)]

/-- The constraint list `[B_0, …, B_{m-1}, P_{C_1}, …]`. -/
def rawConstraintTerms (p E : ℕ) (ℓ : List ℕ) (w m : ℕ) (ψ : CNF) : List Terms :=
  (List.range m).map (rawBterms p E ℓ w) ++ ψ.map (rawClauseTerms p E ℓ w)

/-- `t` coefficient samples. -/
def coeffs (p B t : ℕ) (bits : List Bool) : List ℕ := (List.range t).map (sampleMod p B bits)

/-- The normalized sparse polynomial `H`. -/
def buildH (p E : ℕ) (ℓ : List ℕ) (w m : ℕ) (ψ : CNF) (B : ℕ) (bits : List Bool) : Terms :=
  normalize p (RootData.Hterms p (coeffs p B (m + ψ.length) bits) (rawConstraintTerms p E ℓ w m ψ))

/-! ### The degree oracle interface -/

/-- **Degree oracle**: on `pair (unaryN c) (pair z r)` it decides, with error at most `2^{-c}`
over a random `r`, whether the sparse gcd of the instance `z = inst p R H` has positive degree —
but only for the instances produced by the reduction on the successful compression event, with at
most one satisfying assignment. `inst` builds the instance string from `(p, R, H)`. -/
structure DegreeOracle where
  inst : ℕ → Terms → Terms → List Bool
  /-- String-level instance builder: `instStr (encDivInstance p R H) = inst p R H`. -/
  instStr : List Bool → List Bool
  O : List Bool → List Bool
  σ : Polynomial ℕ
  O_mem_FP : O ∈ FP
  instStr_mem_FP : instStr ∈ FP
  instStr_eq : ∀ p R H, instStr (encDivInstance p R H) = inst p R H
  inst_length_le : ∀ p R H, (inst p R H).length ≤ 4 * (encDivInstance p R H).length + 4
  O_prefix : ∀ c z r, O (pair (unaryN c) (pair z r)) =
    O (pair (unaryN c) (pair z (r.take (σ.eval (c + z.length)))))
  correct : ∀ (c : ℕ) (d : RootData) (ψ : CNF) (us : List ℕ), CNF.VarsLt ψ d.m → BoundedClauses ψ →
    (solutions ψ d.m).card ≤ 1 →
    d.commonZeros [toPoly d.p (RootData.Hterms d.p us (d.constraintTerms ψ))] =
      d.commonZeros (d.constraintPolys ψ) →
    1 - 1 / (2 : ℚ) ^ c ≤ eventProb (univ.filter fun r : BitString
      (σ.eval (c + (inst d.p (rawRterms d.p d.E)
        (normalize d.p (RootData.Hterms d.p us (d.constraintTerms ψ)))).length)) ↦
      (O (pair (unaryN c) (pair (inst d.p (rawRterms d.p d.E)
          (normalize d.p (RootData.Hterms d.p us (d.constraintTerms ψ)))) (List.ofFn r))) = [true] ↔
        0 < (monicGcd d.R (toPoly d.p (normalize d.p
          (RootData.Hterms d.p us (d.constraintTerms ψ))))).natDegree))

/-! ### Parameters of the reduction, as functions of `s = |x|` -/

/-- The isolation polynomial `A(s) = 16 (s + 4)`. -/
def A (s : ℕ) : ℕ := 16 * (s + 4)

/-- Number of trials `r = 8 A(s)`. -/
def r (s : ℕ) : ℕ := 8 * A s

/-- Bit count with `2^cnt > 400 r`: dummy primes and oracle amplification. -/
def cnt (s : ℕ) : ℕ := Nat.size (400 * r s)

/-- Bound on the number of variables of the isolated formula. -/
def Vmax (s : ℕ) : ℕ := (s + 1) + s + (s + 3) * (s + 1)

/-- Bound on the number of clauses of the isolated formula. -/
def Kmax (s : ℕ) : ℕ := 3 * s + s + (s + 3) * (4 * (s + 1) + 1)

/-- Number of primes requested from the construction. -/
def Nn (s : ℕ) : ℕ := Vmax s + cnt s + 4

/-- Package attempts. -/
def tp : ℕ := 4

/-- ω attempts. -/
def ta (s : ℕ) : ℕ := 36 * (Vmax s + 1)

/-- Number of coefficient blocks. -/
def Tmax (s : ℕ) : ℕ := Vmax s + Kmax s

/-- `k`-bit and hash-bit block lengths (for the largest possible `m₀ = s + 1`). -/
def KB (s : ℕ) : ℕ := kBits (s + 1)
def HB (s : ℕ) : ℕ := hashBits (s + 1)

namespace PrimeConstruction

variable (C : PrimeConstruction)

/-- Seed length per package attempt. -/
def Lp (s : ℕ) : ℕ := C.seedLen.eval (Nn s)

/-- Bits per field sample (`≥ bitLength p + 1`). -/
def Bb (s : ℕ) : ℕ := C.bitBound.eval (Nn s) + 1

/-- Block offsets. -/
def o2 (_C : PrimeConstruction) (s : ℕ) : ℕ := KB s + HB s
def o3 (s : ℕ) : ℕ := C.o2 s + tp * C.Lp s
def o4 (s : ℕ) : ℕ := C.o3 s + ta s * C.Bb s
def o5 (s : ℕ) : ℕ := C.o4 s + Tmax s * C.Bb s

/-- A bound on the instance string length. -/
def Zmax (s : ℕ) : ℕ :=
  4 * (2 * C.Bb s + 2 + (2 * (8 * (C.Bb s + 4)) + 2 + (3 * Vmax s + 8 * Kmax s) * (8 * (C.Bb s + 4)))) + 4

end PrimeConstruction

namespace DegreeOracle

variable (Or : DegreeOracle) (C : PrimeConstruction)

/-- Oracle seed block length. -/
def σOr (s : ℕ) : ℕ := Or.σ.eval (cnt s + C.Zmax s)

/-- Length of one trial's seed. -/
def L (s : ℕ) : ℕ := C.o5 s + Or.σOr C s

/-- **One trial.** -/
def trialData (s : ℕ) (φ : CNF) (seed : List Bool) : Bool :=
  let m₀ := φ.maxVar + 1
  let kb := block seed 0 (kBits m₀)
  let hb := block seed (KB s) (hashBits m₀)
  let ψn := isolateSeed φ kb hb
  match C.firstPackage (Nn s) tp (C.Lp s) (block seed (C.o2 s) (tp * C.Lp s)) with
  | none => false
  | some (ℓ, c) =>
    let p := 1 + c * ℓ.prod
    let ℓm := ℓ.take ψn.2
    let E := ℓm.prod
    match findOmega p E ℓm (ta s) (C.Bb s) (block seed (C.o3 s) (ta s * C.Bb s)) with
    | none => false
    | some w =>
      let H := buildH p E ℓm w ψn.2 ψn.1 (C.Bb s) (block seed (C.o4 s) (Tmax s * C.Bb s))
      decide (Or.O (pair (unaryN (cnt s)) (pair (Or.inst p (rawRterms p E) H)
        (block seed (C.o5 s) (Or.σOr C s)))) = [true])

/-- **The verdict**: parse, then OR over `r s` trials. -/
def verdictData (x seed : List Bool) : Bool :=
  match CNF.decode? x with
  | none => false
  | some φ => (List.range (r x.length)).any fun i ↦
      Or.trialData C x.length φ (block seed (i * Or.L C x.length) (Or.L C x.length))

end DegreeOracle

/-! ### Statements of the analysis (proved in `Machine/Analysis.lean`) -/

end SparseGcd
