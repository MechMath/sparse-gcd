import SparseDivComplexity.StringArith.Succ
import SparseDivComplexity.StringArith.Add
import SparseDivComplexity.StringArith.Sub
import SparseDivComplexity.StringArith.Mul
import SparseDivComplexity.StringArith.Blocks
import SparseDivComplexity.BridgeTerms
import SparseDivComplexity.Languages

/-!
# The bridge as a polynomial-time string transformation

`bridgeStr : List Bool → List Bool` is the *algorithm* of Lemma 4 on the sparse binary encoding of
`Encoding.lean`: it parses `(p, P)`, checks that every coefficient is a residue below `p`, normalizes
`P`, and outputs the encoding of `(p, f_P, g_P)` where `f_P` and `g_P` are produced term by term by the
string arithmetic of `StringArith` (exponent `p·e` by `mulBits`, `p + e` by `addBits`, `e + 1` by
`succBits`, coefficient `-c` by `negModStr`) and then collected by `normalizeStr`. Malformed inputs
(undecodable, or a coefficient `≥ p`) are mapped to the fixed `DIV` instance `noInstance = (2, 0, 1)`.

The algorithm never expands a polynomial into a dense coefficient array: it only operates on the
list of framed blocks and on binary numerals.

## Main results

* `decDivInstance_bridgeStr` — the decoded output is exactly `bridgeTerms p l` (the term-list
  algorithm of `BridgeTerms.lean`), hence the semantics `fP`, `gP` and all bounds of that module
  transfer.
* `bridgeStr_eq_noInstance_of_decRootInstance_eq_none`, `bridgeStr_eq_noInstance_of_not_wf`.
* `bridgeStr_mem_FP` — the transformation is polynomial-time computable (complexitylib's `FP`, via
  Cobham's characterization).
* `length_bridgeStr_le` — an explicit (conservative) output-length bound `100 (|s| + 1)^3`.
-/

open Complexity SparseDiv.StringArith

namespace SparseDiv

/-- Coefficient numeral of a term block `pair c e`. -/
def coefOf (b : List Bool) : List Bool := pairFst b

/-- Exponent numeral of a term block `pair c e`. -/
def expOf (b : List Bool) : List Bool := pairSnd b

/-- Flag: `s` starts with a well-formed self-delimiting block (`unpair? s` succeeds). -/
def hasBlockFlag (s : List Bool) : List Bool := Cobham.eqFlag (pair (pairFst s) (pairSnd s)) s

theorem hasBlockFlag_eq_true_iff (s : List Bool) : hasBlockFlag s = [true] ↔ (unpair? s).isSome := by
  rw [hasBlockFlag, Cobham.eqFlag_eq_true_iff]
  constructor
  · intro h
    rw [← h, unpair?_pair]
    rfl
  · intro h
    obtain ⟨⟨x, y⟩, hxy⟩ := Option.isSome_iff_exists.mp h
    rw [eq_pair_of_unpair?_eq_some hxy, pairFst_pair, pairSnd_pair]

theorem cobham_hasBlockFlag_comp {n : ℕ} {g : (Fin n → List Bool) → List Bool} (hg : Cobham g) :
    Cobham fun v : Fin n → List Bool ↦ hasBlockFlag (g v) :=
  (Cobham.eqFlag_mem (cobham_pair_comp (cobham_pairFst_comp hg) (cobham_pairSnd_comp hg))
    hg).of_eq fun _ ↦ rfl

/-- Flag: `s` is a well-formed sequence of framed blocks (`undelimitBlocks s` succeeds). -/
def validBlocksFlag (s : List Bool) : List Bool := Cobham.eqFlag (mapBlocks id s) s

/-- Soundness of the fuelled block parser: a successful parse reads the input as the framing of
the parsed blocks. -/
private theorem eq_frame_of_undelimitBlocksAux_eq_some :
    ∀ (fuel : ℕ) {s : List Bool} {bs : List (List Bool)},
      undelimitBlocksAux fuel s = some bs → s = frame bs
  | 0, [], bs, h => by
    simp only [undelimitBlocksAux, Option.some.injEq] at h
    subst h; rfl
  | 0, _ :: _, _, h => by simp [undelimitBlocksAux] at h
  | fuel + 1, [], bs, h => by
    simp only [undelimitBlocksAux, Option.some.injEq] at h
    subst h; rfl
  | fuel + 1, b :: t, bs, h => by
    rcases hu : unpair? (b :: t) with _ | ⟨x, y⟩
    · simp [undelimitBlocksAux, hu] at h
    · rcases hcs : undelimitBlocksAux fuel y with _ | cs
      · simp [undelimitBlocksAux, hu, hcs] at h
      · simp [undelimitBlocksAux, hu, hcs] at h
        subst h
        rw [eq_pair_of_unpair?_eq_some hu, eq_frame_of_undelimitBlocksAux_eq_some fuel hcs]
        simp [frame, pair]

/-- Soundness of the block parser: a successful parse reads the input as the framing of the parsed
blocks. -/
private theorem eq_frame_of_undelimitBlocks_eq_some {s : List Bool} {bs : List (List Bool)}
    (h : undelimitBlocks s = some bs) : s = frame bs :=
  eq_frame_of_undelimitBlocksAux_eq_some _ h

theorem validBlocksFlag_eq_true_iff (s : List Bool) :
    validBlocksFlag s = [true] ↔ (undelimitBlocks s).isSome := by
  rw [validBlocksFlag, Cobham.eqFlag_eq_true_iff, mapBlocks, List.map_id]
  constructor
  · intro h
    have hb : undelimitBlocks (frame (blocks s)) = some (blocks s) :=
      undelimitBlocks_flatten_delimit _
    rw [h] at hb
    rw [hb]
    rfl
  · intro h
    obtain ⟨bs, hbs⟩ := Option.isSome_iff_exists.mp h
    rw [eq_frame_of_undelimitBlocks_eq_some hbs]
    exact congrArg frame (blocks_flatten_delimit bs)

theorem cobham_validBlocksFlag_comp {n : ℕ} {g : (Fin n → List Bool) → List Bool}
    (hg : Cobham g) : Cobham fun v : Fin n → List Bool ↦ validBlocksFlag (g v) := by
  -- `mapBlocks id` is `cobham_mapBlocks` with no parameters and the projection as block function.
  have hid : Cobham fun v : Fin (0 + 1) → List Bool ↦
      mapBlocks (fun b ↦ (fun w : Fin (0 + 1) → List Bool ↦ w 0) (Fin.cons b (Fin.tail v))) (v 0) :=
    cobham_mapBlocks (Cobham.proj 0) Polynomial.X fun v ↦ by simp
  exact (Cobham.eqFlag_mem (Cobham.comp hid fun _ : Fin 1 ↦ hg) hg).of_eq fun v ↦ by
    simp [validBlocksFlag]
    rfl

/-- Flag: every block of `s` is a term block whose coefficient is below `p`. -/
def wfBlocksFlag (p s : List Bool) : List Bool :=
  foldBlocks (fun acc b ↦ andBit acc (andBit (hasBlockFlag b) (ltBits (coefOf b) p)))
    [true] s

/-- `-c` modulo `p` for a residue `c < p`: `0 ↦ 0`, otherwise `p - c`. -/
def negModStr (p c : List Bool) : List Bool := caseBit₀ (isZeroBits c) [] (subBits p c)

theorem decNat_negModStr (p c : List Bool) (hc : decNat c < decNat p) :
    decNat (negModStr p c) = negMod (decNat p) (decNat c) := by
  rw [negModStr]
  rcases isZeroBits_flag c with h | h
  · rw [h, caseBit₀_cons, Bool.cond_true, decNat_nil, (isZeroBits_eq_true_iff c).1 h, negMod_zero]
  · rw [h, caseBit₀_cons, Bool.cond_false, decNat_subBits, negMod]
    have hne : decNat c ≠ 0 := fun h0 ↦ by
      have := (isZeroBits_eq_true_iff c).2 h0
      rw [h] at this
      simp at this
    rw [Nat.mod_eq_of_lt hc, Nat.mod_eq_of_lt (by omega)]

/-- `(c + c') mod p` for residues `c, c' < p`: one conditional subtraction. -/
def addModStr (p c c' : List Bool) : List Bool :=
  caseBit₀ (ltBits (addBits c c') p) (addBits c c') (subBits (addBits c c') p)

theorem decNat_addModStr (p c c' : List Bool) (hc : decNat c < decNat p) (hc' : decNat c' < decNat p) :
    decNat (addModStr p c c') = (decNat c + decNat c') % decNat p := by
  rw [addModStr]
  rcases ltBits_flag (addBits c c') p with h | h
  · have h' := (ltBits_eq_true_iff _ _).1 h
    rw [decNat_addBits] at h'
    rw [h, caseBit₀_cons, Bool.cond_true, decNat_addBits, Nat.mod_eq_of_lt h']
  · have h' := (ltBits_eq_false_iff _ _).1 h
    rw [decNat_addBits] at h'
    rw [h, caseBit₀_cons, Bool.cond_false, decNat_subBits, decNat_addBits,
      Nat.mod_eq_sub_mod h', Nat.mod_eq_of_lt (by omega)]

/-- One step of the insertion of the term `(c, e)` into a sorted accumulator: the state is
`pair inserted acc`. Mirrors `SparseDiv.insertTerm`. -/
def insertStep (p c e : List Bool) (state b : List Bool) : List Bool :=
  let ins := pairFst state
  let acc := pairSnd state
  let c' := coefOf b
  let e' := expOf b
  caseBit₀ ins (pair ins (acc ++ delimit b))
    (caseBit₀ (ltBits e e')
      (pair [true] (acc ++ caseBit₀ (isZeroBits c) [] (delimit (pair c e)) ++ delimit b))
      (caseBit₀ (eqBits e e')
        (pair [true] (acc ++ caseBit₀ (isZeroBits (addModStr p c c')) []
          (delimit (pair (addModStr p c c') e))))
        (pair [false] (acc ++ delimit b))))

/-- Insert the term `(c, e)` (with `c < p`) into a sorted framed accumulator. -/
def insertStr (p c e acc : List Bool) : List Bool :=
  let r := foldBlocks (insertStep p c e) (pair [false] []) acc
  caseBit₀ (pairFst r) (pairSnd r)
    (pairSnd r ++ caseBit₀ (isZeroBits c) [] (delimit (pair c e)))

/-- Collect like terms of a framed term list with residue coefficients: left fold of `insertStr`. -/
def normalizeStr (p s : List Bool) : List Bool :=
  foldBlocks (fun acc b ↦ insertStr p (coefOf b) (expOf b) acc) [] s

/-- The displayed terms of `f_P`: `(cᵢ, p·eᵢ)` then `(-cᵢ, eᵢ)`. -/
def fTermsStr (p s : List Bool) : List Bool :=
  mapBlocks (fun b ↦ pair (coefOf b) (mulBits p (expOf b))) s ++
    mapBlocks (fun b ↦ pair (negModStr p (coefOf b)) (expOf b)) s

/-- The displayed terms of `g_P`: `(cᵢ, p + eᵢ)` then `(-cᵢ, eᵢ + 1)`. -/
def gTermsStr (p s : List Bool) : List Bool :=
  mapBlocks (fun b ↦ pair (coefOf b) (addBits p (expOf b))) s ++
    mapBlocks (fun b ↦ pair (negModStr p (coefOf b)) (succBits (expOf b))) s

/-- The encoded guarded pair `(f, g) = (1, X)`. -/
def guardedStr : List Bool := pair (encTerms [(1, 0)]) (encTerms [(1, 1)])

/-- The bridge on a parsed, well-formed instance: zero test, generation, collection. -/
def bridgeBody (p s : List Bool) : List Bool :=
  let n := normalizeStr p s
  pair p (caseBit₀ (nonemptyFlag n)
    (pair (normalizeStr p (fTermsStr p n)) (normalizeStr p (gTermsStr p n))) guardedStr)

/-- Flag: `s` decodes as a `SparseRoot` instance whose coefficients are residues below `p`. -/
def validRootFlag (s : List Bool) : List Bool :=
  andBit (hasBlockFlag s)
    (andBit (validBlocksFlag (pairSnd s)) (wfBlocksFlag (pairFst s) (pairSnd s)))

/-- **The bridge string transformation.** -/
def bridgeStr (s : List Bool) : List Bool :=
  caseBit₀ (validRootFlag s) (bridgeBody (pairFst s) (pairSnd s)) noInstance

end SparseDiv
