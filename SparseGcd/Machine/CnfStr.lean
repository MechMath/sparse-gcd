import SparseGcd.Machine.TrialData
import SparseDivComplexity.StringArith.Blocks
import SparseDivComplexity.BridgeString.Complexity

/-!
# CNF formulas as strings (Cobham layer)

Internal encoding with *unary* variable indices (matching complexitylib's unary encoding of
literals):

* `encLitU l = pair [l.sign] (unaryN l.var)`;
* `encClauseU c = frame (c.map encLitU)`;
* `encCNFU φ = frame (φ.map encClauseU)`.

`parseCnfStr` converts complexitylib's encoding `SAT.CNF.encode φ` (doubled bits with separators
`01` after each literal and `10` after each clause) into the internal one and rejects every string
that is not an encoding. `isolateStr` implements `isolateSeed` (Cnf/Reduce.lean) on the internal
encoding, returning `pair (encCNFU ψ) (unaryN n')`.

Every string function is a plain definition on `List Bool` (so that correctness is proved by
`simp`/induction against the data-level definitions), and its membership in Cobham's algebra is
proved separately. Loops are `foldBlocks` over framed blocks (with the accumulator shape
`pair out ctr`, see `accStep`) or clocked iterations (`Cobham.iterFn`); the length side conditions
are discharged by explicit bounds valid for *all* inputs.
-/

open Complexity SAT SparseDiv SparseDiv.StringArith

namespace SparseGcd

def encLitU (l : Lit) : List Bool := pair [l.sign] (unaryN l.var)
def encClauseU (c : Clause) : List Bool := frame (c.map encLitU)
def encCNFU (φ : CNF) : List Bool := frame (φ.map encClauseU)

/-! ### Elementary facts about the encodings -/

theorem encClauseU_nil : encClauseU [] = [] := rfl

theorem encClauseU_cons (l : Lit) (c : Clause) :
    encClauseU (l :: c) = delimit (encLitU l) ++ encClauseU c := by
  simp [encClauseU, frame_cons]

theorem encClauseU_append (c d : Clause) : encClauseU (c ++ d) = encClauseU c ++ encClauseU d := by
  simp [encClauseU, frame_append]

theorem encCNFU_nil : encCNFU [] = [] := rfl

theorem encCNFU_cons (c : Clause) (φ : CNF) :
    encCNFU (c :: φ) = delimit (encClauseU c) ++ encCNFU φ := by
  simp [encCNFU, frame_cons]

theorem encCNFU_append (φ ψ : CNF) : encCNFU (φ ++ ψ) = encCNFU φ ++ encCNFU ψ := by
  simp [encCNFU, frame_append]

theorem encCNFU_singleton (c : Clause) : encCNFU [c] = delimit (encClauseU c) := by
  rw [encCNFU_cons, encCNFU_nil, List.append_nil]

theorem length_encClauseU_cons (l : Lit) (c : Clause) :
    (encClauseU (l :: c)).length = 2 * (encLitU l).length + 2 + (encClauseU c).length := by
  rw [encClauseU_cons, List.length_append, delimit_length]

theorem length_encLitU (l : Lit) : (encLitU l).length = l.var + 4 := by
  simp [encLitU, unaryN]
  omega

theorem length_le_length_encClauseU (c : Clause) : c.length ≤ (encClauseU c).length := by
  induction c with
  | nil => simp [encClauseU_nil]
  | cons l c ih =>
    rw [length_encClauseU_cons, List.length_cons]
    omega

theorem unaryN_zero : unaryN 0 = [] := rfl

theorem unaryN_succ (n : ℕ) : unaryN (n + 1) = true :: unaryN n := rfl

theorem unaryN_add (a b : ℕ) : unaryN (a + b) = unaryN a ++ unaryN b := List.replicate_add a b true

@[simp] theorem length_unaryN (n : ℕ) : (unaryN n).length = n := by simp [unaryN]

theorem unaryN_tail (n : ℕ) : (unaryN (n + 1)).tail = unaryN n := rfl

theorem unaryN_drop (a b : ℕ) : (unaryN (a + b)).drop a = unaryN b := by
  rw [unaryN_add]
  exact List.drop_left' (length_unaryN a)

theorem unaryN_take_of_le {a b : ℕ} (h : a ≤ b) : (unaryN a).take b = unaryN a :=
  List.take_of_length_le (by simp [h])

theorem unaryN_append_true (n : ℕ) : unaryN n ++ [true] = unaryN (n + 1) :=
  (List.replicate_succ' ..).symm

theorem delimit_eq_pair_nil (x : List Bool) : delimit x = pair x [] := by simp [pair]

/-- `pairFst` consumes two input bits per output bit. -/
theorem two_mul_length_pairFst_le : ∀ z : List Bool, 2 * (pairFst z).length ≤ z.length
  | [] => by simp [pairFst]
  | [b] => by cases b <;> simp [pairFst]
  | false :: false :: z => by
    have := two_mul_length_pairFst_le z
    simp [pairFst]
    omega
  | true :: true :: z => by
    have := two_mul_length_pairFst_le z
    simp [pairFst]
    omega
  | false :: true :: z => by simp [pairFst]
  | true :: false :: z => by simp [pairFst]

theorem length_pairFst_le (z : List Bool) : (pairFst z).length ≤ z.length := by
  have := two_mul_length_pairFst_le z
  omega

theorem length_pairSnd_le (z : List Bool) : (pairSnd z).length ≤ z.length := pairSnd_length_le z

/-- `frame (blocks s)` is a prefix of `s`. -/
theorem length_frame_blocks_le (s : List Bool) : (frame (blocks s)).length ≤ s.length := by
  obtain ⟨bs, rem, rfl, hrem⟩ := exists_frame_append s
  rcases hrem with rfl | hbad
  · simp [blocks_frame]
  · by_cases hne : rem = []
    · subst hne; simp [blocks_frame]
    · rw [blocks_frame_append_of_bad bs hne hbad, frame_nil]
      simp

theorem two_mul_length_add_two_le_of_mem_blocks {b s : List Bool} (h : b ∈ blocks s) :
    2 * b.length + 2 ≤ s.length :=
  le_trans (two_mul_length_add_two_le_of_mem_frame h) (length_frame_blocks_le s)

theorem length_frame_cons (b : List Bool) (bs : List (List Bool)) :
    (frame (b :: bs)).length = 2 * b.length + 2 + (frame bs).length := by
  rw [frame_cons, List.length_append, delimit_length]

/-! ### Cobham helpers -/

theorem cobham_delimit_comp {n : ℕ} {g : (Fin n → List Bool) → List Bool} (hg : Cobham g) :
    Cobham fun v : Fin n → List Bool ↦ delimit (g v) :=
  (cobham_pair_comp hg (Cobham.const [])).of_eq fun _ ↦ by simp [pair]

theorem cobham_smash_comp {n : ℕ} {g₀ g₁ : (Fin n → List Bool) → List Bool}
    (h₀ : Cobham g₀) (h₁ : Cobham g₁) :
    Cobham fun v : Fin n → List Bool ↦ Complexity.smash (g₀ v) (g₁ v) :=
  (Cobham.comp₂ Cobham.smash h₀ h₁).of_eq fun _ ↦ by simp

/-- Reindexing a `Fin 1`-ary member of the class along a member of the class. -/
theorem cobham_comp₁ {n : ℕ} {f : (Fin 1 → List Bool) → List Bool} (hf : Cobham f)
    {g : (Fin n → List Bool) → List Bool} (hg : Cobham g) :
    Cobham fun v : Fin n → List Bool ↦ f fun _ ↦ g v :=
  (Cobham.comp hf fun _ : Fin 1 ↦ hg).of_eq fun _ ↦ rfl

/-! ### The parser

The state is `parseState rem cur cl acc = pair rem (pair cur (pair cl acc))`: the unread input,
the raw bits of the current literal (in order), the framed literals of the current clause and the
framed clauses read so far. Malformed input moves to the fixed point `parseBad = [false]`. -/

def parseState (rem cur cl acc : List Bool) : List Bool := pair rem (pair cur (pair cl acc))

def parseBad : List Bool := [false]

/-- One token (two bits) of the parser. -/
def parseStep (st : List Bool) : List Bool :=
  let rem := pairFst st
  let cur := pairFst (pairSnd st)
  let cl := pairFst (pairSnd (pairSnd st))
  let acc := pairSnd (pairSnd (pairSnd st))
  let f0 := bitAt [] rem
  let f1 := bitAt [] rem.tail
  let rest := rem.tail.tail
  let data := caseBit₀ (nonemptyFlag cur)
    (caseBit₀ f0 (parseState rest (cur ++ [true]) cl acc) parseBad)
    (parseState rest f0 cl acc)
  let litSep := caseBit₀ (nonemptyFlag cur)
    (parseState rest [] (cl ++ delimit (pair (bitAt [] cur) cur.tail)) acc) parseBad
  let clSep := caseBit₀ (nonemptyFlag cur) parseBad (parseState rest [] [] (acc ++ delimit cl))
  caseBit₀ (nonemptyFlag rem)
    (caseBit₀ (nonemptyFlag rem.tail)
      (caseBit₀ f0 (caseBit₀ f1 data clSep) (caseBit₀ f1 litSep data))
      parseBad)
    (caseBit₀ (orBit (nonemptyFlag cur) (nonemptyFlag cl)) parseBad st)

/-- Read the answer off the final state. -/
def parseFinish (st : List Bool) : List Bool :=
  let acc := pairSnd (pairSnd (pairSnd st))
  caseBit₀ (Cobham.eqFlag st (parseState [] [] [] acc)) (pair [true] acc) [false]

/-- The parser: `pair [true] (encCNFU φ)` on `CNF.encode φ`, `[false]` otherwise. -/
def parseCnfStr (x : List Bool) : List Bool :=
  parseFinish (parseStep^[x.length + 1] (parseState x [] [] []))

/-! #### The step equations -/

theorem parseStep_bad : parseStep parseBad = parseBad := by decide

theorem parseStep_nil_nil_nil (acc : List Bool) :
    parseStep (parseState [] [] [] acc) = parseState [] [] [] acc := by
  simp [parseStep, parseState, orBit]

theorem parseStep_nil_cur (b : Bool) (cur cl acc : List Bool) :
    parseStep (parseState [] (b :: cur) cl acc) = parseBad := by
  simp [parseStep, parseState, orBit]

theorem parseStep_nil_cl (b : Bool) (cl acc : List Bool) :
    parseStep (parseState [] [] (b :: cl) acc) = parseBad := by
  simp [parseStep, parseState, orBit]

theorem parseStep_single (b : Bool) (cur cl acc : List Bool) :
    parseStep (parseState [b] cur cl acc) = parseBad := by
  simp [parseStep, parseState]

theorem parseStep_data_nil (b : Bool) (rest cl acc : List Bool) :
    parseStep (parseState (b :: b :: rest) [] cl acc) = parseState rest [b] cl acc := by
  cases b <;> simp [parseStep, parseState, bitAt]

theorem parseStep_data_true (rest : List Bool) (c : Bool) (cs cl acc : List Bool) :
    parseStep (parseState (true :: true :: rest) (c :: cs) cl acc) =
      parseState rest (c :: cs ++ [true]) cl acc := by
  simp [parseStep, parseState, bitAt]

theorem parseStep_data_false (rest : List Bool) (c : Bool) (cs cl acc : List Bool) :
    parseStep (parseState (false :: false :: rest) (c :: cs) cl acc) = parseBad := by
  simp [parseStep, parseState, bitAt]

theorem parseStep_litSep_nil (rest cl acc : List Bool) :
    parseStep (parseState (false :: true :: rest) [] cl acc) = parseBad := by
  simp [parseStep, parseState, bitAt]

theorem parseStep_litSep_cons (rest : List Bool) (c : Bool) (cs cl acc : List Bool) :
    parseStep (parseState (false :: true :: rest) (c :: cs) cl acc) =
      parseState rest [] (cl ++ delimit (pair [c] cs)) acc := by
  cases c <;> simp [parseStep, parseState, bitAt]

theorem parseStep_clSep_nil (rest cl acc : List Bool) :
    parseStep (parseState (true :: false :: rest) [] cl acc) =
      parseState rest [] [] (acc ++ delimit cl) := by
  simp [parseStep, parseState, bitAt]

theorem parseStep_clSep_cons (rest : List Bool) (c : Bool) (cs cl acc : List Bool) :
    parseStep (parseState (true :: false :: rest) (c :: cs) cl acc) = parseBad := by
  simp [parseStep, parseState, bitAt]

/-! #### The data-level parser -/

/-- The parser as a structural recursion (two bits per step), returning the internal encoding. -/
def parseRec : List Bool → List Bool → List Bool → List Bool → Option (List Bool)
  | [], [], [], acc => some acc
  | [], [], _ :: _, _ => none
  | [], _ :: _, _, _ => none
  | [_], _, _, _ => none
  | true :: true :: rest, [], cl, acc => parseRec rest [true] cl acc
  | true :: true :: rest, c :: cs, cl, acc => parseRec rest (c :: cs ++ [true]) cl acc
  | false :: false :: rest, [], cl, acc => parseRec rest [false] cl acc
  | false :: false :: _, _ :: _, _, _ => none
  | false :: true :: _, [], _, _ => none
  | false :: true :: rest, c :: cs, cl, acc => parseRec rest [] (cl ++ delimit (pair [c] cs)) acc
  | true :: false :: rest, [], cl, acc => parseRec rest [] [] (acc ++ delimit cl)
  | true :: false :: _, _ :: _, _, _ => none

/-- One two-bit step of the loop agrees with `parseRec`. -/
theorem parseStep_two (b₀ b₁ : Bool) (rest cur cl acc : List Bool) :
    (∃ cur' cl' acc', parseStep (parseState (b₀ :: b₁ :: rest) cur cl acc) =
        parseState rest cur' cl' acc' ∧
        parseRec (b₀ :: b₁ :: rest) cur cl acc = parseRec rest cur' cl' acc') ∨
      (parseStep (parseState (b₀ :: b₁ :: rest) cur cl acc) = parseBad ∧
        parseRec (b₀ :: b₁ :: rest) cur cl acc = none) := by
  cases cur with
  | nil =>
    cases b₀ <;> cases b₁
    · exact Or.inl ⟨_, _, _, parseStep_data_nil false rest cl acc, by simp only [parseRec]⟩
    · exact Or.inr ⟨parseStep_litSep_nil rest cl acc, by simp only [parseRec]⟩
    · exact Or.inl ⟨_, _, _, parseStep_clSep_nil rest cl acc, by simp only [parseRec]⟩
    · exact Or.inl ⟨_, _, _, parseStep_data_nil true rest cl acc, by simp only [parseRec]⟩
  | cons c cs =>
    cases b₀ <;> cases b₁
    · exact Or.inr ⟨parseStep_data_false rest c cs cl acc, by simp only [parseRec]⟩
    · exact Or.inl ⟨_, _, _, parseStep_litSep_cons rest c cs cl acc, by simp only [parseRec]⟩
    · exact Or.inr ⟨parseStep_clSep_cons rest c cs cl acc, by simp only [parseRec]⟩
    · exact Or.inl ⟨_, _, _, parseStep_data_true rest c cs cl acc, by simp only [parseRec]⟩

/-- **The loop computes `parseRec`** once it has run for at least `|rem| + 1` steps. -/
theorem parseStep_iterate : ∀ (rem cur cl acc : List Bool) (k : ℕ), rem.length + 1 ≤ k →
    parseStep^[k] (parseState rem cur cl acc) =
      (parseRec rem cur cl acc).elim parseBad (parseState [] [] [])
  | [], cur, cl, acc, k, hk => by
    obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
    rw [Function.iterate_succ_apply]
    cases cur with
    | nil =>
      cases cl with
      | nil =>
        rw [parseStep_nil_nil_nil, Function.iterate_fixed (parseStep_nil_nil_nil acc)]
        rfl
      | cons b cl => rw [parseStep_nil_cl, Function.iterate_fixed parseStep_bad]; rfl
    | cons b cur => rw [parseStep_nil_cur, Function.iterate_fixed parseStep_bad]; rfl
  | [b], cur, cl, acc, k, hk => by
    obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
    rw [Function.iterate_succ_apply, parseStep_single, Function.iterate_fixed parseStep_bad]
    rfl
  | b₀ :: b₁ :: rest, cur, cl, acc, k, hk => by
    obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
    have hk' : rest.length + 1 ≤ k' := by simp at hk; omega
    rw [Function.iterate_succ_apply]
    rcases parseStep_two b₀ b₁ rest cur cl acc with ⟨cur', cl', acc', h1, h2⟩ | ⟨h1, h2⟩
    · rw [h1, h2]
      exact parseStep_iterate rest cur' cl' acc' k' hk'
    · rw [h1, h2, Function.iterate_fixed parseStep_bad]
      rfl

theorem parseFinish_state (out : List Bool) :
    parseFinish (parseState [] [] [] out) = pair [true] out := by
  simp [parseFinish, parseState, eqFlag_self]

theorem parseFinish_bad : parseFinish parseBad = [false] := by decide

theorem parseCnfStr_eq_parseRec (x : List Bool) :
    parseCnfStr x = (parseRec x [] [] []).elim [false] (pair [true]) := by
  unfold parseCnfStr
  rw [parseStep_iterate x [] [] [] (x.length + 1) le_rfl]
  cases parseRec x [] [] [] with
  | none => exact parseFinish_bad
  | some out => exact parseFinish_state out

/-! #### Completeness -/

theorem parseRec_doubleBits_replicate (v : ℕ) : ∀ (rest : List Bool) (s : Bool) (j : ℕ)
    (cl acc : List Bool),
    parseRec (doubleBits (List.replicate v true) ++ rest) (s :: List.replicate j true) cl acc =
      parseRec rest (s :: List.replicate (j + v) true) cl acc := by
  induction v with
  | zero => intro rest s j cl acc; simp
  | succ v ih =>
    intro rest s j cl acc
    rw [List.replicate_succ, doubleBits_cons, List.cons_append, List.cons_append]
    simp only [parseRec]
    rw [show s :: List.replicate j true ++ [true] = s :: List.replicate (j + 1) true by
      simp [List.replicate_succ'], ih, show j + 1 + v = j + (v + 1) by omega]

theorem parseRec_lit (l : Lit) (rest cl acc : List Bool) :
    parseRec (doubleBits l.encodeRaw ++ [false, true] ++ rest) [] cl acc =
      parseRec rest [] (cl ++ delimit (encLitU l)) acc := by
  obtain ⟨s, v⟩ := l
  have h1 : doubleBits (Lit.encodeRaw ⟨s, v⟩) ++ [false, true] ++ rest =
      s :: s :: (doubleBits (List.replicate v true) ++ ([false, true] ++ rest)) := by
    simp [Lit.encodeRaw, Unary.encode, doubleBits_cons]
  have h2 : parseRec (s :: s :: (doubleBits (List.replicate v true) ++ ([false, true] ++ rest)))
      [] cl acc = parseRec (doubleBits (List.replicate v true) ++ ([false, true] ++ rest))
        (s :: List.replicate 0 true) cl acc := by
    cases s <;> simp only [parseRec, List.replicate]
  rw [h1, h2, parseRec_doubleBits_replicate, Nat.zero_add]
  show parseRec (false :: true :: rest) _ _ _ = _
  simp [parseRec, encLitU, unaryN]

theorem parseRec_clause (c : Clause) : ∀ (rest cl acc : List Bool),
    parseRec (Clause.encode c ++ rest) [] cl acc = parseRec rest [] (cl ++ encClauseU c) acc := by
  induction c with
  | nil => intro rest cl acc; simp [encClauseU_nil]
  | cons l c ih =>
    intro rest cl acc
    rw [Clause.encode_cons, List.append_assoc, List.append_assoc, ← List.append_assoc (doubleBits _),
      parseRec_lit, ih, encClauseU_cons, List.append_assoc]

theorem parseRec_cnf (φ : CNF) : ∀ (rest acc : List Bool),
    parseRec (CNF.encode φ ++ rest) [] [] acc = parseRec rest [] [] (acc ++ encCNFU φ) := by
  induction φ with
  | nil => intro rest acc; simp [encCNFU_nil]
  | cons c φ ih =>
    intro rest acc
    rw [CNF.encode_cons, List.append_assoc, List.append_assoc, parseRec_clause, List.nil_append]
    simp only [List.cons_append, List.nil_append, parseRec]
    rw [ih, encCNFU_cons, List.append_assoc]

theorem parseRec_encode (φ : CNF) : parseRec (CNF.encode φ) [] [] [] = some (encCNFU φ) := by
  rw [← List.append_nil (CNF.encode φ), parseRec_cnf]
  simp [parseRec]

/-! #### Soundness -/

/-- The current-literal register is `[]` or a sign bit followed by a run of `true`s. -/
def RawLit (cur : List Bool) : Prop := cur = [] ∨ ∃ (s : Bool) (k : ℕ), cur = s :: List.replicate k true

theorem doubleBits_append_true (l : List Bool) : doubleBits (l ++ [true]) = doubleBits l ++ [true, true] := by
  simp [doubleBits, List.flatMap_append]

theorem Clause.encode_append' (c d : Clause) : Clause.encode (c ++ d) = Clause.encode c ++ Clause.encode d := by
  induction c with
  | nil => rfl
  | cons l c ih => rw [List.cons_append, Clause.encode_cons, Clause.encode_cons, ih]; simp [List.append_assoc]

theorem encClauseU_ne_nil (l : Lit) (c : Clause) : encClauseU (l :: c) ≠ [] := by
  intro h
  have := congrArg List.length h
  rw [length_encClauseU_cons] at this
  simp at this

theorem parseRec_sound : ∀ (rem cur : List Bool) (c₀ : Clause) (φ₀ : CNF) (out : List Bool),
    RawLit cur → parseRec rem cur (encClauseU c₀) (encCNFU φ₀) = some out →
    ∃ φ : CNF, out = encCNFU φ ∧
      CNF.encode φ = CNF.encode φ₀ ++ Clause.encode c₀ ++ doubleBits cur ++ rem
  | [], cur, c₀, φ₀, out, _, h => by
    cases cur with
    | nil =>
      cases c₀ with
      | nil =>
        simp only [encClauseU_nil, parseRec, Option.some.injEq] at h
        exact ⟨φ₀, h.symm, by simp⟩
      | cons l c =>
        obtain ⟨x, xs, hx⟩ := List.exists_cons_of_ne_nil (encClauseU_ne_nil l c)
        rw [hx] at h
        simp [parseRec] at h
    | cons b cur => simp [parseRec] at h
  | [b], cur, c₀, φ₀, out, _, h => by simp [parseRec] at h
  | b₀ :: b₁ :: rest, cur, c₀, φ₀, out, hcur, h => by
    rcases hcur with rfl | ⟨s, k, rfl⟩
    · cases b₀ <;> cases b₁ <;> simp only [parseRec] at h
      · obtain ⟨φ, hout, hφ⟩ := parseRec_sound rest [false] c₀ φ₀ out (Or.inr ⟨false, 0, rfl⟩) h
        exact ⟨φ, hout, by simpa using hφ⟩
      · simp at h
      · obtain ⟨φ, hout, hφ⟩ := parseRec_sound rest [] [] (φ₀ ++ [c₀]) out (Or.inl rfl)
          (by rw [encClauseU_nil, encCNFU_append, encCNFU_cons, encCNFU_nil, List.append_nil]; exact h)
        refine ⟨φ, hout, ?_⟩
        rw [hφ, CNF.encode_append, CNF.encode_cons, CNF.encode_nil]
        simp
      · obtain ⟨φ, hout, hφ⟩ := parseRec_sound rest [true] c₀ φ₀ out (Or.inr ⟨true, 0, rfl⟩) h
        exact ⟨φ, hout, by simpa using hφ⟩
    · cases b₀ <;> cases b₁ <;> simp only [parseRec] at h
      · simp at h
      · obtain ⟨φ, hout, hφ⟩ := parseRec_sound rest [] (c₀ ++ [⟨s, k⟩]) φ₀ out (Or.inl rfl)
          (by rw [encClauseU_append, encClauseU_cons, encClauseU_nil, List.append_nil]; exact h)
        refine ⟨φ, hout, ?_⟩
        rw [hφ, Clause.encode_append', Clause.encode_cons, Clause.encode_nil]
        simp [Lit.encodeRaw, Unary.encode]
      · simp at h
      · obtain ⟨φ, hout, hφ⟩ := parseRec_sound rest (s :: List.replicate (k + 1) true) c₀ φ₀ out
          (Or.inr ⟨s, k + 1, rfl⟩) (by rw [← h]; congr 2; simp [List.replicate_succ'])
        refine ⟨φ, hout, ?_⟩
        rw [hφ, List.replicate_succ', ← List.cons_append, doubleBits_append_true]
        simp

theorem parseCnfStr_encode (φ : CNF) : parseCnfStr (CNF.encode φ) = pair [true] (encCNFU φ) := by
  rw [parseCnfStr_eq_parseRec, parseRec_encode]
  rfl

theorem parseCnfStr_eq_false (x : List Bool) (h : CNF.decode? x = none) : parseCnfStr x = [false] := by
  rw [parseCnfStr_eq_parseRec]
  cases hp : parseRec x [] [] [] with
  | none => rfl
  | some out =>
    exfalso
    obtain ⟨φ, -, hφ⟩ := parseRec_sound x [] [] [] out (Or.inl rfl) hp
    simp only [CNF.encode_nil, Clause.encode_nil, doubleBits_nil, List.nil_append] at hφ
    rw [← hφ, CNF.decode?_encode] at h
    cases h

/-- The parser agrees with complexitylib's decoder. -/
theorem parseCnfStr_eq (x : List Bool) :
    parseCnfStr x = match CNF.decode? x with
      | some φ => pair [true] (encCNFU φ)
      | none => [false] := by
  cases hd : CNF.decode? x with
  | none => exact parseCnfStr_eq_false x hd
  | some φ =>
    obtain rfl := CNF.decode?_sound hd
    exact parseCnfStr_encode φ

/-! #### Complexity -/

theorem cobham_parseStep : Cobham fun v : Fin 1 → List Bool ↦ parseStep (v 0) := by
  have hst : Cobham fun v : Fin 1 → List Bool ↦ v 0 := Cobham.proj 0
  have hrem := cobham_pairFst_comp hst
  have hcur := cobham_pairFst_comp (cobham_pairSnd_comp hst)
  have hcl := cobham_pairFst_comp (cobham_pairSnd_comp (cobham_pairSnd_comp hst))
  have hacc := cobham_pairSnd_comp (cobham_pairSnd_comp (cobham_pairSnd_comp hst))
  have hf0 := Cobham.headFlagFn hrem
  have htl := Cobham.tailFn hrem
  have hf1 := Cobham.headFlagFn htl
  have hrest := Cobham.tailFn htl
  have hbad : Cobham fun _ : Fin 1 → List Bool ↦ parseBad := Cobham.const _
  have hne := Cobham.nonemptyFn hcur
  have hstate : ∀ {a b c d : (Fin 1 → List Bool) → List Bool}, Cobham a → Cobham b → Cobham c →
      Cobham d → Cobham fun v ↦ parseState (a v) (b v) (c v) (d v) :=
    fun ha hb hc hd ↦ cobham_pair_comp ha (cobham_pair_comp hb (cobham_pair_comp hc hd))
  have hdata := Cobham.iteFn hne
    (Cobham.iteFn hf0 (hstate hrest (Cobham.appendFn hcur (Cobham.const [true])) hcl hacc) hbad)
    (hstate hrest hf0 hcl hacc)
  have hlit := Cobham.iteFn hne
    (hstate hrest (Cobham.const []) (Cobham.appendFn hcl (cobham_delimit_comp
      (cobham_pair_comp (Cobham.headFlagFn hcur) (Cobham.tailFn hcur)))) hacc) hbad
  have hcls := Cobham.iteFn hne hbad
    (hstate hrest (Cobham.const []) (Cobham.const []) (Cobham.appendFn hacc (cobham_delimit_comp hcl)))
  exact (Cobham.iteFn (Cobham.nonemptyFn hrem)
    (Cobham.iteFn (Cobham.nonemptyFn htl)
      (Cobham.iteFn hf0 (Cobham.iteFn hf1 hdata hcls) (Cobham.iteFn hf1 hlit hdata)) hbad)
    (Cobham.iteFn (Cobham.orFn hne (Cobham.nonemptyFn hcl)) hbad hst)).of_eq fun _ ↦ rfl

theorem cobham_parseFinish_comp {n : ℕ} {g : (Fin n → List Bool) → List Bool} (hg : Cobham g) :
    Cobham fun v : Fin n → List Bool ↦ parseFinish (g v) := by
  have hacc := cobham_pairSnd_comp (cobham_pairSnd_comp (cobham_pairSnd_comp hg))
  exact (Cobham.iteFn (Cobham.eqFlag_mem hg (cobham_pair_comp (Cobham.const [])
    (cobham_pair_comp (Cobham.const []) (cobham_pair_comp (Cobham.const []) hacc))))
    (cobham_pair_comp (Cobham.const [true]) hacc) (Cobham.const [false])).of_eq fun _ ↦ rfl

/-- The potential `8|rem| + 4|cur| + 2|cl| + |acc|` does not increase along the loop. -/
theorem parseStep_state_cases (rem cur cl acc : List Bool) :
    parseStep (parseState rem cur cl acc) = parseBad ∨
      ∃ rem' cur' cl' acc', parseStep (parseState rem cur cl acc) = parseState rem' cur' cl' acc' ∧
        8 * rem'.length + 4 * cur'.length + 2 * cl'.length + acc'.length ≤
          8 * rem.length + 4 * cur.length + 2 * cl.length + acc.length := by
  match rem, cur with
  | [], [] =>
    cases cl with
    | nil => exact Or.inr ⟨_, _, _, _, parseStep_nil_nil_nil acc, le_rfl⟩
    | cons b cl => exact Or.inl (parseStep_nil_cl b cl acc)
  | [], b :: cur => exact Or.inl (parseStep_nil_cur b cur cl acc)
  | [b], cur => exact Or.inl (parseStep_single b cur cl acc)
  | b₀ :: b₁ :: rest, [] =>
    cases b₀ <;> cases b₁
    · exact Or.inr ⟨_, _, _, _, parseStep_data_nil false rest cl acc, by simp; omega⟩
    · exact Or.inl (parseStep_litSep_nil rest cl acc)
    · exact Or.inr ⟨_, _, _, _, parseStep_clSep_nil rest cl acc, by simp; omega⟩
    · exact Or.inr ⟨_, _, _, _, parseStep_data_nil true rest cl acc, by simp; omega⟩
  | b₀ :: b₁ :: rest, c :: cs =>
    cases b₀ <;> cases b₁
    · exact Or.inl (parseStep_data_false rest c cs cl acc)
    · exact Or.inr ⟨_, _, _, _, parseStep_litSep_cons rest c cs cl acc, by simp; omega⟩
    · exact Or.inl (parseStep_clSep_cons rest c cs cl acc)
    · exact Or.inr ⟨_, _, _, _, parseStep_data_true rest c cs cl acc, by simp; omega⟩

theorem parseStep_iterate_cases (rem cur cl acc : List Bool) (k : ℕ) :
    parseStep^[k] (parseState rem cur cl acc) = parseBad ∨
      ∃ rem' cur' cl' acc', parseStep^[k] (parseState rem cur cl acc) = parseState rem' cur' cl' acc' ∧
        8 * rem'.length + 4 * cur'.length + 2 * cl'.length + acc'.length ≤
          8 * rem.length + 4 * cur.length + 2 * cl.length + acc.length := by
  induction k with
  | zero => exact Or.inr ⟨rem, cur, cl, acc, rfl, le_rfl⟩
  | succ k ih =>
    rw [Function.iterate_succ_apply']
    rcases ih with h | ⟨rem', cur', cl', acc', h, hle⟩
    · rw [h, parseStep_bad]; exact Or.inl rfl
    · rw [h]
      rcases parseStep_state_cases rem' cur' cl' acc' with h' | ⟨r, c, l, a, h', hle'⟩
      · exact Or.inl h'
      · exact Or.inr ⟨r, c, l, a, h', le_trans hle' hle⟩

theorem length_parseState (rem cur cl acc : List Bool) :
    (parseState rem cur cl acc).length = 2 * rem.length + 2 * cur.length + 2 * cl.length + acc.length + 6 := by
  simp [parseState, pair_length]
  omega

theorem length_parseStep_iterate_le (x : List Bool) (k : ℕ) :
    (parseStep^[k] (parseState x [] [] [])).length ≤ 16 * x.length + 6 := by
  rcases parseStep_iterate_cases x [] [] [] k with h | ⟨rem', cur', cl', acc', h, hle⟩
  · rw [h]; simp [parseBad]
  · rw [h, length_parseState]
    simp at hle
    omega

theorem parseCnfStr_mem_FP : parseCnfStr ∈ FP := by
  rw [← CobhamFP_eq_FP]
  show Cobham fun v : Fin 1 → List Bool ↦ parseCnfStr (v 0)
  have he : Cobham fun v : Fin 1 → List Bool ↦ parseState (v 0) [] [] [] :=
    cobham_pair_comp (Cobham.proj 0) (Cobham.const _)
  have hf : Cobham fun w : Fin 2 → List Bool ↦ parseStep (w 0) :=
    (Cobham.comp cobham_parseStep fun _ : Fin 1 ↦ Cobham.proj 0).of_eq fun _ ↦ rfl
  have hj : Cobham fun w : Fin 2 → List Bool ↦
      List.replicate 6 false ++ (List.replicate 16 (w 1)).flatten :=
    Cobham.appendFn (Cobham.const _) (Cobham.repeatFn (Cobham.proj 1) 16)
  have hiter := Cobham.iterFn he hf hj (by
    intro c v
    show (parseStep^[c.length] (parseState (v 0) [] [] [])).length ≤
      (List.replicate 6 false ++ (List.replicate 16 (v 0)).flatten).length
    simp only [List.length_append, List.length_replicate, List.length_flatten, List.map_replicate,
      List.sum_replicate, smul_eq_mul]
    have := length_parseStep_iterate_le (v 0) c.length
    omega)
  have hloop := Cobham.comp hiter
    (gs := fun i (v : Fin 1 → List Bool) ↦ (Fin.cons (false :: v 0) v : Fin 2 → List Bool) i)
    (by
      intro i
      refine Fin.cases ?_ (fun i ↦ ?_) i
      · exact cobham_cons false (Cobham.proj 0)
      · exact Cobham.proj i)
  refine (cobham_parseFinish_comp hloop).of_eq fun v ↦ ?_
  simp only [parseCnfStr, Fin.tail_cons, Fin.cons_zero, List.length_cons]

/-! ### Number of variables -/

/-- The longer of two (unary) strings. -/
def maxU (a b : List Bool) : List Bool := caseBit₀ (Cobham.lenLeFlag a b) a b

theorem maxU_unaryN (x y : ℕ) : maxU (unaryN x) (unaryN y) = unaryN (max x y) := by
  unfold maxU
  rcases Cobham.lenLeFlag_flag (unaryN x) (unaryN y) with h | h
  · have := (Cobham.lenLeFlag_eq_true_iff _ _).mp h
    simp only [length_unaryN] at this
    rw [h, caseBit₀_cons, Bool.cond_true, max_eq_left this]
  · have hlt : x < y := by
      by_contra hle
      have := (Cobham.lenLeFlag_eq_true_iff (unaryN x) (unaryN y)).mpr (by simp; omega)
      rw [h] at this
      simp at this
    rw [h, caseBit₀_cons, Bool.cond_false, max_eq_right hlt.le]

theorem caseBit₀_length_le_max (s x y : List Bool) :
    (caseBit₀ s x y).length ≤ max x.length y.length := by
  cases s with
  | nil => simp
  | cons b s => cases b <;> simp

theorem length_maxU_le (a b : List Bool) : (maxU a b).length ≤ max a.length b.length :=
  caseBit₀_length_le_max _ _ _

theorem cobham_maxU_comp {n : ℕ} {g₀ g₁ : (Fin n → List Bool) → List Bool}
    (h₀ : Cobham g₀) (h₁ : Cobham g₁) :
    Cobham fun v : Fin n → List Bool ↦ maxU (g₀ v) (g₁ v) :=
  Cobham.iteFn (Cobham.lenLeFlag_mem h₀ h₁) h₀ h₁

/-- The largest variable of a clause (unary), from `encClauseU c`. -/
def clauseMaxU (c : List Bool) : List Bool := foldBlocks (fun acc b ↦ maxU acc (pairSnd b)) [] c

/-- `unaryN (φ.maxVar + 1)` from the internal encoding. -/
def numVarsStr (t : List Bool) : List Bool :=
  true :: foldBlocks (fun acc c ↦ maxU acc (clauseMaxU c)) [] t

theorem foldl_maxU_encLitU (c : Clause) : ∀ m : ℕ,
    (c.map encLitU).foldl (fun acc b ↦ maxU acc (pairSnd b)) (unaryN m) = unaryN (max m c.maxVar) := by
  induction c with
  | nil => intro m; simp
  | cons l c ih =>
    intro m
    rw [List.map_cons, List.foldl_cons, encLitU, pairSnd_pair, maxU_unaryN, ih, Clause.maxVar_cons,
      max_assoc]

theorem clauseMaxU_encClauseU (c : Clause) : clauseMaxU (encClauseU c) = unaryN c.maxVar := by
  rw [clauseMaxU, encClauseU, foldBlocks_frame, ← unaryN_zero, foldl_maxU_encLitU, Nat.zero_max]

theorem foldl_maxU_encClauseU (φ : CNF) : ∀ m : ℕ,
    (φ.map encClauseU).foldl (fun acc c ↦ maxU acc (clauseMaxU c)) (unaryN m) =
      unaryN (max m φ.maxVar) := by
  induction φ with
  | nil => intro m; simp
  | cons c φ ih =>
    intro m
    rw [List.map_cons, List.foldl_cons, clauseMaxU_encClauseU, maxU_unaryN, ih, CNF.maxVar_cons,
      max_assoc]

theorem numVarsStr_encCNFU (φ : CNF) : numVarsStr (encCNFU φ) = unaryN (φ.maxVar + 1) := by
  rw [numVarsStr, encCNFU, foldBlocks_frame, ← unaryN_zero, foldl_maxU_encClauseU, Nat.zero_max]
  rfl

theorem length_foldl_maxU_le (g : List Bool → List Bool) (N : ℕ) (hg : ∀ b, (g b).length ≤ b.length) :
    ∀ (bs : List (List Bool)) (acc : List Bool), (∀ b ∈ bs, b.length ≤ N) → acc.length ≤ N →
      (bs.foldl (fun acc b ↦ maxU acc (g b)) acc).length ≤ N
  | [], acc, _, hacc => hacc
  | b :: bs, acc, hbs, hacc => by
    rw [List.foldl_cons]
    refine length_foldl_maxU_le g N hg bs _ (fun b' hb' ↦ hbs b' (List.mem_cons_of_mem _ hb')) ?_
    have h1 := length_maxU_le acc (g b)
    have h2 := hg b
    have h3 := hbs b (List.mem_cons_self ..)
    omega

theorem length_clauseMaxU_le (c : List Bool) : (clauseMaxU c).length ≤ c.length := by
  refine length_foldl_maxU_le pairSnd c.length length_pairSnd_le (blocks c) [] ?_ (by simp)
  intro b hb
  have := two_mul_length_add_two_le_of_mem_blocks hb
  omega

theorem cobham_clauseMaxU : Cobham fun v : Fin 1 → List Bool ↦ clauseMaxU (v 0) := by
  have hstep : Cobham fun w : Fin 2 → List Bool ↦ maxU (w 0) (pairSnd (w 1)) :=
    cobham_maxU_comp (Cobham.proj 0) (cobham_pairSnd_comp (Cobham.proj 1))
  refine (cobham_foldBlocks hstep (init := fun _ ↦ []) Cobham.empty 1 ?_).of_eq fun v ↦ rfl
  intro w
  have h1 := length_maxU_le (w 0) (pairSnd (w 1))
  have h2 := length_pairSnd_le (w 1)
  omega

theorem numVarsStr_mem_FP : numVarsStr ∈ FP := by
  rw [← CobhamFP_eq_FP]
  show Cobham fun v : Fin 1 → List Bool ↦ numVarsStr (v 0)
  have hstep : Cobham fun w : Fin 2 → List Bool ↦ maxU (w 0) (clauseMaxU (w 1)) :=
    cobham_maxU_comp (Cobham.proj 0) (cobham_comp₁ cobham_clauseMaxU (Cobham.proj 1))
  have hfold := cobham_foldBlocks hstep (init := fun _ ↦ []) Cobham.empty 1 (by
    intro w
    have h1 := length_maxU_le (w 0) (clauseMaxU (w 1))
    have h2 := length_clauseMaxU_le (w 1)
    omega)
  exact (cobham_cons true hfold).of_eq fun v ↦ rfl

/-! ### The `k`-bit and hash-bit counts -/

theorem succBits_encNat (n : ℕ) : succBits (encNat n) = encNat (n + 1) := by
  induction n using Nat.binaryRec with
  | zero => simp [encNat, succBits]
  | bit b m ih =>
    cases b
    · rcases Nat.eq_zero_or_pos m with rfl | hm
      · simp [encNat, succBits]
      · simp only [Nat.bit_val, Bool.toNat_false, add_zero]
        rw [encNat, Nat.bit0_bits m hm.ne', succBits, encNat, Nat.bit1_bits]
    · simp only [Nat.bit_val, Bool.toNat_true]
      rw [encNat, Nat.bit1_bits, succBits, show 2 * m + 1 + 1 = 2 * (m + 1) by ring, encNat,
        Nat.bit0_bits (m + 1) (Nat.succ_ne_zero m)]
      rw [encNat] at ih
      rw [ih]
      rfl

theorem succBits_iterate_nil (n : ℕ) : succBits^[n] [] = encNat n := by
  induction n with
  | zero => simp [encNat]
  | succ n ih => rw [Function.iterate_succ_apply', ih, succBits_encNat]

theorem length_succBits_iterate_le (n : ℕ) : (succBits^[n] []).length ≤ n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Function.iterate_succ_apply']
    have := length_succBits_le (succBits^[n] [])
    omega

/-- The binary numeral of `|m| + 2`. -/
def binOfUnary2 (m : List Bool) : List Bool := succBits^[(true :: true :: m).length] []

/-- `encNat (Nat.size (m₀ + 2))`-many bits: the number of `k`-bits, as a unary string, from
`unaryN m₀`. -/
def kBitsStr (m : List Bool) : List Bool := Complexity.smash (binOfUnary2 m) [true]

theorem kBitsStr_unaryN (m₀ : ℕ) : kBitsStr (unaryN m₀) = unaryN (kBits m₀) := by
  have h : (true :: true :: unaryN m₀).length = m₀ + 2 := by simp
  rw [kBitsStr, binOfUnary2, h, succBits_iterate_nil, Complexity.smash, length_encNat, kBits]
  simp [unaryN]

theorem cobham_binOfUnary2 : Cobham fun v : Fin 1 → List Bool ↦ binOfUnary2 (v 0) := by
  have hiter := Cobham.iterFn (n := 0) (e := fun _ ↦ []) (f := fun w ↦ succBits (w 0))
    (j := fun w ↦ w 0) Cobham.empty cobham_succBits (Cobham.proj 0) (by
      intro c v
      show (succBits^[c.length] []).length ≤ c.length
      exact length_succBits_iterate_le _)
  exact (cobham_comp₁ hiter (cobham_cons true (cobham_cons true (Cobham.proj 0)))).of_eq
    fun v ↦ rfl

theorem kBitsStr_mem_FP : kBitsStr ∈ FP := by
  rw [← CobhamFP_eq_FP]
  exact cobham_smash_comp cobham_binOfUnary2 (Cobham.const [true])

/-- `unaryN (hashBits m₀)` from `unaryN m₀`. -/
def hashBitsStr (m : List Bool) : List Bool := Complexity.smash (true :: true :: m) (true :: m)

theorem hashBitsStr_unaryN (m₀ : ℕ) : hashBitsStr (unaryN m₀) = unaryN (hashBits m₀) := by
  simp [hashBitsStr, Complexity.smash, unaryN, hashBits]

theorem hashBitsStr_mem_FP : hashBitsStr ∈ FP := by
  rw [← CobhamFP_eq_FP]
  exact cobham_smash_comp (cobham_cons true (cobham_cons true (Cobham.proj 0)))
    (cobham_cons true (Cobham.proj 0))

/-! ### Folds with an accumulator `pair out ctr`

`accStep f h` is the step of a block fold whose accumulator is `pair out ctr`: the block `b`
appends `f ctr b` to the output `out` and replaces the control register `ctr` by `h ctr b`. -/

def accStep (f h : List Bool → List Bool → List Bool) (acc b : List Bool) : List Bool :=
  pair (pairFst acc ++ f (pairSnd acc) b) (h (pairSnd acc) b)

theorem accStep_pair (f h : List Bool → List Bool → List Bool) (out ctr b : List Bool) :
    accStep f h (pair out ctr) b = pair (out ++ f ctr b) (h ctr b) := by
  simp [accStep]

/-- Length bound for the whole fold: the control register grows by at most `2|b| + 2 + C` per
block `b` and every block output is at most `K` bits long. -/
theorem length_foldl_accStep_le (f h : List Bool → List Bool → List Bool) (B C K : ℕ)
    (hh : ∀ ctr b, (h ctr b).length ≤ ctr.length + 2 * b.length + 2 + C)
    (hf : ∀ ctr b, ctr.length ≤ B → b.length ≤ B → (f ctr b).length ≤ K) :
    ∀ (bs : List (List Bool)) (out ctr : List Bool),
      ctr.length + (frame bs).length + bs.length * C ≤ B →
      (bs.foldl (accStep f h) (pair out ctr)).length ≤ 2 * (out.length + bs.length * K) + 2 + B
  | [], out, ctr, hB => by
    simp only [List.foldl_nil, pair_length, frame_nil, List.length_nil, zero_mul, add_zero] at hB ⊢
    omega
  | b :: bs, out, ctr, hB => by
    rw [List.foldl_cons, accStep_pair, List.length_cons, add_mul, one_mul]
    rw [length_frame_cons, List.length_cons, add_mul, one_mul] at hB
    have h1 := length_foldl_accStep_le f h B C K hh hf bs (out ++ f ctr b) (h ctr b)
      (by have := hh ctr b; omega)
    have h2 := hf ctr b (by omega) (by omega)
    rw [List.length_append] at h1
    omega

/-- **Length bound for the whole trajectory of a block loop** from a bound on every fold over a
block list that fits in the input. -/
theorem blockStep_iterate_length_le' (g : List Bool → List Bool → List Bool) (bad : List Bool)
    (hfix : blockStep g bad bad = bad) (s acc₀ : List Bool) (N : ℕ)
    (hfold : ∀ bs : List (List Bool), (frame bs).length ≤ s.length → (bs.foldl g acc₀).length ≤ N)
    (hbad : bad.length ≤ 2 * s.length + 2 + N) (k : ℕ) :
    ((blockStep g bad)^[k] (pair s acc₀)).length ≤ 2 * s.length + 2 + N := by
  obtain ⟨bs, rem, hs, hrem⟩ := exists_frame_append s
  have hreg : ∀ j, (pair (frame (bs.drop j) ++ rem) ((bs.take j).foldl g acc₀)).length ≤
      2 * s.length + 2 + N := by
    intro j
    have hsplit : frame bs ++ rem = frame (bs.take j) ++ (frame (bs.drop j) ++ rem) := by
      rw [← List.append_assoc, ← frame_append, List.take_append_drop]
    have hlen : (frame (bs.drop j) ++ rem).length ≤ s.length := by
      rw [hs, hsplit]
      simp only [List.length_append]
      omega
    have htake : (frame (bs.take j)).length ≤ s.length := by
      rw [hs, hsplit]
      simp only [List.length_append]
      omega
    have hf := hfold _ htake
    rw [pair_length]
    omega
  by_cases hk : k ≤ bs.length ∨ rem = []
  · rcases hk with hk | hk
    · rw [blockStep_iterate_of_le g bad hs acc₀ hk]
      exact hreg k
    · rw [blockStep_iterate_of_nil g bad hs hk acc₀ k]
      exact hreg k
  · push Not at hk
    rw [blockStep_iterate_of_bad g bad hfix hs hk.2 (hrem.resolve_left hk.2) acc₀ hk.1]
    exact hbad

/-- Reindexing of the step arguments of `cobham_foldBlocks`: the block function receives the
control register, the block, then the parameters. -/
theorem cobham_ctrBlock {n : ℕ} {f : (Fin (n + 2) → List Bool) → List Bool} (hf : Cobham f) :
    Cobham fun x : Fin (n + 2) → List Bool ↦
      f (Fin.cons (pairSnd (x 0)) (Fin.cons (x 1) (Fin.tail (Fin.tail x)))) := by
  refine (Cobham.comp hf
    (gs := fun i (x : Fin (n + 2) → List Bool) ↦
      (Fin.cons (pairSnd (x 0)) (Fin.cons (x 1) (Fin.tail (Fin.tail x))) :
        Fin (n + 2) → List Bool) i) ?_).of_eq fun x ↦ rfl
  intro i
  refine Fin.cases ?_ (fun i ↦ Fin.cases ?_ (fun i ↦ ?_) i) i
  · exact cobham_pairSnd_comp (Cobham.proj 0)
  · exact Cobham.proj 1
  · exact Cobham.proj i.succ.succ

/-- **Accumulator folds are in Cobham's algebra.** The block functions `f`, `h` receive the control
register, the block, then the parameters `Fin.tail v`; `q` bounds the initial registers, `D` the
extra growth of the control register per block (both in the parameters), and `K` the block output
(in all arguments); all bounds are polynomial. -/
theorem cobham_foldAcc {n : ℕ} {f h : (Fin (n + 2) → List Bool) → List Bool}
    (hf : Cobham f) (hh : Cobham h)
    {out₀ ctr₀ : (Fin n → List Bool) → List Bool} (hout : Cobham out₀) (hctr : Cobham ctr₀)
    (q D K : Polynomial ℕ)
    (hout_le : ∀ p, (out₀ p).length ≤ q.eval (∑ i, (p i).length))
    (hctr_le : ∀ p, (ctr₀ p).length ≤ q.eval (∑ i, (p i).length))
    (hh_le : ∀ w, (h w).length ≤ (w 0).length + 2 * (w 1).length + 2 +
      D.eval (∑ i, (Fin.tail (Fin.tail w) i).length))
    (hf_le : ∀ w, (f w).length ≤ K.eval (∑ i, (w i).length)) :
    Cobham fun v : Fin (n + 1) → List Bool ↦
      foldBlocks (accStep (fun c b ↦ f (Fin.cons c (Fin.cons b (Fin.tail v))))
        (fun c b ↦ h (Fin.cons c (Fin.cons b (Fin.tail v)))))
        (pair (out₀ (Fin.tail v)) (ctr₀ (Fin.tail v))) (v 0) := by
  -- The step on `(acc, b, params)`.
  have hstep : Cobham fun w : Fin (n + 2) → List Bool ↦
      accStep (fun c b ↦ f (Fin.cons c (Fin.cons b (Fin.tail (Fin.tail w)))))
        (fun c b ↦ h (Fin.cons c (Fin.cons b (Fin.tail (Fin.tail w))))) (w 0) (w 1) :=
    (cobham_pair_comp (Cobham.appendFn (cobham_pairFst_comp (Cobham.proj 0)) (cobham_ctrBlock hf))
      (cobham_ctrBlock hh)).of_eq fun w ↦ rfl
  -- The block function on `(acc, b, s, params)`.
  have hg : Cobham fun x : Fin (n + 3) → List Bool ↦
      accStep (fun c b ↦ f (Fin.cons c (Fin.cons b (Fin.tail (Fin.tail (Fin.tail x))))))
        (fun c b ↦ h (Fin.cons c (Fin.cons b (Fin.tail (Fin.tail (Fin.tail x)))))) (x 0) (x 1) := by
    refine (Cobham.comp hstep
      (gs := fun i (x : Fin (n + 3) → List Bool) ↦
        (Fin.cons (x 0) (Fin.cons (x 1) (Fin.tail (Fin.tail (Fin.tail x)))) :
          Fin (n + 2) → List Bool) i) ?_).of_eq fun x ↦ rfl
    intro i
    refine Fin.cases ?_ (fun i ↦ Fin.cases ?_ (fun i ↦ ?_) i) i
    · exact Cobham.proj 0
    · exact Cobham.proj 1
    · exact Cobham.proj i.succ.succ.succ
  have hinit' : Cobham fun u : Fin (n + 1) → List Bool ↦
      pair (out₀ (Fin.tail u)) (ctr₀ (Fin.tail u)) :=
    cobham_pair_comp ((Cobham.comp hout fun i ↦ Cobham.proj i.succ).of_eq fun _ ↦ rfl)
      ((Cobham.comp hctr fun i ↦ Cobham.proj i.succ).of_eq fun _ ↦ rfl)
  have hbad : Cobham fun u : Fin (n + 1) → List Bool ↦
      pair [] (pair (out₀ (Fin.tail u)) (ctr₀ (Fin.tail u))) :=
    cobham_pair_comp (Cobham.const []) hinit'
  -- The ruler.
  set Bp : Polynomial ℕ := q + Polynomial.X + Polynomial.X * D with hBp
  set R : Polynomial ℕ := Polynomial.C 2 * Polynomial.X + Polynomial.C 2 +
    (Polynomial.C 2 * (q + Polynomial.X * K.comp (Polynomial.C 2 * Bp + Polynomial.X)) +
      Polynomial.C 2 + Bp) with hR
  have hReval : ∀ L, R.eval L = 2 * L + 2 +
      (2 * (q.eval L + L * K.eval (2 * (q.eval L + L + L * D.eval L) + L)) + 2 +
        (q.eval L + L + L * D.eval L)) := by
    intro L
    simp [hR, hBp, Polynomial.eval_comp]
  have hruler : Cobham fun u : Fin (n + 1) → List Bool ↦ Cobham.polyLen R (List.ofFn u).flatten :=
    Cobham.polyLen_mem _ (cobham_flattenOfFn (n + 1))
  refine (cobham_blockLoop hg hbad hinit' hruler ?_).of_eq fun v ↦ ?_
  · intro u k
    simp only [Fin.cons_zero, Fin.cons_one, Fin.tail_cons]
    have hs : (u 0).length ≤ ∑ i, (u i).length := by
      rw [Fin.sum_univ_succ]
      exact Nat.le_add_right _ _
    have hP : ∑ i, (Fin.tail u i).length ≤ ∑ i, (u i).length := by
      rw [Fin.sum_univ_succ]
      exact Nat.le_add_left _ _
    have hq : q.eval (∑ i, (Fin.tail u i).length) ≤ q.eval (∑ i, (u i).length) :=
      polynomial_eval_mono_nat q hP
    have hD : D.eval (∑ i, (Fin.tail u i).length) ≤ D.eval (∑ i, (u i).length) :=
      polynomial_eval_mono_nat D hP
    have hctr0 := le_trans (hctr_le (Fin.tail u)) hq
    have hout0 := le_trans (hout_le (Fin.tail u)) hq
    rw [Cobham.polyLen_length, length_flatten_ofFn, hReval]
    generalize hL : ∑ i, (u i).length = L at hs hP hq hD hctr0 hout0 ⊢
    generalize hDP : D.eval (∑ i, (Fin.tail u i).length) = DP at hD
    have hfold : ∀ bs : List (List Bool), (frame bs).length ≤ (u 0).length →
        (bs.foldl (accStep (fun c b ↦ f (Fin.cons c (Fin.cons b (Fin.tail u))))
          (fun c b ↦ h (Fin.cons c (Fin.cons b (Fin.tail u)))))
          (pair (out₀ (Fin.tail u)) (ctr₀ (Fin.tail u)))).length ≤
        2 * (q.eval L + L * K.eval (2 * (q.eval L + L + L * D.eval L) + L)) + 2 +
          (q.eval L + L + L * D.eval L) := by
      intro bs hbs
      have hbsl : bs.length ≤ L := le_trans (length_le_length_frame bs) (by omega)
      have hDmul : bs.length * DP ≤ L * D.eval L := Nat.mul_le_mul hbsl hD
      have h1 := length_foldl_accStep_le _ _ (q.eval L + L + L * D.eval L) DP
        (K.eval (2 * (q.eval L + L + L * D.eval L) + L))
        (fun ctr b ↦ by
          have := hh_le (Fin.cons ctr (Fin.cons b (Fin.tail u)))
          simp only [Fin.cons_zero, Fin.cons_one, Fin.tail_cons, hDP] at this
          exact this)
        (fun ctr b hc hb ↦ by
          have h1 := hf_le (Fin.cons ctr (Fin.cons b (Fin.tail u)))
          refine le_trans h1 (polynomial_eval_mono_nat K ?_)
          rw [Fin.sum_univ_succ, Fin.sum_univ_succ]
          simp only [Fin.cons_zero, Fin.cons_succ]
          omega)
        bs (out₀ (Fin.tail u)) (ctr₀ (Fin.tail u)) (by omega)
      have h2 : bs.length * K.eval (2 * (q.eval L + L + L * D.eval L) + L) ≤
          L * K.eval (2 * (q.eval L + L + L * D.eval L) + L) := Nat.mul_le_mul_right _ hbsl
      omega
    have hb := blockStep_iterate_length_le' _
      (pair [] (pair (out₀ (Fin.tail u)) (ctr₀ (Fin.tail u)))) (blockStep_pair_nil _ _ _) (u 0)
      (pair (out₀ (Fin.tail u)) (ctr₀ (Fin.tail u))) _ hfold
      (by rw [pair_length, pair_length]; simp only [List.length_nil]; omega) k
    refine le_trans hb ?_
    omega
  · rw [foldBlocks_eq_blockLoop]
    rfl

/-- **Clocked iteration with a polynomial ruler.** -/
theorem cobham_iter {n : ℕ} {f : (Fin (n + 1) → List Bool) → List Bool} (hf : Cobham f)
    {e : (Fin n → List Bool) → List Bool} (he : Cobham e) (q : Polynomial ℕ)
    (hbound : ∀ (c : List Bool) (v : Fin n → List Bool),
      ((fun s ↦ f (Fin.cons s v))^[c.length] (e v)).length ≤
        q.eval (c.length + ∑ i, (v i).length)) :
    Cobham fun v : Fin (n + 1) → List Bool ↦
      (fun s ↦ f (Fin.cons s (Fin.tail v)))^[(v 0).length] (e (Fin.tail v)) := by
  refine Cobham.iterFn he hf (Cobham.polyLen_mem q (cobham_flattenOfFn (n + 1))) ?_
  intro c v
  rw [Cobham.polyLen_length, length_flatten_ofFn, Fin.sum_univ_succ]
  simp only [Fin.cons_zero, Fin.cons_succ]
  exact hbound c v

/-- The two components read off a string fit in it. -/
theorem two_mul_length_pairFst_add_length_pairSnd_le (z : List Bool) :
    2 * (pairFst z).length + (pairSnd z).length ≤ z.length := by
  rcases hu : unpair? z with _ | ⟨x, y⟩
  · have h : pairSnd z = [] := by simp [pairSnd, hu]
    rw [h, List.length_nil, add_zero]
    exact two_mul_length_pairFst_le z
  · rw [eq_pair_of_unpair?_eq_some hu, pairFst_pair, pairSnd_pair, pair_length]
    omega

theorem caseBit₀_cases (s x y : List Bool) : caseBit₀ s x y = x ∨ caseBit₀ s x y = y := by
  cases s with
  | nil => exact Or.inr rfl
  | cons b s => cases b <;> simp

theorem length_notBit (x : List Bool) : (notBit x).length = 1 := by
  rcases caseBit₀_cases x [false] [true] with h | h <;> rw [notBit, h] <;> rfl

theorem frame_cons_pair (b : List Bool) (bs : List (List Bool)) : frame (b :: bs) = pair b (frame bs) := by
  simp [frame, pair]

theorem frame_singleton (b : List Bool) : frame [b] = delimit b := by simp [frame]

theorem pairFst_nil : pairFst [] = [] := rfl

theorem pairSnd_nil : pairSnd [] = [] := rfl

theorem encClauseU_cons' (l : Lit) (c : Clause) : encClauseU (l :: c) = pair (encLitU l) (encClauseU c) :=
  encClauseU_cons l c

/-! ### String-level gadgets -/

/-- Negation of an internal literal: flip the sign bit. -/
def negLitU (c : List Bool) : List Bool := pair (notBit (pairFst c)) (pairSnd c)

theorem negLitU_encLitU (l : Lit) : negLitU (encLitU l) = encLitU (Lit.neg l) := by
  simp [negLitU, encLitU, Lit.neg]

theorem length_negLitU_le (c : List Bool) : (negLitU c).length ≤ c.length + 4 := by
  have := length_pairSnd_le c
  simp only [negLitU, pair_length, length_notBit]
  omega

/-- `encCNFU (orGadget t l₁ l₂)` from `unaryN t`, `encLitU l₁`, `encLitU l₂`. -/
def orGadgetU (tU c₁ c₂ : List Bool) : List Bool :=
  frame [frame [pair [false] tU, c₁, c₂], frame [pair [true] tU, negLitU c₁],
    frame [pair [true] tU, negLitU c₂]]

theorem orGadgetU_eq (t : ℕ) (l₁ l₂ : Lit) :
    orGadgetU (unaryN t) (encLitU l₁) (encLitU l₂) = encCNFU (orGadget t l₁ l₂) := by
  rw [orGadgetU, negLitU_encLitU, negLitU_encLitU]
  rfl

theorem orGadgetU_eq' (t t' : ℕ) (l₂ : Lit) :
    orGadgetU (unaryN t) (pair [true] (unaryN t')) (encLitU l₂) = encCNFU (orGadget t ⟨true, t'⟩ l₂) :=
  orGadgetU_eq t ⟨true, t'⟩ l₂

theorem length_orGadgetU_le (tU c₁ c₂ : List Bool) :
    (orGadgetU tU c₁ c₂).length ≤ 12 * (tU.length + c₁.length + c₂.length) + 114 := by
  have h1 := length_negLitU_le c₁
  have h2 := length_negLitU_le c₂
  simp only [orGadgetU, length_frame_cons, frame_nil, List.length_nil, pair_length,
    List.length_singleton]
  omega

/-- `encCNFU (xorGadget t x₁ x₂)` from the unary strings. -/
def xorGadgetU (tU x₁ x₂ : List Bool) : List Bool :=
  frame [frame [pair [false] tU, pair [true] x₁, pair [true] x₂],
    frame [pair [false] tU, pair [false] x₁, pair [false] x₂],
    frame [pair [true] tU, pair [false] x₁, pair [true] x₂],
    frame [pair [true] tU, pair [true] x₁, pair [false] x₂]]

theorem xorGadgetU_eq (t x₁ x₂ : ℕ) :
    xorGadgetU (unaryN t) (unaryN x₁) (unaryN x₂) = encCNFU (xorGadget t x₁ x₂) := rfl

theorem length_xorGadgetU_le (tU x₁ x₂ : List Bool) :
    (xorGadgetU tU x₁ x₂).length ≤ 16 * (tU.length + x₁.length + x₂.length) + 248 := by
  simp only [xorGadgetU, length_frame_cons, frame_nil, List.length_nil, pair_length,
    List.length_singleton]
  omega

/-! ### The hash rows -/

/-- One row of width `|w|`: move it from the remaining bits to the framed accumulator. -/
def hashRowsStep (w st : List Bool) : List Bool :=
  pair ((pairFst st).drop w.length) (pairSnd st ++ delimit ((pairFst st).take w.length))

/-- The `|k|` rows of width `|w|` of `hb`, framed. -/
def hashRowsStr (w k hb : List Bool) : List Bool :=
  pairSnd ((hashRowsStep w)^[k.length] (pair hb []))

theorem hashRowsStep_iterate (w hb acc : List Bool) : ∀ j : ℕ,
    (hashRowsStep w)^[j] (pair hb acc) = pair (hb.drop (j * w.length))
      (acc ++ frame ((List.range j).map fun i ↦ (hb.drop (i * w.length)).take w.length)) := by
  intro j
  induction j with
  | zero => simp [frame_nil]
  | succ j ih =>
    rw [Function.iterate_succ_apply', ih, hashRowsStep, pairFst_pair, pairSnd_pair, List.drop_drop,
      List.range_succ, List.map_append, frame_append, List.map_singleton, frame_singleton,
      List.append_assoc, Nat.succ_mul, Nat.add_comm (j * w.length)]

theorem hashRowsStr_eq (m₀ k : ℕ) (hb : List Bool) :
    hashRowsStr (true :: unaryN m₀) (unaryN k) hb = frame (hashRows m₀ k hb) := by
  rw [hashRowsStr, length_unaryN, hashRowsStep_iterate, pairSnd_pair, List.nil_append, hashRows]
  simp

theorem length_hashRowsStep_le (w st : List Bool) :
    (hashRowsStep w st).length ≤ st.length + 2 * w.length + 4 := by
  have h1 := two_mul_length_pairFst_add_length_pairSnd_le st
  have h2 : ((pairFst st).drop w.length).length ≤ (pairFst st).length := by
    rw [List.length_drop]; omega
  have h3 : ((pairFst st).take w.length).length ≤ w.length := by
    rw [List.length_take]; omega
  simp only [hashRowsStep, pair_length, List.length_append, delimit_length]
  omega

theorem length_hashRowsStep_iterate_le (w hb : List Bool) (j : ℕ) :
    ((hashRowsStep w)^[j] (pair hb [])).length ≤ 2 * hb.length + 2 + j * (2 * w.length + 4) := by
  induction j with
  | zero => simp [pair_length]
  | succ j ih =>
    rw [Function.iterate_succ_apply', add_mul, one_mul]
    have := length_hashRowsStep_le w ((hashRowsStep w)^[j] (pair hb []))
    omega

/-! ### Choosing `k` -/

/-- One step: advance the binary counter and the unary counter; record the unary counter when
the binary counter equals the target. -/
def chooseKStep (kb st : List Bool) : List Bool :=
  let c' := succBits (pairFst st)
  let i' := pairFst (pairSnd st) ++ [true]
  pair c' (pair i' (caseBit₀ (eqBits c' kb) i' (pairSnd (pairSnd st))))

/-- `unaryN (chooseK m₀ kb)` from `unaryN m₀` and the `k`-bits. -/
def chooseKStr (m kb : List Bool) : List Bool :=
  let u := pairSnd (pairSnd ((chooseKStep kb)^[(true :: true :: m).length] (pair [] (pair [] []))))
  caseBit₀ (nonemptyFlag u) u [true]

theorem chooseKStep_iterate (kb : List Bool) : ∀ j : ℕ,
    (chooseKStep kb)^[j] (pair [] (pair [] [])) = pair (encNat j) (pair (unaryN j)
      (if 1 ≤ decNat kb ∧ decNat kb ≤ j then unaryN (decNat kb) else [])) := by
  intro j
  induction j with
  | zero =>
    rw [Function.iterate_zero_apply, ite_eq_right (by omega)]
    simp [encNat, unaryN_zero]
  | succ j ih =>
    rw [Function.iterate_succ_apply', ih]
    simp only [chooseKStep, pairFst_pair, pairSnd_pair, succBits_encNat, unaryN_append_true]
    by_cases h : decNat kb = j + 1
    · have hflag : eqBits (encNat (j + 1)) kb = [true] := (eqBits_eq_true_iff _ _).mpr (by simp [h])
      rw [hflag, caseBit₀_cons, Bool.cond_true, ite_eq_left (by omega), h]
    · have hflag : eqBits (encNat (j + 1)) kb = [false] := by
        rcases eqBits_flag (encNat (j + 1)) kb with h' | h'
        · exact absurd ((eqBits_eq_true_iff _ _).mp h') (by simp; omega)
        · exact h'
      rw [hflag, caseBit₀_cons, Bool.cond_false]
      congr 2
      by_cases h1 : 1 ≤ decNat kb ∧ decNat kb ≤ j
      · rw [ite_eq_left h1, ite_eq_left (by omega)]
      · rw [ite_eq_right h1, ite_eq_right (by omega)]

theorem chooseKStr_eq (m₀ : ℕ) (kb : List Bool) :
    chooseKStr (unaryN m₀) kb = unaryN (chooseK m₀ kb) := by
  have hlen : (true :: true :: unaryN m₀).length = m₀ + 2 := by simp
  simp only [chooseKStr, hlen, chooseKStep_iterate, pairSnd_pair, chooseK]
  by_cases h : 1 ≤ decNat kb ∧ decNat kb ≤ m₀ + 2
  · rw [ite_eq_left h, ite_eq_left h]
    obtain ⟨j, hj⟩ : ∃ j, decNat kb = j + 1 := ⟨decNat kb - 1, by omega⟩
    rw [hj, unaryN_succ, nonemptyFlag_cons, caseBit₀_cons, Bool.cond_true]
  · rw [ite_eq_right h, ite_eq_right h, nonemptyFlag_nil, caseBit₀_nil]
    rfl

theorem length_chooseKStep_iterate_le (kb : List Bool) (j : ℕ) :
    ((chooseKStep kb)^[j] (pair [] (pair [] []))).length ≤ 5 * j + 4 := by
  rw [chooseKStep_iterate]
  have h1 : (encNat j).length ≤ j := by
    rw [length_encNat]; exact Nat.size_le.mpr Nat.lt_two_pow_self
  have h2 : (if 1 ≤ decNat kb ∧ decNat kb ≤ j then unaryN (decNat kb) else []).length ≤ j := by
    by_cases h : 1 ≤ decNat kb ∧ decNat kb ≤ j
    · rw [ite_eq_left h, length_unaryN]; omega
    · rw [ite_eq_right h]; simp
  simp only [pair_length, length_unaryN]
  omega

/-! ### Selected variables of a hash row -/

/-- One step: read the next row bit, advance the unary index, and record the index if the bit is
set. -/
def rowSelStep (st : List Bool) : List Bool :=
  let row := pairFst st
  let jU := pairFst (pairSnd st)
  let acc := pairSnd (pairSnd st)
  pair row.tail (pair (jU ++ [true]) (caseBit₀ (bitAt [] row) (acc ++ delimit jU) acc))

/-- The framed list of the unary indices `j < |m|` whose row bit is set. -/
def rowSelStr (m row : List Bool) : List Bool :=
  pairSnd (pairSnd (rowSelStep^[m.length] (pair row (pair [] []))))

theorem filter_range_succ (p : ℕ → Bool) (j : ℕ) :
    (List.range (j + 1)).filter p = (List.range j).filter p ++ if p j then [j] else [] := by
  rw [List.range_succ, List.filter_append]
  congr 1
  cases h : p j <;> simp [h]

theorem rowSelStep_iterate (row : List Bool) : ∀ j : ℕ,
    rowSelStep^[j] (pair row (pair [] [])) = pair (row.drop j) (pair (unaryN j)
      (frame (((List.range j).filter fun i ↦ row.getD i false).map unaryN))) := by
  intro j
  induction j with
  | zero => simp [frame_nil, unaryN_zero]
  | succ j ih =>
    have hget : (row.drop j).getD 0 false = row.getD j false := by
      simp [List.getD_eq_getElem?_getD, List.getElem?_drop]
    rw [Function.iterate_succ_apply', ih]
    simp only [rowSelStep, pairFst_pair, pairSnd_pair, List.tail_drop, unaryN_append_true,
      filter_range_succ, List.map_append, frame_append]
    rw [bitAt_eq_getD_single, List.length_nil, hget]
    cases hb : row.getD j false
    · simp [frame_nil]
    · simp [frame_singleton]

theorem rowSelStr_eq (m₀ : ℕ) (row : List Bool) :
    rowSelStr (unaryN m₀) row = frame ((rowOfList m₀ row).1.map unaryN) := by
  rw [rowSelStr, length_unaryN, rowSelStep_iterate, pairSnd_pair, pairSnd_pair, rowOfList]

theorem length_frame_le_of_forall (N : ℕ) : ∀ bs : List (List Bool), (∀ b ∈ bs, b.length ≤ N) →
    (frame bs).length ≤ bs.length * (2 * N + 2)
  | [], _ => by simp [frame_nil]
  | b :: bs, h => by
    rw [length_frame_cons, List.length_cons, add_mul, one_mul]
    have h1 := length_frame_le_of_forall N bs fun b' hb' ↦ h b' (List.mem_cons_of_mem _ hb')
    have h2 := h b (List.mem_cons_self ..)
    omega

theorem length_rowSelStep_iterate_le (row : List Bool) (j : ℕ) :
    (rowSelStep^[j] (pair row (pair [] []))).length ≤ 2 * row.length + 2 * j + 6 + j * (2 * j + 2) := by
  rw [rowSelStep_iterate]
  have h1 : (row.drop j).length ≤ row.length := by rw [List.length_drop]; omega
  have h2 := length_frame_le_of_forall j (((List.range j).filter fun i ↦ row.getD i false).map unaryN)
    (by
      intro b hb
      obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hb
      have := List.mem_range.mp (List.mem_filter.mp hi).1
      simp
      omega)
  have h3 : (((List.range j).filter fun i ↦ row.getD i false).map unaryN).length ≤ j := by
    rw [List.length_map]
    exact le_trans (List.length_filter_le _ _) (by simp)
  have h4 := Nat.mul_le_mul_right (2 * j + 2) h3
  simp only [pair_length, length_unaryN]
  omega

theorem length_rowSelStr_le (m row : List Bool) :
    (rowSelStr m row).length ≤ 2 * row.length + 2 * m.length + 6 + m.length * (2 * m.length + 2) :=
  le_trans (length_pairSnd_le _) (le_trans (length_pairSnd_le _) (length_rowSelStep_iterate_le row _))

/-! ### Parity constraints -/

def xorStepF (ctr b : List Bool) : List Bool := xorGadgetU ctr ctr.tail b
def xorStepH (ctr _b : List Bool) : List Bool := ctr ++ [true]

/-- `pair (encCNFU (parityCnf t xs b).1) (unaryN (parityCnf t xs b).2)` for the row `row` of
width `|m| + 1` and `(xs, b) = rowOfList |m| row`. -/
def parityCnfStr (m tU row : List Bool) : List Bool :=
  let sel := rowSelStr m row
  let bt := bitAt m row
  let x₀ := pairFst sel
  let rest := pairSnd sel
  let x₁ := pairFst rest
  let rest' := pairSnd rest
  let r := foldBlocks (accStep xorStepF xorStepH) (pair [] (tU ++ [true])) rest'
  let ctr := pairSnd r
  let long := pair (xorGadgetU tU x₀ x₁ ++ pairFst r ++ delimit (delimit (pair bt ctr.tail)))
    ((ctr.drop tU.length).take m.length)
  let one := pair (delimit (delimit (pair bt x₀))) []
  let zero := pair (caseBit₀ bt (delimit []) []) []
  caseBit₀ (nonemptyFlag sel) (caseBit₀ (nonemptyFlag rest) long one) zero

theorem foldl_xorStep (rest : List ℕ) : ∀ (t : ℕ) (acc : List Bool),
    (rest.map unaryN).foldl (accStep xorStepF xorStepH) (pair acc (unaryN (t + 1))) =
      pair (acc ++ encCNFU (xorChain.xorChainAux (t + 1) t rest)) (unaryN (t + 1 + rest.length)) := by
  induction rest with
  | nil => intro t acc; simp [xorChain.xorChainAux, encCNFU_nil]
  | cons x rest ih =>
    intro t acc
    rw [List.map_cons, List.foldl_cons, accStep_pair, xorStepF, xorStepH, unaryN_tail,
      xorGadgetU_eq, unaryN_append_true, ih, xorChain.xorChainAux, encCNFU_append,
      List.append_assoc, List.length_cons, show t + 1 + 1 + rest.length = t + 1 + (rest.length + 1) by
        omega]

theorem parityCnfStr_zero (m tU row : List Bool) (h : rowSelStr m row = []) :
    parityCnfStr m tU row = pair (caseBit₀ (bitAt m row) (delimit []) []) [] := by
  simp only [parityCnfStr, h, nonemptyFlag_nil, caseBit₀_nil]

theorem parityCnfStr_one (m tU row x₀ : List Bool) (h : rowSelStr m row = pair x₀ []) :
    parityCnfStr m tU row = pair (delimit (delimit (pair (bitAt m row) x₀))) [] := by
  simp only [parityCnfStr, h, pairFst_pair, pairSnd_pair, nonemptyFlag_nil, caseBit₀_nil,
    nonemptyFlag_of_ne_nil (pair_ne_nil x₀ []), caseBit₀_cons, Bool.cond_true]

theorem parityCnfStr_long (m tU row x₀ x₁ rest' : List Bool)
    (h : rowSelStr m row = pair x₀ (pair x₁ rest')) :
    parityCnfStr m tU row =
      pair (xorGadgetU tU x₀ x₁ ++
          pairFst (foldBlocks (accStep xorStepF xorStepH) (pair [] (tU ++ [true])) rest') ++
          delimit (delimit (pair (bitAt m row)
            (pairSnd (foldBlocks (accStep xorStepF xorStepH) (pair [] (tU ++ [true])) rest')).tail)))
        (((pairSnd (foldBlocks (accStep xorStepF xorStepH) (pair [] (tU ++ [true])) rest')).drop
          tU.length).take m.length) := by
  simp only [parityCnfStr, h, pairFst_pair, pairSnd_pair,
    nonemptyFlag_of_ne_nil (pair_ne_nil x₀ (pair x₁ rest')),
    nonemptyFlag_of_ne_nil (pair_ne_nil x₁ rest'), caseBit₀_cons, Bool.cond_true]

theorem parityCnfStr_eq (m₀ t : ℕ) (row : List Bool) :
    parityCnfStr (unaryN m₀) (unaryN t) row =
      pair (encCNFU (parityCnf t (rowOfList m₀ row).1 (rowOfList m₀ row).2).1)
        (unaryN (parityCnf t (rowOfList m₀ row).1 (rowOfList m₀ row).2).2) := by
  have hbt : bitAt (unaryN m₀) row = [(rowOfList m₀ row).2] := by
    rw [bitAt_eq_getD_single, length_unaryN]
    rfl
  have hlen := rowOfList_fst_length_le m₀ row
  have hsel := rowSelStr_eq m₀ row
  generalize (rowOfList m₀ row).1 = xs at hsel hlen ⊢
  generalize (rowOfList m₀ row).2 = b at hbt ⊢
  match xs with
  | [] =>
    rw [parityCnfStr_zero _ _ _ (by rw [hsel, List.map_nil, frame_nil]), hbt, parityCnf]
    cases b <;> simp [encCNFU_cons, encCNFU_nil, encClauseU_nil, unaryN_zero]
  | [x] =>
    rw [parityCnfStr_one _ _ _ (unaryN x)
      (by rw [hsel, List.map_cons, List.map_nil, frame_cons_pair, frame_nil]), hbt, parityCnf]
    simp [encCNFU_cons, encCNFU_nil, encClauseU_cons, encClauseU_nil, encLitU, unaryN_zero]
  | x₀ :: x₁ :: rest =>
    have htail : (unaryN (t + 1 + rest.length)).tail = unaryN (t + rest.length) := by
      rw [show t + 1 + rest.length = t + rest.length + 1 by omega]
      rfl
    have hdrop : ((unaryN (t + 1 + rest.length)).drop t).take m₀ = unaryN (rest.length + 1) := by
      rw [show t + 1 + rest.length = t + (rest.length + 1) by omega, unaryN_drop, unaryN_take_of_le]
      simp at hlen
      omega
    rw [parityCnfStr_long _ _ _ (unaryN x₀) (unaryN x₁) (frame (rest.map unaryN))
      (by rw [hsel, List.map_cons, List.map_cons, frame_cons_pair, frame_cons_pair]), hbt,
      parityCnf, unaryN_append_true, foldBlocks_frame, foldl_xorStep, pairFst_pair, pairSnd_pair,
      List.nil_append, xorGadgetU_eq, length_unaryN, length_unaryN, htail, hdrop]
    simp [encCNFU_append, encCNFU_cons, encCNFU_nil, encClauseU_cons, encClauseU_nil, encLitU,
      xorChain]

/-! ### Shortening a clause -/

def orStepF (ctr _b : List Bool) : List Bool :=
  orGadgetU (pairFst ctr) (pair [true] (pairFst ctr).tail) (pairSnd ctr)
def orStepH (ctr b : List Bool) : List Bool := pair (pairFst ctr ++ [true]) b

/-- `pair (encCNFU (shortenClause t c).1) (unaryN (shortenClause t c).2)` from `unaryN t` and
`encClauseU c`. -/
def shortenClauseStr (tU c : List Bool) : List Bool :=
  let l₁ := pairFst c
  let r₁ := pairSnd c
  let l₂ := pairFst r₁
  let r₂ := pairSnd r₁
  let l₃ := pairFst r₂
  let r₃ := pairSnd r₂
  let r := foldBlocks (accStep orStepF orStepH) (pair [] (pair (tU ++ [true]) l₃)) r₃
  let ctr := pairSnd r
  let long := pair (orGadgetU tU l₁ l₂ ++ pairFst r ++
      delimit (frame [pair [true] (pairFst ctr).tail, pairSnd ctr]))
    (((pairFst ctr).drop tU.length).take c.length)
  caseBit₀ (nonemptyFlag r₃) long (pair (delimit c) [])

theorem orChainAux_singleton (t prev : ℕ) (l : Lit) :
    shortenClause.orChainAux t prev [l] = [[⟨true, prev⟩, l]] := rfl

theorem orChainAux_cons_cons (t prev : ℕ) (l l' : Lit) (ls : List Lit) :
    shortenClause.orChainAux t prev (l :: l' :: ls) =
      orGadget t ⟨true, prev⟩ l ++ shortenClause.orChainAux (t + 1) t (l' :: ls) := rfl

theorem foldl_orStep (ls : List Lit) : ∀ (t : ℕ) (acc : List Bool) (p : Lit),
    ∃ (acc' : List Bool) (q : Lit),
      (ls.map encLitU).foldl (accStep orStepF orStepH)
          (pair acc (pair (unaryN (t + 1)) (encLitU p))) =
        pair acc' (pair (unaryN (t + 1 + ls.length)) (encLitU q)) ∧
      acc' ++ delimit (frame [pair [true] (unaryN (t + ls.length)), encLitU q]) =
        acc ++ encCNFU (shortenClause.orChainAux (t + 1) t (p :: ls)) := by
  induction ls with
  | nil =>
    intro t acc p
    refine ⟨acc, p, by simp, ?_⟩
    rw [orChainAux_singleton]
    simp [encCNFU_cons, encCNFU_nil, encClauseU_cons, encClauseU_nil, encLitU, frame_cons, frame_nil]
  | cons l ls ih =>
    intro t acc p
    rw [List.map_cons, List.foldl_cons, accStep_pair, orStepF, orStepH, pairFst_pair, pairSnd_pair,
      unaryN_tail, unaryN_append_true, orGadgetU_eq']
    obtain ⟨acc', q, h1, h2⟩ := ih (t + 1) (acc ++ encCNFU (orGadget (t + 1) ⟨true, t⟩ p)) l
    refine ⟨acc', q, ?_, ?_⟩
    · rw [h1, List.length_cons, show t + 1 + 1 + ls.length = t + 1 + (ls.length + 1) by omega]
    · rw [List.length_cons, show t + (ls.length + 1) = t + 1 + ls.length by omega, h2,
        orChainAux_cons_cons, encCNFU_append, List.append_assoc]

theorem shortenClauseStr_short (tU c : List Bool) (hc : pairSnd (pairSnd (pairSnd c)) = []) :
    shortenClauseStr tU c = pair (delimit c) [] := by
  simp only [shortenClauseStr, hc, nonemptyFlag_nil, caseBit₀_nil]

theorem shortenClauseStr_long (tU l₁ l₂ l₃ r₃ : List Bool) (h : r₃ ≠ []) :
    shortenClauseStr tU (pair l₁ (pair l₂ (pair l₃ r₃))) =
      pair (orGadgetU tU l₁ l₂ ++
          pairFst (foldBlocks (accStep orStepF orStepH) (pair [] (pair (tU ++ [true]) l₃)) r₃) ++
          delimit (frame [pair [true] (pairFst (pairSnd
            (foldBlocks (accStep orStepF orStepH) (pair [] (pair (tU ++ [true]) l₃)) r₃))).tail,
            pairSnd (pairSnd
              (foldBlocks (accStep orStepF orStepH) (pair [] (pair (tU ++ [true]) l₃)) r₃))]))
        (((pairFst (pairSnd
            (foldBlocks (accStep orStepF orStepH) (pair [] (pair (tU ++ [true]) l₃)) r₃))).drop
          tU.length).take (pair l₁ (pair l₂ (pair l₃ r₃))).length) := by
  simp only [shortenClauseStr, pairFst_pair, pairSnd_pair, nonemptyFlag_of_ne_nil h, caseBit₀_cons,
    Bool.cond_true]

theorem shortenClauseStr_eq (t : ℕ) (c : Clause) :
    shortenClauseStr (unaryN t) (encClauseU c) =
      pair (encCNFU (shortenClause t c).1) (unaryN (shortenClause t c).2) := by
  match c with
  | [] | [_] | [_, _] | [_, _, _] =>
    rw [shortenClauseStr_short _ _ (by simp [encClauseU_cons', encClauseU_nil, pairSnd_nil]),
      shortenClause_short _ _ (by simp)]
    simp only [encCNFU_singleton, unaryN_zero]
  | l₁ :: l₂ :: l₃ :: l₄ :: rest =>
    have hlen := length_le_length_encClauseU (l₁ :: l₂ :: l₃ :: l₄ :: rest)
    have htail : (unaryN (t + 1 + (rest.length + 1))).tail = unaryN (t + (rest.length + 1)) := by
      rw [show t + 1 + (rest.length + 1) = t + (rest.length + 1) + 1 by omega]
      rfl
    have hdrop : ((unaryN (t + 1 + (rest.length + 1))).drop t).take
        (encClauseU (l₁ :: l₂ :: l₃ :: l₄ :: rest)).length = unaryN (rest.length + 2) := by
      rw [show t + 1 + (rest.length + 1) = t + (rest.length + 2) by omega, unaryN_drop,
        unaryN_take_of_le]
      simp at hlen
      omega
    obtain ⟨acc', q, h1, h2⟩ := foldl_orStep (l₄ :: rest) t [] l₃
    rw [List.length_cons] at h1 h2
    rw [encClauseU_cons' l₁, encClauseU_cons' l₂, encClauseU_cons' l₃,
      shortenClauseStr_long _ _ _ _ _ (encClauseU_ne_nil l₄ rest), unaryN_append_true,
      show encClauseU (l₄ :: rest) = frame ((l₄ :: rest).map encLitU) from rfl, foldBlocks_frame, h1,
      pairFst_pair, pairSnd_pair, pairFst_pair, pairSnd_pair, htail, List.append_assoc, h2,
      List.nil_append, orGadgetU_eq, ← encCNFU_append, length_unaryN,
      show frame ((l₄ :: rest).map encLitU) = encClauseU (l₄ :: rest) from rfl,
      ← encClauseU_cons' l₃, ← encClauseU_cons' l₂, ← encClauseU_cons' l₁, hdrop]
    rfl

/-! ### All clauses and all rows -/

def shortenStepF (ctr b : List Bool) : List Bool := pairFst (shortenClauseStr ctr b)
def shortenStepH (ctr b : List Bool) : List Bool := ctr ++ pairSnd (shortenClauseStr ctr b)

/-- `pair (encCNFU (shortenAll m₀ φ).1) (unaryN (shortenAll m₀ φ).2)`. -/
def shortenAllStr (m t : List Bool) : List Bool :=
  foldBlocks (accStep shortenStepF shortenStepH) (pair [] m) t

theorem foldl_shortenStep (φ : CNF) : ∀ (t : ℕ) (acc : List Bool),
    (φ.map encClauseU).foldl (accStep shortenStepF shortenStepH) (pair acc (unaryN t)) =
      pair (acc ++ encCNFU (shortenAll t φ).1) (unaryN (shortenAll t φ).2) := by
  induction φ with
  | nil => intro t acc; simp [shortenAll, encCNFU_nil]
  | cons c φ ih =>
    intro t acc
    rw [List.map_cons, List.foldl_cons, accStep_pair, shortenStepF, shortenStepH,
      shortenClauseStr_eq, pairFst_pair, pairSnd_pair, ← unaryN_add, ih, shortenAll]
    simp only [encCNFU_append, List.append_assoc]

theorem shortenAllStr_eq (m₀ : ℕ) (φ : CNF) :
    shortenAllStr (unaryN m₀) (encCNFU φ) =
      pair (encCNFU (shortenAll m₀ φ).1) (unaryN (shortenAll m₀ φ).2) := by
  rw [shortenAllStr, encCNFU, foldBlocks_frame, foldl_shortenStep, List.nil_append]

def rowStepF (m ctr b : List Bool) : List Bool := pairFst (parityCnfStr m ctr b)
def rowStepH (m ctr b : List Bool) : List Bool := ctr ++ pairSnd (parityCnfStr m ctr b)

/-- `pair (encCNFU (isolateRows m₀ t rows).1) (unaryN (isolateRows m₀ t rows).2)`. -/
def isolateRowsStr (m tU rows : List Bool) : List Bool :=
  foldBlocks (accStep (rowStepF m) (rowStepH m)) (pair [] tU) rows

theorem foldl_rowStep (m₀ : ℕ) (rows : List (List Bool)) : ∀ (t : ℕ) (acc : List Bool),
    rows.foldl (accStep (rowStepF (unaryN m₀)) (rowStepH (unaryN m₀))) (pair acc (unaryN t)) =
      pair (acc ++ encCNFU (isolateRows m₀ t rows).1) (unaryN (isolateRows m₀ t rows).2) := by
  induction rows with
  | nil => intro t acc; simp [isolateRows, encCNFU_nil]
  | cons row rows ih =>
    intro t acc
    rw [List.foldl_cons, accStep_pair, rowStepF, rowStepH, parityCnfStr_eq, pairFst_pair,
      pairSnd_pair, ← unaryN_add, ih, isolateRows]
    simp only [encCNFU_append, List.append_assoc]

theorem isolateRowsStr_eq (m₀ t : ℕ) (rows : List (List Bool)) :
    isolateRowsStr (unaryN m₀) (unaryN t) (frame rows) =
      pair (encCNFU (isolateRows m₀ t rows).1) (unaryN (isolateRows m₀ t rows).2) := by
  rw [isolateRowsStr, foldBlocks_frame, foldl_rowStep, List.nil_append]

/-- The isolation map on `pair t (pair kb hb)` where `t = encCNFU φ`, `kb`, `hb` are the exact
`kBits m₀`- and `hashBits m₀`-bit blocks. -/
def isolateStr (z : List Bool) : List Bool :=
  let t := pairFst z
  let kb := pairFst (pairSnd z)
  let hb := pairSnd (pairSnd z)
  let m := numVarsStr t
  let s := shortenAllStr m t
  let r := isolateRowsStr m (pairSnd s) (hashRowsStr (true :: m) (chooseKStr m kb) hb)
  pair (pairFst s ++ pairFst r) (pairSnd r)

theorem isolateStr_encCNFU (φ : CNF) (kb hb : List Bool) :
    isolateStr (pair (encCNFU φ) (pair kb hb)) =
      pair (encCNFU (isolateSeed φ kb hb).1) (unaryN (isolateSeed φ kb hb).2) := by
  simp only [isolateStr, pairFst_pair, pairSnd_pair, numVarsStr_encCNFU, shortenAllStr_eq,
    chooseKStr_eq, hashRowsStr_eq, isolateRowsStr_eq, isolateSeed, isolate, encCNFU_append]

/-! ### Polynomial length bounds come for free

Every function of Cobham's algebra has a polynomially bounded output length; this discharges the
`hf_le`/`hout_le`/`hctr_le` side conditions of `cobham_foldAcc` mechanically. -/

theorem cobham_length_poly : ∀ {n : ℕ} {f : (Fin n → List Bool) → List Bool}, Cobham f →
    ∃ q : Polynomial ℕ, ∀ v : Fin n → List Bool, (f v).length ≤ q.eval (∑ i, (v i).length) := by
  intro n f hf
  induction hf with
  | proj i =>
    refine ⟨Polynomial.X, fun v ↦ ?_⟩
    simpa using Finset.single_le_sum (f := fun i ↦ (v i).length)
      (fun _ _ ↦ Nat.zero_le _) (Finset.mem_univ i)
  | empty => exact ⟨0, fun v ↦ by simp⟩
  | bit b => exact ⟨Polynomial.X + 1, fun v ↦ by simp⟩
  | smash =>
    refine ⟨Polynomial.X * Polynomial.X, fun v ↦ ?_⟩
    simp only [smash_length, Polynomial.eval_mul, Polynomial.eval_X, Fin.sum_univ_two]
    exact Nat.mul_le_mul (by omega) (by omega)
  | comp hf hgs ihf ihgs =>
    obtain ⟨qf, hqf⟩ := ihf
    choose qg hqg using ihgs
    refine ⟨qf.comp (∑ i, qg i), fun v ↦ ?_⟩
    rw [Polynomial.eval_comp, Polynomial.eval_finsetSum]
    refine le_trans (hqf _) (polynomial_eval_mono_nat qf ?_)
    exact Finset.sum_le_sum fun i _ ↦ hqg i v
  | boundedRec hg hh0 hh1 hj hlen ihg ihh0 ihh1 ihj =>
    obtain ⟨qj, hqj⟩ := ihj
    refine ⟨qj, fun v ↦ ?_⟩
    refine le_trans (hlen (v 0) (Fin.tail v)) ?_
    rw [Fin.cons_self_tail]
    exact hqj v

/-- `cobham_foldAcc` with the polynomial side conditions discharged automatically. -/
theorem cobham_foldAcc' {n : ℕ} {f h : (Fin (n + 2) → List Bool) → List Bool}
    (hf : Cobham f) (hh : Cobham h)
    {out₀ ctr₀ : (Fin n → List Bool) → List Bool} (hout : Cobham out₀) (hctr : Cobham ctr₀)
    (D : Polynomial ℕ)
    (hh_le : ∀ w, (h w).length ≤ (w 0).length + 2 * (w 1).length + 2 +
      D.eval (∑ i, (Fin.tail (Fin.tail w) i).length)) :
    Cobham fun v : Fin (n + 1) → List Bool ↦
      foldBlocks (accStep (fun c b ↦ f (Fin.cons c (Fin.cons b (Fin.tail v))))
        (fun c b ↦ h (Fin.cons c (Fin.cons b (Fin.tail v)))))
        (pair (out₀ (Fin.tail v)) (ctr₀ (Fin.tail v))) (v 0) := by
  obtain ⟨q₁, hq₁⟩ := cobham_length_poly hout
  obtain ⟨q₂, hq₂⟩ := cobham_length_poly hctr
  obtain ⟨K, hK⟩ := cobham_length_poly hf
  refine cobham_foldAcc hf hh hout hctr (q₁ + q₂) D K (fun p ↦ ?_) (fun p ↦ ?_) hh_le hK
  · have := hq₁ p
    simp only [Polynomial.eval_add]
    omega
  · have := hq₂ p
    simp only [Polynomial.eval_add]
    omega

/-! ### Framed tuples in the algebra -/

theorem cobham_frame1_comp {n : ℕ} {g₀ : (Fin n → List Bool) → List Bool} (h₀ : Cobham g₀) :
    Cobham fun v : Fin n → List Bool ↦ frame [g₀ v] :=
  (cobham_delimit_comp h₀).of_eq fun _ ↦ (frame_singleton _).symm

theorem cobham_frame2_comp {n : ℕ} {g₀ g₁ : (Fin n → List Bool) → List Bool}
    (h₀ : Cobham g₀) (h₁ : Cobham g₁) :
    Cobham fun v : Fin n → List Bool ↦ frame [g₀ v, g₁ v] :=
  (Cobham.appendFn (cobham_delimit_comp h₀) (cobham_frame1_comp h₁)).of_eq fun _ ↦
    (frame_cons _ _).symm

theorem cobham_frame3_comp {n : ℕ} {g₀ g₁ g₂ : (Fin n → List Bool) → List Bool}
    (h₀ : Cobham g₀) (h₁ : Cobham g₁) (h₂ : Cobham g₂) :
    Cobham fun v : Fin n → List Bool ↦ frame [g₀ v, g₁ v, g₂ v] :=
  (Cobham.appendFn (cobham_delimit_comp h₀) (cobham_frame2_comp h₁ h₂)).of_eq fun _ ↦
    (frame_cons _ _).symm

theorem cobham_frame4_comp {n : ℕ} {g₀ g₁ g₂ g₃ : (Fin n → List Bool) → List Bool}
    (h₀ : Cobham g₀) (h₁ : Cobham g₁) (h₂ : Cobham g₂) (h₃ : Cobham g₃) :
    Cobham fun v : Fin n → List Bool ↦ frame [g₀ v, g₁ v, g₂ v, g₃ v] :=
  (Cobham.appendFn (cobham_delimit_comp h₀) (cobham_frame3_comp h₁ h₂ h₃)).of_eq fun _ ↦
    (frame_cons _ _).symm

/-! ### The gadgets are in the algebra -/

theorem cobham_negLitU_comp {n : ℕ} {g : (Fin n → List Bool) → List Bool} (hg : Cobham g) :
    Cobham fun v : Fin n → List Bool ↦ negLitU (g v) :=
  (cobham_pair_comp (Cobham.notFn (cobham_pairFst_comp hg)) (cobham_pairSnd_comp hg)).of_eq
    fun _ ↦ rfl

theorem cobham_orGadgetU_comp {n : ℕ} {gt g₁ g₂ : (Fin n → List Bool) → List Bool}
    (ht : Cobham gt) (h₁ : Cobham g₁) (h₂ : Cobham g₂) :
    Cobham fun v : Fin n → List Bool ↦ orGadgetU (gt v) (g₁ v) (g₂ v) :=
  (cobham_frame3_comp
      (cobham_frame3_comp (cobham_pair_comp (Cobham.const [false]) ht) h₁ h₂)
      (cobham_frame2_comp (cobham_pair_comp (Cobham.const [true]) ht) (cobham_negLitU_comp h₁))
      (cobham_frame2_comp (cobham_pair_comp (Cobham.const [true]) ht)
        (cobham_negLitU_comp h₂))).of_eq fun _ ↦ rfl

theorem cobham_xorGadgetU_comp {n : ℕ} {gt g₁ g₂ : (Fin n → List Bool) → List Bool}
    (ht : Cobham gt) (h₁ : Cobham g₁) (h₂ : Cobham g₂) :
    Cobham fun v : Fin n → List Bool ↦ xorGadgetU (gt v) (g₁ v) (g₂ v) :=
  (cobham_frame4_comp
      (cobham_frame3_comp (cobham_pair_comp (Cobham.const [false]) ht)
        (cobham_pair_comp (Cobham.const [true]) h₁) (cobham_pair_comp (Cobham.const [true]) h₂))
      (cobham_frame3_comp (cobham_pair_comp (Cobham.const [false]) ht)
        (cobham_pair_comp (Cobham.const [false]) h₁) (cobham_pair_comp (Cobham.const [false]) h₂))
      (cobham_frame3_comp (cobham_pair_comp (Cobham.const [true]) ht)
        (cobham_pair_comp (Cobham.const [false]) h₁) (cobham_pair_comp (Cobham.const [true]) h₂))
      (cobham_frame3_comp (cobham_pair_comp (Cobham.const [true]) ht)
        (cobham_pair_comp (Cobham.const [true]) h₁)
        (cobham_pair_comp (Cobham.const [false]) h₂))).of_eq fun _ ↦ rfl

/-! ### The clocked loops are in the algebra -/

theorem cobham_rowSelStep : Cobham fun v : Fin 1 → List Bool ↦ rowSelStep (v 0) := by
  have hst : Cobham fun v : Fin 1 → List Bool ↦ v 0 := Cobham.proj 0
  have hrow := cobham_pairFst_comp hst
  have hjU := cobham_pairFst_comp (cobham_pairSnd_comp hst)
  have hacc := cobham_pairSnd_comp (cobham_pairSnd_comp hst)
  exact (cobham_pair_comp (Cobham.tailFn hrow)
    (cobham_pair_comp (Cobham.appendFn hjU (Cobham.const [true]))
      (Cobham.iteFn (Cobham.headFlagFn hrow)
        (Cobham.appendFn hacc (cobham_delimit_comp hjU)) hacc))).of_eq fun _ ↦ rfl

theorem cobham_rowSelStr : Cobham fun v : Fin 2 → List Bool ↦ rowSelStr (v 0) (v 1) := by
  have hf : Cobham fun w : Fin 2 → List Bool ↦ rowSelStep (w 0) :=
    (Cobham.comp cobham_rowSelStep fun _ : Fin 1 ↦ Cobham.proj 0).of_eq fun _ ↦ rfl
  have he : Cobham fun p : Fin 1 → List Bool ↦ pair (p 0) (pair [] []) :=
    cobham_pair_comp (Cobham.proj 0) (Cobham.const _)
  refine (cobham_pairSnd_comp (cobham_pairSnd_comp (cobham_iter hf he
    (Polynomial.C 2 * Polynomial.X * Polynomial.X + Polynomial.C 6 * Polynomial.X +
      Polynomial.C 6) ?_))).of_eq fun v ↦ rfl
  intro c v
  refine le_trans (length_rowSelStep_iterate_le (v 0) c.length) ?_
  simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X,
    Fin.sum_univ_one]
  set L := c.length + (v 0).length with hL
  have h1 : c.length * (2 * c.length + 2) ≤ L * (2 * L + 2) := Nat.mul_le_mul (by omega) (by omega)
  have h2 : L * (2 * L + 2) = 2 * L * L + 2 * L := by ring
  omega

theorem cobham_hashRowsStep : Cobham fun v : Fin 2 → List Bool ↦ hashRowsStep (v 0) (v 1) := by
  have hw : Cobham fun v : Fin 2 → List Bool ↦ v 0 := Cobham.proj 0
  have hst : Cobham fun v : Fin 2 → List Bool ↦ v 1 := Cobham.proj 1
  exact (cobham_pair_comp (Cobham.dropFn hw (cobham_pairFst_comp hst))
    (Cobham.appendFn (cobham_pairSnd_comp hst)
      (cobham_delimit_comp (Cobham.takeFn hw (cobham_pairFst_comp hst))))).of_eq fun _ ↦ rfl

theorem cobham_hashRowsStr :
    Cobham fun v : Fin 3 → List Bool ↦ hashRowsStr (v 1) (v 0) (v 2) := by
  have hf : Cobham fun x : Fin 3 → List Bool ↦ hashRowsStep (x 1) (x 0) :=
    (Cobham.comp₂ cobham_hashRowsStep (Cobham.proj 1) (Cobham.proj 0)).of_eq fun _ ↦ by simp
  have he : Cobham fun p : Fin 2 → List Bool ↦ pair (p 1) [] :=
    cobham_pair_comp (Cobham.proj 1) (Cobham.const [])
  refine (cobham_pairSnd_comp (cobham_iter hf he
    (Polynomial.C 2 * Polynomial.X * Polynomial.X + Polynomial.C 6 * Polynomial.X +
      Polynomial.C 2) ?_)).of_eq fun v ↦ rfl
  intro c v
  refine le_trans (length_hashRowsStep_iterate_le (v 0) (v 1) c.length) ?_
  simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X,
    Fin.sum_univ_two]
  set L := c.length + ((v 0).length + (v 1).length) with hL
  have h1 : c.length * (2 * (v 0).length + 4) ≤ L * (2 * L + 4) :=
    Nat.mul_le_mul (by omega) (by omega)
  have h2 : L * (2 * L + 4) = 2 * L * L + 4 * L := by ring
  omega

theorem cobham_chooseKStep : Cobham fun v : Fin 2 → List Bool ↦ chooseKStep (v 0) (v 1) := by
  have hkb : Cobham fun v : Fin 2 → List Bool ↦ v 0 := Cobham.proj 0
  have hst : Cobham fun v : Fin 2 → List Bool ↦ v 1 := Cobham.proj 1
  have hc' := cobham_succBits_comp (cobham_pairFst_comp hst)
  have hi' := Cobham.appendFn (cobham_pairFst_comp (cobham_pairSnd_comp hst))
    (Cobham.const [true])
  exact (cobham_pair_comp hc' (cobham_pair_comp hi'
    (Cobham.iteFn (cobham_eqBits_comp hc' hkb) hi'
      (cobham_pairSnd_comp (cobham_pairSnd_comp hst))))).of_eq fun _ ↦ rfl

theorem cobham_chooseKStr : Cobham fun v : Fin 2 → List Bool ↦ chooseKStr (v 0) (v 1) := by
  have hf : Cobham fun x : Fin 2 → List Bool ↦ chooseKStep (x 1) (x 0) :=
    (Cobham.comp₂ cobham_chooseKStep (Cobham.proj 1) (Cobham.proj 0)).of_eq fun _ ↦ by simp
  have he : Cobham fun _ : Fin 1 → List Bool ↦ pair [] (pair [] []) := Cobham.const _
  have hiter := cobham_iter hf he (Polynomial.C 5 * Polynomial.X + Polynomial.C 4) (by
    intro c v
    refine le_trans (length_chooseKStep_iterate_le (v 0) c.length) ?_
    simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X,
      Fin.sum_univ_one]
    omega)
  have hu : Cobham fun v : Fin 2 → List Bool ↦
      pairSnd (pairSnd ((chooseKStep (v 1))^[(true :: true :: v 0).length]
        (pair [] (pair [] [])))) := by
    refine cobham_pairSnd_comp (cobham_pairSnd_comp ?_)
    exact (Cobham.comp₂ hiter (cobham_cons true (cobham_cons true (Cobham.proj 0)))
      (Cobham.proj 1)).of_eq fun _ ↦ by simp
  exact (Cobham.iteFn (Cobham.nonemptyFn hu) hu (Cobham.const [true])).of_eq fun _ ↦ rfl

/-! ### The parity constraints are in the algebra -/

/-- The inner XOR-chain fold: `v 0` is the framed list of remaining selected variables,
`v 1` the auxiliary-variable counter. -/
theorem cobham_xorFold : Cobham fun v : Fin 2 → List Bool ↦
    foldBlocks (accStep xorStepF xorStepH) (pair [] (v 1 ++ [true])) (v 0) := by
  have hf : Cobham fun w : Fin 3 → List Bool ↦ xorStepF (w 0) (w 1) :=
    cobham_xorGadgetU_comp (Cobham.proj 0) (Cobham.tailFn (Cobham.proj 0)) (Cobham.proj 1)
  have hh : Cobham fun w : Fin 3 → List Bool ↦ xorStepH (w 0) (w 1) :=
    (Cobham.appendFn (Cobham.proj 0) (Cobham.const [true])).of_eq fun _ ↦ rfl
  have hout : Cobham fun _ : Fin 1 → List Bool ↦ ([] : List Bool) := Cobham.empty
  have hctr : Cobham fun p : Fin 1 → List Bool ↦ p 0 ++ [true] :=
    Cobham.appendFn (Cobham.proj 0) (Cobham.const [true])
  exact (cobham_foldAcc' hf hh hout hctr 0 (by
    intro w
    simp only [xorStepH, List.length_append, List.length_singleton, Polynomial.eval_zero]
    omega)).of_eq fun v ↦ rfl

theorem cobham_parityCnfStr :
    Cobham fun v : Fin 3 → List Bool ↦ parityCnfStr (v 0) (v 1) (v 2) := by
  have hm : Cobham fun v : Fin 3 → List Bool ↦ v 0 := Cobham.proj 0
  have htU : Cobham fun v : Fin 3 → List Bool ↦ v 1 := Cobham.proj 1
  have hrow : Cobham fun v : Fin 3 → List Bool ↦ v 2 := Cobham.proj 2
  have hsel : Cobham fun v : Fin 3 → List Bool ↦ rowSelStr (v 0) (v 2) :=
    (Cobham.comp₂ cobham_rowSelStr hm hrow).of_eq fun _ ↦ by simp
  have hbt : Cobham fun v : Fin 3 → List Bool ↦ bitAt (v 0) (v 2) :=
    (Cobham.comp₂ Cobham.bitAtFn hm hrow).of_eq fun _ ↦ by simp
  have hx₀ := cobham_pairFst_comp hsel
  have hrest := cobham_pairSnd_comp hsel
  have hx₁ := cobham_pairFst_comp hrest
  have hrest' := cobham_pairSnd_comp hrest
  have hr : Cobham fun v : Fin 3 → List Bool ↦
      foldBlocks (accStep xorStepF xorStepH) (pair [] (v 1 ++ [true]))
        (pairSnd (pairSnd (rowSelStr (v 0) (v 2)))) :=
    (Cobham.comp₂ cobham_xorFold hrest' htU).of_eq fun _ ↦ by simp
  have hctr := cobham_pairSnd_comp hr
  have hlong := cobham_pair_comp
    (Cobham.appendFn (Cobham.appendFn (cobham_xorGadgetU_comp htU hx₀ hx₁)
        (cobham_pairFst_comp hr))
      (cobham_delimit_comp (cobham_delimit_comp
        (cobham_pair_comp hbt (Cobham.tailFn hctr)))))
    (Cobham.takeFn hm (Cobham.dropFn htU hctr))
  have hone := cobham_pair_comp
    (cobham_delimit_comp (cobham_delimit_comp (cobham_pair_comp hbt hx₀))) (Cobham.const [])
  have hzero := cobham_pair_comp
    (Cobham.iteFn hbt (Cobham.const (delimit [])) (Cobham.const [])) (Cobham.const [])
  exact (Cobham.iteFn (Cobham.nonemptyFn hsel)
    (Cobham.iteFn (Cobham.nonemptyFn hrest) hlong hone) hzero).of_eq fun _ ↦ rfl

theorem length_pairSnd_caseBit₀_le (s x y : List Bool) (N : ℕ)
    (hx : (pairSnd x).length ≤ N) (hy : (pairSnd y).length ≤ N) :
    (pairSnd (caseBit₀ s x y)).length ≤ N := by
  rcases caseBit₀_cases s x y with h | h <;> rw [h] <;> assumption

theorem length_pairSnd_parityCnfStr_le (m tU row : List Bool) :
    (pairSnd (parityCnfStr m tU row)).length ≤ m.length := by
  simp only [parityCnfStr]
  refine length_pairSnd_caseBit₀_le _ _ _ _ (length_pairSnd_caseBit₀_le _ _ _ _ ?_ ?_) ?_
  · rw [pairSnd_pair]
    simp only [List.length_take, List.length_drop]
    omega
  · rw [pairSnd_pair]; simp
  · rw [pairSnd_pair]; simp

/-! ### Shortening a clause is in the algebra -/

/-- The inner OR-chain fold: `v 0` is the framed list of the remaining literals, `v 1` the
auxiliary-variable counter (unary) and `v 2` the previous literal. -/
theorem cobham_orFold : Cobham fun v : Fin 3 → List Bool ↦
    foldBlocks (accStep orStepF orStepH) (pair [] (pair (v 1 ++ [true]) (v 2))) (v 0) := by
  have hc : Cobham fun w : Fin 4 → List Bool ↦ pairFst (w 0) :=
    cobham_pairFst_comp (Cobham.proj 0)
  have hf : Cobham fun w : Fin 4 → List Bool ↦ orStepF (w 0) (w 1) :=
    cobham_orGadgetU_comp hc (cobham_pair_comp (Cobham.const [true]) (Cobham.tailFn hc))
      (cobham_pairSnd_comp (Cobham.proj 0))
  have hh : Cobham fun w : Fin 4 → List Bool ↦ orStepH (w 0) (w 1) :=
    cobham_pair_comp (Cobham.appendFn hc (Cobham.const [true])) (Cobham.proj 1)
  have hout : Cobham fun _ : Fin 2 → List Bool ↦ ([] : List Bool) := Cobham.empty
  have hctr : Cobham fun p : Fin 2 → List Bool ↦ pair (p 0 ++ [true]) (p 1) :=
    cobham_pair_comp (Cobham.appendFn (Cobham.proj 0) (Cobham.const [true])) (Cobham.proj 1)
  exact (cobham_foldAcc' hf hh hout hctr (Polynomial.C 2) (by
    intro w
    have h1 := two_mul_length_pairFst_le (w 0)
    simp only [orStepH, pair_length, List.length_append, List.length_singleton,
      Polynomial.eval_C]
    omega)).of_eq fun v ↦ rfl

theorem cobham_shortenClauseStr :
    Cobham fun v : Fin 2 → List Bool ↦ shortenClauseStr (v 0) (v 1) := by
  have htU : Cobham fun v : Fin 2 → List Bool ↦ v 0 := Cobham.proj 0
  have hc : Cobham fun v : Fin 2 → List Bool ↦ v 1 := Cobham.proj 1
  have hl₁ := cobham_pairFst_comp hc
  have hr₁ := cobham_pairSnd_comp hc
  have hl₂ := cobham_pairFst_comp hr₁
  have hr₂ := cobham_pairSnd_comp hr₁
  have hl₃ := cobham_pairFst_comp hr₂
  have hr₃ := cobham_pairSnd_comp hr₂
  have hr : Cobham fun v : Fin 2 → List Bool ↦
      foldBlocks (accStep orStepF orStepH)
        (pair [] (pair (v 0 ++ [true]) (pairFst (pairSnd (pairSnd (v 1))))))
        (pairSnd (pairSnd (pairSnd (v 1)))) :=
    (Cobham.comp₃ cobham_orFold hr₃ htU hl₃).of_eq fun _ ↦ by simp
  have hctr := cobham_pairSnd_comp hr
  have hlong := cobham_pair_comp
    (Cobham.appendFn (Cobham.appendFn (cobham_orGadgetU_comp htU hl₁ hl₂)
        (cobham_pairFst_comp hr))
      (cobham_delimit_comp (cobham_frame2_comp
        (cobham_pair_comp (Cobham.const [true]) (Cobham.tailFn (cobham_pairFst_comp hctr)))
        (cobham_pairSnd_comp hctr))))
    (Cobham.takeFn hc (Cobham.dropFn htU (cobham_pairFst_comp hctr)))
  exact (Cobham.iteFn (Cobham.nonemptyFn hr₃) hlong
    (cobham_pair_comp (cobham_delimit_comp hc) (Cobham.const []))).of_eq fun _ ↦ rfl

theorem length_pairSnd_shortenClauseStr_le (tU c : List Bool) :
    (pairSnd (shortenClauseStr tU c)).length ≤ c.length := by
  simp only [shortenClauseStr]
  refine length_pairSnd_caseBit₀_le _ _ _ _ ?_ ?_
  · rw [pairSnd_pair]
    simp only [List.length_take, List.length_drop]
    omega
  · rw [pairSnd_pair]; simp

/-! ### The two outer folds and the final composition -/

theorem cobham_shortenAllStr :
    Cobham fun v : Fin 2 → List Bool ↦ shortenAllStr (v 1) (v 0) := by
  have hsc : Cobham fun w : Fin 3 → List Bool ↦ shortenClauseStr (w 0) (w 1) :=
    (Cobham.comp₂ cobham_shortenClauseStr (Cobham.proj 0) (Cobham.proj 1)).of_eq fun _ ↦ by simp
  have hf : Cobham fun w : Fin 3 → List Bool ↦ shortenStepF (w 0) (w 1) :=
    cobham_pairFst_comp hsc
  have hh : Cobham fun w : Fin 3 → List Bool ↦ shortenStepH (w 0) (w 1) :=
    Cobham.appendFn (Cobham.proj 0) (cobham_pairSnd_comp hsc)
  have hout : Cobham fun _ : Fin 1 → List Bool ↦ ([] : List Bool) := Cobham.empty
  have hctr : Cobham fun p : Fin 1 → List Bool ↦ p 0 := Cobham.proj 0
  exact (cobham_foldAcc' hf hh hout hctr 0 (by
    intro w
    have h1 := length_pairSnd_shortenClauseStr_le (w 0) (w 1)
    simp only [shortenStepH, List.length_append, Polynomial.eval_zero]
    omega)).of_eq fun v ↦ rfl

theorem cobham_isolateRowsStr :
    Cobham fun v : Fin 3 → List Bool ↦ isolateRowsStr (v 1) (v 2) (v 0) := by
  have hp : Cobham fun w : Fin 4 → List Bool ↦ parityCnfStr (w 2) (w 0) (w 1) :=
    (Cobham.comp₃ cobham_parityCnfStr (Cobham.proj 2) (Cobham.proj 0)
      (Cobham.proj 1)).of_eq fun _ ↦ by simp
  have hf : Cobham fun w : Fin 4 → List Bool ↦ rowStepF (w 2) (w 0) (w 1) :=
    cobham_pairFst_comp hp
  have hh : Cobham fun w : Fin 4 → List Bool ↦ rowStepH (w 2) (w 0) (w 1) :=
    Cobham.appendFn (Cobham.proj 0) (cobham_pairSnd_comp hp)
  have hout : Cobham fun _ : Fin 2 → List Bool ↦ ([] : List Bool) := Cobham.empty
  have hctr : Cobham fun p : Fin 2 → List Bool ↦ p 1 := Cobham.proj 1
  exact (cobham_foldAcc' hf hh hout hctr Polynomial.X (by
    intro w
    have h1 := length_pairSnd_parityCnfStr_le (w 2) (w 0) (w 1)
    have h2 : (Fin.tail (Fin.tail w) 0).length = (w 2).length := rfl
    simp only [rowStepH, List.length_append, Polynomial.eval_X, Fin.sum_univ_two]
    omega)).of_eq fun v ↦ rfl

theorem cobham_numVarsStr : Cobham fun v : Fin 1 → List Bool ↦ numVarsStr (v 0) := by
  have h := numVarsStr_mem_FP
  rw [← CobhamFP_eq_FP] at h
  exact h

theorem isolateStr_mem_FP : isolateStr ∈ FP := by
  rw [← CobhamFP_eq_FP]
  show Cobham fun v : Fin 1 → List Bool ↦ isolateStr (v 0)
  have hz : Cobham fun v : Fin 1 → List Bool ↦ v 0 := Cobham.proj 0
  have ht := cobham_pairFst_comp hz
  have hkb := cobham_pairFst_comp (cobham_pairSnd_comp hz)
  have hhb := cobham_pairSnd_comp (cobham_pairSnd_comp hz)
  have hm : Cobham fun v : Fin 1 → List Bool ↦ numVarsStr (pairFst (v 0)) :=
    cobham_comp₁ cobham_numVarsStr ht
  have hs : Cobham fun v : Fin 1 → List Bool ↦
      shortenAllStr (numVarsStr (pairFst (v 0))) (pairFst (v 0)) :=
    (Cobham.comp₂ cobham_shortenAllStr ht hm).of_eq fun _ ↦ by simp
  have hk : Cobham fun v : Fin 1 → List Bool ↦
      chooseKStr (numVarsStr (pairFst (v 0))) (pairFst (pairSnd (v 0))) :=
    (Cobham.comp₂ cobham_chooseKStr hm hkb).of_eq fun _ ↦ by simp
  have hrows : Cobham fun v : Fin 1 → List Bool ↦
      hashRowsStr (true :: numVarsStr (pairFst (v 0)))
        (chooseKStr (numVarsStr (pairFst (v 0))) (pairFst (pairSnd (v 0))))
        (pairSnd (pairSnd (v 0))) :=
    (Cobham.comp₃ cobham_hashRowsStr hk (cobham_cons true hm) hhb).of_eq fun _ ↦ by simp
  have hr : Cobham fun v : Fin 1 → List Bool ↦
      isolateRowsStr (numVarsStr (pairFst (v 0)))
        (pairSnd (shortenAllStr (numVarsStr (pairFst (v 0))) (pairFst (v 0))))
        (hashRowsStr (true :: numVarsStr (pairFst (v 0)))
          (chooseKStr (numVarsStr (pairFst (v 0))) (pairFst (pairSnd (v 0))))
          (pairSnd (pairSnd (v 0)))) :=
    (Cobham.comp₃ cobham_isolateRowsStr hrows hm (cobham_pairSnd_comp hs)).of_eq fun _ ↦ by simp
  exact (cobham_pair_comp (Cobham.appendFn (cobham_pairFst_comp hs) (cobham_pairFst_comp hr))
    (cobham_pairSnd_comp hr)).of_eq fun _ ↦ rfl

end SparseGcd
