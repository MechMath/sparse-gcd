import SparseDivComplexity.BridgeString

/-!
# Correctness of the bridge string transformation

The decoded output of `bridgeStr` is exactly the term-list algorithm `bridgeTerms` of
`BridgeTerms.lean` on decodable well-formed inputs, and the fixed `DIV` instance otherwise.

## Proof architecture

Every string the algorithm manipulates is a framed list of *term blocks* `pair c e` with numerals
`c`, `e`. We work with the explicit representation `ts : List (List Bool × List Bool)` of such a
list: `frameTerms ts` is the framed string and `decodeTerms ts` the decoded term list. The string
operations are then shown to act on this representation, and the decoded effect is computed:

* `insertStr` mirrors `insertTermS`, a copy of `insertTerm` on numeral pairs, whose decoding is
  `insertTerm` (by the specifications of `ltBits`, `eqBits`, `isZeroBits`, `addModStr`);
* `normalizeStr` is therefore a left fold of `insertTerm`, which equals `normalize` by uniqueness
  of canonical forms (`normalize_of_normalized`, `normalize_eq_of_toPoly_eq`);
* `fTermsStr`, `gTermsStr` decode to `fTermsRaw`, `gTermsRaw` by the specifications of `mulBits`,
  `addBits`, `succBits`, `negModStr`.
-/

open Complexity SparseDiv.StringArith

namespace SparseDiv

/-! ### Framed lists of term blocks -/

/-- The term block of a numeral pair. -/
def blk (t : List Bool × List Bool) : List Bool := pair t.1 t.2

/-- The framed string of a list of numeral pairs. -/
def frameTerms (ts : List (List Bool × List Bool)) : List Bool := frame (ts.map blk)

/-- The term list denoted by a list of numeral pairs. -/
def decodeTerms (ts : List (List Bool × List Bool)) : Terms :=
  ts.map fun t ↦ (decNat t.1, decNat t.2)

private theorem coefOf_blk (t : List Bool × List Bool) : coefOf (blk t) = t.1 := by
  simp [coefOf, blk]

private theorem expOf_blk (t : List Bool × List Bool) : expOf (blk t) = t.2 := by
  simp [expOf, blk]

private theorem frameTerms_nil : frameTerms [] = [] := rfl

private theorem frameTerms_append (ts ts' : List (List Bool × List Bool)) :
    frameTerms (ts ++ ts') = frameTerms ts ++ frameTerms ts' := by
  simp [frameTerms, frame]

private theorem frameTerms_singleton (t : List Bool × List Bool) :
    frameTerms [t] = delimit (blk t) := by
  simp [frameTerms, frame]

private theorem frameTerms_eq_nil_iff (ts : List (List Bool × List Bool)) :
    frameTerms ts = [] ↔ ts = [] := by
  cases ts with
  | nil => simp [frameTerms_nil]
  | cons t ts =>
    simp only [List.cons_ne_nil, iff_false]
    rw [← List.singleton_append, frameTerms_append, frameTerms_singleton]
    intro h
    have := congrArg List.length h
    simp at this

private theorem decodeTerms_nil : decodeTerms [] = [] := rfl

private theorem decodeTerms_cons (t : List Bool × List Bool) (ts : List (List Bool × List Bool)) :
    decodeTerms (t :: ts) = (decNat t.1, decNat t.2) :: decodeTerms ts := rfl

private theorem decodeTerms_append (ts ts' : List (List Bool × List Bool)) :
    decodeTerms (ts ++ ts') = decodeTerms ts ++ decodeTerms ts' := by
  simp [decodeTerms]

private theorem decodeTerms_eq_nil_iff (ts : List (List Bool × List Bool)) :
    decodeTerms ts = [] ↔ ts = [] := by
  simp [decodeTerms]

/-- Well-formedness of the decoded list, elementwise. -/
private theorem wf_decodeTerms_iff (p : ℕ) (ts : List (List Bool × List Bool)) :
    WFTerms p (decodeTerms ts) ↔ ∀ t ∈ ts, decNat t.1 < p := by
  simp only [WFTerms, decodeTerms, List.forall_mem_map]

/-- Folding over the blocks of a framed list is folding over the list. -/
private theorem foldBlocks_frameTerms (step : List Bool → List Bool → List Bool)
    (init : List Bool) (ts : List (List Bool × List Bool)) :
    foldBlocks step init (frameTerms ts) = ts.foldl (fun acc t ↦ step acc (blk t)) init := by
  rw [frameTerms, foldBlocks_frame, List.foldl_map]

/-- Mapping over the blocks of a framed list of term blocks. -/
private theorem mapBlocks_frameTerms (f : List Bool → List Bool)
    (ts : List (List Bool × List Bool)) :
    mapBlocks f (frameTerms ts) = frame (ts.map fun t ↦ f (blk t)) := by
  rw [frameTerms, mapBlocks_frame, List.map_map]
  rfl

/-! ### Decoding framed term lists -/

private theorem decTermList_map_blk (ts : List (List Bool × List Bool)) :
    decTermList (ts.map blk) = some (decodeTerms ts) := by
  induction ts with
  | nil => rfl
  | cons t ts ih => simp [decTermList, decTerm, blk, ih, decodeTerms_cons]

private theorem decTerms_frameTerms (ts : List (List Bool × List Bool)) :
    decTerms (frameTerms ts) = some (decodeTerms ts) := by
  rw [decTerms, frameTerms, frame, undelimitBlocks_flatten_delimit, Option.bind_some,
    decTermList_map_blk]

/-- Soundness of the fuelled block parser. -/
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

/-- Soundness of the block parser. -/
private theorem eq_frame_of_undelimitBlocks_eq_some {s : List Bool} {bs : List (List Bool)}
    (h : undelimitBlocks s = some bs) : s = frame bs :=
  eq_frame_of_undelimitBlocksAux_eq_some _ h

/-- A list of blocks that all parse as pairs is a list of term blocks. -/
private theorem exists_map_blk_of_forall_isSome {bs : List (List Bool)}
    (h : ∀ b ∈ bs, (unpair? b).isSome) : ∃ ts : List (List Bool × List Bool), bs = ts.map blk := by
  induction bs with
  | nil => exact ⟨[], rfl⟩
  | cons b bs ih =>
    obtain ⟨ts, rfl⟩ := ih fun b' hb' ↦ h b' (List.mem_cons_of_mem _ hb')
    obtain ⟨⟨c, e⟩, hce⟩ := Option.isSome_iff_exists.mp (h b (List.mem_cons_self ..))
    exact ⟨(c, e) :: ts, by rw [eq_pair_of_unpair?_eq_some hce]; rfl⟩

/-- A successfully decoded list of blocks is a list of term blocks. -/
private theorem exists_map_blk_of_decTermList_eq_some :
    ∀ {bs : List (List Bool)} {l : Terms}, decTermList bs = some l →
      ∃ ts : List (List Bool × List Bool), bs = ts.map blk ∧ l = decodeTerms ts
  | [], l, h => by
    simp only [decTermList, Option.some.injEq] at h
    exact ⟨[], rfl, h.symm⟩
  | b :: bs, l, h => by
    rcases hb : decTerm b with _ | t
    · simp [decTermList, hb] at h
    rcases hbs : decTermList bs with _ | ts'
    · simp [decTermList, hb, hbs] at h
    simp [decTermList, hb, hbs] at h
    subst h
    obtain ⟨ts, rfl, rfl⟩ := exists_map_blk_of_decTermList_eq_some hbs
    simp only [decTerm, Option.map_eq_some_iff] at hb
    obtain ⟨⟨c, e⟩, hce, rfl⟩ := hb
    exact ⟨(c, e) :: ts, by rw [eq_pair_of_unpair?_eq_some hce]; rfl, rfl⟩

/-- Structure of a decodable `SparseRoot` instance. -/
private theorem decRootInstance_eq_some_iff {s : List Bool} {p : ℕ} {l : Terms} :
    decRootInstance s = some (p, l) ↔
      ∃ (a : List Bool) (ts : List (List Bool × List Bool)),
        s = pair a (frameTerms ts) ∧ p = decNat a ∧ l = decodeTerms ts := by
  constructor
  · intro h
    rcases hu : unpair? s with _ | ⟨a, r⟩
    · simp [decRootInstance, hu] at h
    · simp only [decRootInstance, hu, Option.bind_some, Option.map_eq_some_iff,
        Prod.mk.injEq] at h
      obtain ⟨l', hl', rfl, rfl⟩ := h
      simp only [decTerms, Option.bind_eq_some_iff] at hl'
      obtain ⟨bs, hbs, hl'⟩ := hl'
      obtain ⟨ts, rfl, rfl⟩ := exists_map_blk_of_decTermList_eq_some hl'
      refine ⟨a, ts, ?_, rfl, rfl⟩
      rw [eq_pair_of_unpair?_eq_some hu, eq_frame_of_undelimitBlocks_eq_some hbs]
      rfl
  · rintro ⟨a, ts, rfl, rfl, rfl⟩
    simp [decRootInstance, decTerms_frameTerms]

/-- Decoding the output shape of the bridge. -/
private theorem decDivInstance_pair_pair (a : List Bool) (F G : List (List Bool × List Bool)) :
    decDivInstance (pair a (pair (frameTerms F) (frameTerms G))) =
      some (decNat a, decodeTerms F, decodeTerms G) := by
  simp [decDivInstance, decTerms_frameTerms]

/-! ### The validity flag -/

private theorem hasBlockFlag_flag (s : List Bool) :
    hasBlockFlag s = [true] ∨ hasBlockFlag s = [false] :=
  Cobham.eqFlag_flag _ _

private theorem validBlocksFlag_flag (s : List Bool) :
    validBlocksFlag s = [true] ∨ validBlocksFlag s = [false] :=
  Cobham.eqFlag_flag _ _

/-- The step of `wfBlocksFlag`. -/
private def wfStep (a acc b : List Bool) : List Bool :=
  andBit acc (andBit (hasBlockFlag b) (ltBits (coefOf b) a))

private theorem foldl_wfStep_flag (a : List Bool) (bs : List (List Bool)) {init : List Bool}
    (hinit : init = [true] ∨ init = [false]) :
    bs.foldl (wfStep a) init = [true] ∨ bs.foldl (wfStep a) init = [false] := by
  induction bs generalizing init with
  | nil => exact hinit
  | cons b bs ih => exact ih (andBit_flag _ _)

private theorem foldl_wfStep_eq_true_iff (a : List Bool) (bs : List (List Bool))
    {init : List Bool} (hinit : init = [true] ∨ init = [false]) :
    bs.foldl (wfStep a) init = [true] ↔
      init = [true] ∧ ∀ b ∈ bs, hasBlockFlag b = [true] ∧ ltBits (coefOf b) a = [true] := by
  induction bs generalizing init with
  | nil => simp
  | cons b bs ih =>
    rw [List.foldl_cons,
      ih (show wfStep a init b = [true] ∨ wfStep a init b = [false] from andBit_flag _ _), wfStep,
      Cobham.andBit_eq_true_iff hinit (andBit_flag _ _),
      Cobham.andBit_eq_true_iff (hasBlockFlag_flag b) (ltBits_flag _ _), List.forall_mem_cons]
    tauto

private theorem wfBlocksFlag_flag (a s : List Bool) :
    wfBlocksFlag a s = [true] ∨ wfBlocksFlag a s = [false] :=
  foldl_wfStep_flag a (blocks s) (Or.inl rfl)

private theorem wfBlocksFlag_frameTerms_eq_true_iff (a : List Bool)
    (ts : List (List Bool × List Bool)) :
    wfBlocksFlag a (frameTerms ts) = [true] ↔ ∀ t ∈ ts, decNat t.1 < decNat a := by
  rw [wfBlocksFlag, frameTerms, foldBlocks_frame,
    show (fun acc b ↦ andBit acc (andBit (hasBlockFlag b) (ltBits (coefOf b) a))) = wfStep a
      from rfl,
    foldl_wfStep_eq_true_iff a _ (Or.inl rfl), List.forall_mem_map]
  simp only [true_and, ltBits_eq_true_iff, hasBlockFlag_eq_true_iff, blk, unpair?_pair,
    Option.isSome_some, coefOf, pairFst_pair]

private theorem validRootFlag_flag (s : List Bool) :
    validRootFlag s = [true] ∨ validRootFlag s = [false] :=
  andBit_flag _ _

/-- The validity flag is exactly decodability plus well-formedness of the coefficients. -/
theorem validRootFlag_eq_true_iff (s : List Bool) :
    validRootFlag s = [true] ↔ ∃ p l, decRootInstance s = some (p, l) ∧ WFTerms p l := by
  rw [validRootFlag, Cobham.andBit_eq_true_iff (hasBlockFlag_flag s) (andBit_flag _ _),
    Cobham.andBit_eq_true_iff (validBlocksFlag_flag _) (wfBlocksFlag_flag _ _),
    hasBlockFlag_eq_true_iff, validBlocksFlag_eq_true_iff]
  constructor
  · rintro ⟨h1, h2, h3⟩
    obtain ⟨⟨a, r⟩, hu⟩ := Option.isSome_iff_exists.mp h1
    obtain rfl := eq_pair_of_unpair?_eq_some hu
    rw [pairSnd_pair] at h2
    rw [pairFst_pair, pairSnd_pair] at h3
    obtain ⟨bs, hbs⟩ := Option.isSome_iff_exists.mp h2
    obtain rfl := eq_frame_of_undelimitBlocks_eq_some hbs
    have hall : ∀ b ∈ bs, (unpair? b).isSome := by
      intro b hb
      rw [wfBlocksFlag, foldBlocks_frame,
        show (fun acc b ↦ andBit acc (andBit (hasBlockFlag b) (ltBits (coefOf b) a))) = wfStep a
          from rfl, foldl_wfStep_eq_true_iff a _ (Or.inl rfl)] at h3
      exact (hasBlockFlag_eq_true_iff b).1 (h3.2 b hb).1
    obtain ⟨ts, rfl⟩ := exists_map_blk_of_forall_isSome hall
    refine ⟨decNat a, decodeTerms ts, decRootInstance_eq_some_iff.2 ⟨a, ts, rfl, rfl, rfl⟩, ?_⟩
    rw [wf_decodeTerms_iff]
    exact (wfBlocksFlag_frameTerms_eq_true_iff a ts).1 h3
  · rintro ⟨p, l, h, hwf⟩
    obtain ⟨a, ts, rfl, rfl, rfl⟩ := decRootInstance_eq_some_iff.1 h
    rw [pairFst_pair, pairSnd_pair]
    refine ⟨by simp, ?_, ?_⟩
    · rw [frameTerms, frame, undelimitBlocks_flatten_delimit]
      rfl
    · exact (wfBlocksFlag_frameTerms_eq_true_iff a ts).2 ((wf_decodeTerms_iff _ _).1 hwf)

theorem bridgeStr_eq_noInstance_of_decRootInstance_eq_none {s : List Bool}
    (h : decRootInstance s = none) : bridgeStr s = noInstance := by
  rcases validRootFlag_flag s with hv | hv
  · obtain ⟨p, l, hs, -⟩ := (validRootFlag_eq_true_iff s).1 hv
    rw [h] at hs
    cases hs
  · rw [bridgeStr, hv, caseBit₀_cons, Bool.cond_false]

theorem bridgeStr_eq_noInstance_of_not_wf {s : List Bool} {p : ℕ} {l : Terms}
    (h : decRootInstance s = some (p, l)) (hwf : ¬ WFTerms p l) : bridgeStr s = noInstance := by
  rcases validRootFlag_flag s with hv | hv
  · obtain ⟨p', l', hs, hwf'⟩ := (validRootFlag_eq_true_iff s).1 hv
    rw [h] at hs
    simp only [Option.some.injEq, Prod.mk.injEq] at hs
    obtain ⟨rfl, rfl⟩ := hs
    exact absurd hwf' hwf
  · rw [bridgeStr, hv, caseBit₀_cons, Bool.cond_false]

/-! ### Insertion -/

/-- Selecting on a flag. -/
private theorem caseBit₀_of_flag {x : List Bool} (hx : x = [true] ∨ x = [false])
    (u v : List Bool) : caseBit₀ x u v = if x = [true] then u else v := by
  rcases hx with rfl | rfl <;> simp

/-- The optional block of the inserted term. -/
private theorem append_caseBit₀_isZeroBits (ts : List (List Bool × List Bool))
    (c e : List Bool) :
    frameTerms ts ++ caseBit₀ (isZeroBits c) [] (delimit (pair c e)) =
      frameTerms (ts ++ if isZeroBits c = [true] then [] else [(c, e)]) := by
  rw [caseBit₀_of_flag (isZeroBits_flag c)]
  split_ifs <;> simp [frameTerms_append, frameTerms_singleton, blk]

/-- String-level copy of `insertTerm` on lists of numeral pairs. -/
private def insertTermS (a c e : List Bool) :
    List (List Bool × List Bool) → List (List Bool × List Bool)
  | [] => if isZeroBits c = [true] then [] else [(c, e)]
  | (c', e') :: rest =>
    if ltBits e e' = [true] then
      (if isZeroBits c = [true] then (c', e') :: rest else (c, e) :: (c', e') :: rest)
    else if eqBits e e' = [true] then
      (if isZeroBits (addModStr a c c') = [true] then rest else (addModStr a c c', e) :: rest)
    else (c', e') :: insertTermS a c e rest

/-- Once the term has been inserted, the remaining blocks are copied. -/
private theorem foldl_insertStep_true (a c e : List Bool) (ts₀ ts : List (List Bool × List Bool)) :
    ts.foldl (fun st t ↦ insertStep a c e st (blk t)) (pair [true] (frameTerms ts₀)) =
      pair [true] (frameTerms (ts₀ ++ ts)) := by
  induction ts generalizing ts₀ with
  | nil => simp
  | cons t ts ih =>
    rw [List.foldl_cons]
    have hstep : insertStep a c e (pair [true] (frameTerms ts₀)) (blk t) =
        pair [true] (frameTerms (ts₀ ++ [t])) := by
      simp [insertStep, frameTerms_append, frameTerms_singleton]
    rw [hstep, ih, List.append_assoc, List.singleton_append]

/-- The fold state before the term has been inserted. -/
private def insFold (a c e : List Bool) (ts₀ ts : List (List Bool × List Bool)) : List Bool :=
  ts.foldl (fun st t ↦ insertStep a c e st (blk t)) (pair [false] (frameTerms ts₀))

/-- Finishing the insertion from the fold state (the body of `insertStr`). -/
private def insFinish (c e r : List Bool) : List Bool :=
  caseBit₀ (pairFst r) (pairSnd r) (pairSnd r ++ caseBit₀ (isZeroBits c) [] (delimit (pair c e)))

private theorem insFinish_true (c e x : List Bool) : insFinish c e (pair [true] x) = x := by
  simp [insFinish]

private theorem delimit_pair_eq_frameTerms (c e : List Bool) :
    delimit (pair c e) = frameTerms [(c, e)] :=
  (frameTerms_singleton (c, e)).symm

/-- Before the term has been inserted, the fold behaves as `insertTermS`. -/
private theorem insFinish_insFold (a c e : List Bool) (ts₀ ts : List (List Bool × List Bool)) :
    insFinish c e (insFold a c e ts₀ ts) = frameTerms (ts₀ ++ insertTermS a c e ts) := by
  induction ts generalizing ts₀ with
  | nil =>
    simp only [insFold, List.foldl_nil, insFinish, pairFst_pair, pairSnd_pair, caseBit₀_cons,
      Bool.cond_false, insertTermS]
    exact append_caseBit₀_isZeroBits ts₀ c e
  | cons t ts ih =>
    obtain ⟨c', e'⟩ := t
    have hstep : insertStep a c e (pair [false] (frameTerms ts₀)) (blk (c', e')) =
        caseBit₀ (ltBits e e')
          (pair [true] (frameTerms ts₀ ++ caseBit₀ (isZeroBits c) [] (delimit (pair c e)) ++
            delimit (pair c' e')))
          (caseBit₀ (eqBits e e')
            (pair [true] (frameTerms ts₀ ++ caseBit₀ (isZeroBits (addModStr a c c')) []
              (delimit (pair (addModStr a c c') e))))
            (pair [false] (frameTerms ts₀ ++ delimit (pair c' e')))) := by
      simp only [insertStep, blk, coefOf, expOf, pairFst_pair, pairSnd_pair, caseBit₀_cons,
        Bool.cond_false]
    rw [insFold, List.foldl_cons, hstep, caseBit₀_of_flag (ltBits_flag e e'),
      caseBit₀_of_flag (eqBits_flag e e'), append_caseBit₀_isZeroBits,
      append_caseBit₀_isZeroBits, delimit_pair_eq_frameTerms c' e']
    simp only [insertTermS]
    split_ifs with h₁ h₂ h₃ h₄
    · -- `e < e'`, `c = 0`: the block is copied, the term is dropped.
      rw [← frameTerms_append, foldl_insertStep_true, insFinish_true]
      simp
    · -- `e < e'`, `c ≠ 0`: the term goes in front of the block.
      rw [← frameTerms_append, foldl_insertStep_true, insFinish_true]
      simp
    · -- `e = e'`, merged coefficient zero: both disappear.
      rw [foldl_insertStep_true, insFinish_true]
      simp
    · -- `e = e'`, merged coefficient nonzero.
      rw [foldl_insertStep_true, insFinish_true]
      simp
    · -- `e > e'`: the block is copied and the fold continues.
      have := ih (ts₀ ++ [(c', e')])
      rw [insFold] at this
      rw [← frameTerms_append, this]
      simp

/-- `insertStr` acts on framed lists as `insertTermS`. -/
private theorem insertStr_frameTerms (a c e : List Bool) (ts : List (List Bool × List Bool)) :
    insertStr a c e (frameTerms ts) = frameTerms (insertTermS a c e ts) := by
  have := insFinish_insFold a c e [] ts
  rw [insFold, insFinish, frameTerms_nil, List.nil_append] at this
  rw [insertStr, foldBlocks_frameTerms]
  exact this

/-- Insertion of a residue preserves residues. -/
private theorem wf_insertTerm {p : ℕ} (hp : 0 < p) (c e : ℕ) {l : Terms} (hl : WFTerms p l) :
    WFTerms p (insertTerm p c e l) := by
  induction l with
  | nil =>
    simp only [insertTerm]
    split_ifs
    · simp [WFTerms]
    · simp [WFTerms, Nat.mod_lt _ hp]
  | cons t l ih =>
    obtain ⟨c', e'⟩ := t
    have hl' : WFTerms p l := fun t ht ↦ hl t (List.mem_cons_of_mem _ ht)
    have hc' : c' < p := hl (c', e') (List.mem_cons_self ..)
    simp only [insertTerm]
    split_ifs
    · exact hl
    · intro t ht
      rcases List.mem_cons.mp ht with rfl | ht
      · exact Nat.mod_lt _ hp
      · exact hl t ht
    · exact hl'
    · intro t ht
      rcases List.mem_cons.mp ht with rfl | ht
      · exact Nat.mod_lt _ hp
      · exact hl' t ht
    · intro t ht
      rcases List.mem_cons.mp ht with rfl | ht
      · exact hc'
      · exact ih hl' t ht

/-- The decoding of `insertTermS` is `insertTerm` (for residue coefficients). -/
private theorem decodeTerms_insertTermS (a c e : List Bool) {ts : List (List Bool × List Bool)}
    (hc : decNat c < decNat a) (hts : ∀ t ∈ ts, decNat t.1 < decNat a) :
    decodeTerms (insertTermS a c e ts) =
      insertTerm (decNat a) (decNat c) (decNat e) (decodeTerms ts) := by
  induction ts with
  | nil =>
    simp only [insertTermS, decodeTerms_nil, insertTerm, Nat.mod_eq_of_lt hc,
      isZeroBits_eq_true_iff]
    split_ifs <;> rfl
  | cons t ts ih =>
    obtain ⟨c', e'⟩ := t
    have hc' : decNat c' < decNat a := hts (c', e') (List.mem_cons_self ..)
    have hts' : ∀ t ∈ ts, decNat t.1 < decNat a := fun t ht ↦ hts t (List.mem_cons_of_mem _ ht)
    simp only [insertTermS, decodeTerms_cons, insertTerm, ltBits_eq_true_iff, eqBits_eq_true_iff,
      isZeroBits_eq_true_iff, decNat_addModStr a c c' hc hc', Nat.mod_eq_of_lt hc]
    split_ifs <;> simp [decodeTerms_cons, ih hts', decNat_addModStr a c c' hc hc']

/-! ### Normalization -/

/-- The string normalization on lists of numeral pairs: a left fold of `insertTermS`. -/
def normalizeS (a : List Bool) (ts : List (List Bool × List Bool)) :
    List (List Bool × List Bool) :=
  ts.foldl (fun acc t ↦ insertTermS a t.1 t.2 acc) []

private theorem foldl_insertStr_frameTerms (a : List Bool)
    (ts₀ ts : List (List Bool × List Bool)) :
    ts.foldl (fun acc t ↦ insertStr a t.1 t.2 acc) (frameTerms ts₀) =
      frameTerms (ts.foldl (fun acc t ↦ insertTermS a t.1 t.2 acc) ts₀) := by
  induction ts generalizing ts₀ with
  | nil => rfl
  | cons t ts ih => rw [List.foldl_cons, List.foldl_cons, insertStr_frameTerms, ih]

/-- `normalizeStr` acts on framed lists as `normalizeS`. -/
theorem normalizeStr_frameTerms (a : List Bool) (ts : List (List Bool × List Bool)) :
    normalizeStr a (frameTerms ts) = frameTerms (normalizeS a ts) := by
  rw [normalizeStr, foldBlocks_frameTerms]
  simp only [coefOf_blk, expOf_blk]
  exact foldl_insertStr_frameTerms a [] ts

/-- The left fold of `insertTerm` over a term list. -/
def normalizeL (p : ℕ) (l : Terms) : Terms :=
  l.foldl (fun acc t ↦ insertTerm p t.1 t.2 acc) []

private theorem decodeTerms_foldl_insertTermS (a : List Bool)
    (ts₀ ts : List (List Bool × List Bool)) (h₀ : ∀ t ∈ ts₀, decNat t.1 < decNat a)
    (hts : ∀ t ∈ ts, decNat t.1 < decNat a) :
    decodeTerms (ts.foldl (fun acc t ↦ insertTermS a t.1 t.2 acc) ts₀) =
      (decodeTerms ts).foldl (fun acc t ↦ insertTerm (decNat a) t.1 t.2 acc) (decodeTerms ts₀) := by
  induction ts generalizing ts₀ with
  | nil => rfl
  | cons t ts ih =>
    have ht : decNat t.1 < decNat a := hts t (List.mem_cons_self ..)
    have hts' : ∀ t ∈ ts, decNat t.1 < decNat a := fun t ht ↦ hts t (List.mem_cons_of_mem _ ht)
    have hp : 0 < decNat a := by omega
    have h₀' : ∀ t' ∈ insertTermS a t.1 t.2 ts₀, decNat t'.1 < decNat a := by
      rw [← wf_decodeTerms_iff, decodeTerms_insertTermS a t.1 t.2 ht h₀]
      exact wf_insertTerm hp _ _ ((wf_decodeTerms_iff _ _).2 h₀)
    rw [List.foldl_cons, decodeTerms_cons, List.foldl_cons, ih _ h₀' hts',
      decodeTerms_insertTermS a t.1 t.2 ht h₀]

/-- The decoding of `normalizeS` is the left fold of `insertTerm`. -/
theorem decodeTerms_normalizeS (a : List Bool) {ts : List (List Bool × List Bool)}
    (hts : ∀ t ∈ ts, decNat t.1 < decNat a) :
    decodeTerms (normalizeS a ts) = normalizeL (decNat a) (decodeTerms ts) :=
  decodeTerms_foldl_insertTermS a [] ts (by simp) hts

/-- Folding `insertTerm` from a canonical accumulator stays canonical and adds the polynomial. -/
private theorem normalized_foldl_insertTerm {p : ℕ} (hp : 0 < p) (l : Terms) {acc : Terms}
    (hacc : Normalized p acc) :
    Normalized p (l.foldl (fun acc t ↦ insertTerm p t.1 t.2 acc) acc) ∧
      toPoly p (l.foldl (fun acc t ↦ insertTerm p t.1 t.2 acc) acc) =
        toPoly p acc + toPoly p l := by
  induction l generalizing acc with
  | nil => simp [hacc]
  | cons t l ih =>
    obtain ⟨h1, h2⟩ := ih (normalized_insertTerm hp t.1 t.2 hacc)
    refine ⟨h1, ?_⟩
    rw [List.foldl_cons, h2, toPoly_insertTerm, toPoly_cons]
    ring

/-- **The left fold of `insertTerm` is `normalize`** (uniqueness of canonical forms). -/
theorem normalizeL_eq_normalize {p : ℕ} (hp : 0 < p) (l : Terms) :
    normalizeL p l = normalize p l := by
  obtain ⟨h1, h2⟩ := normalized_foldl_insertTerm hp l (acc := []) ⟨List.Pairwise.nil, by simp⟩
  rw [toPoly_nil, zero_add] at h2
  unfold normalizeL
  rw [← normalize_of_normalized hp h1]
  exact normalize_eq_of_toPoly_eq hp h2

/-- Well-formedness modulo `0` forces the empty list. -/
private theorem eq_nil_of_wf_zero {l : Terms} (h : WFTerms 0 l) : l = [] := by
  cases l with
  | nil => rfl
  | cons t l => exact absurd (h t (List.mem_cons_self ..)) (Nat.not_lt_zero _)

private theorem normalizeL_eq_normalize_of_wf {p : ℕ} {l : Terms} (hwf : WFTerms p l) :
    normalizeL p l = normalize p l := by
  rcases Nat.eq_zero_or_pos p with rfl | hp
  · rw [eq_nil_of_wf_zero hwf]; rfl
  · exact normalizeL_eq_normalize hp l

/-! ### The displayed terms of `f_P` and `g_P` -/

/-- The numeral pairs displayed by `fTermsStr`. -/
private def fS (a : List Bool) (ts : List (List Bool × List Bool)) :
    List (List Bool × List Bool) :=
  (ts.map fun t ↦ (t.1, mulBits a t.2)) ++ ts.map fun t ↦ (negModStr a t.1, t.2)

/-- The numeral pairs displayed by `gTermsStr`. -/
private def gS (a : List Bool) (ts : List (List Bool × List Bool)) :
    List (List Bool × List Bool) :=
  (ts.map fun t ↦ (t.1, addBits a t.2)) ++ ts.map fun t ↦ (negModStr a t.1, succBits t.2)

private theorem fTermsStr_frameTerms (a : List Bool) (ts : List (List Bool × List Bool)) :
    fTermsStr a (frameTerms ts) = frameTerms (fS a ts) := by
  rw [fTermsStr, mapBlocks_frameTerms, mapBlocks_frameTerms]
  simp only [coefOf_blk, expOf_blk, fS, frameTerms, List.map_append, frame, List.flatten_append,
    List.map_map]
  rfl

private theorem gTermsStr_frameTerms (a : List Bool) (ts : List (List Bool × List Bool)) :
    gTermsStr a (frameTerms ts) = frameTerms (gS a ts) := by
  rw [gTermsStr, mapBlocks_frameTerms, mapBlocks_frameTerms]
  simp only [coefOf_blk, expOf_blk, gS, frameTerms, List.map_append, frame, List.flatten_append,
    List.map_map]
  rfl

private theorem decodeTerms_fS (a : List Bool) {ts : List (List Bool × List Bool)}
    (hts : ∀ t ∈ ts, decNat t.1 < decNat a) :
    decodeTerms (fS a ts) = fTermsRaw (decNat a) (decodeTerms ts) := by
  simp only [fS, fTermsRaw, decodeTerms, List.map_append, List.map_map]
  congr 1
  · exact List.map_congr_left fun t _ ↦ by simp [decNat_mulBits]
  · exact List.map_congr_left fun t ht ↦ by simp [decNat_negModStr a t.1 (hts t ht)]

private theorem decodeTerms_gS (a : List Bool) {ts : List (List Bool × List Bool)}
    (hts : ∀ t ∈ ts, decNat t.1 < decNat a) :
    decodeTerms (gS a ts) = gTermsRaw (decNat a) (decodeTerms ts) := by
  simp only [gS, gTermsRaw, decodeTerms, List.map_append, List.map_map]
  congr 1
  · exact List.map_congr_left fun t _ ↦ by simp [decNat_addBits]
  · exact List.map_congr_left fun t ht ↦ by
      simp [decNat_negModStr a t.1 (hts t ht), decNat_succBits]

private theorem wf_fTermsRaw {p : ℕ} (hp : 0 < p) {l : Terms} (hl : WFTerms p l) :
    WFTerms p (fTermsRaw p l) := by
  intro t ht
  simp only [fTermsRaw, List.mem_append, List.mem_map] at ht
  rcases ht with ⟨s, hs, rfl⟩ | ⟨s, hs, rfl⟩
  · exact hl s hs
  · exact negMod_lt hp _

private theorem wf_gTermsRaw {p : ℕ} (hp : 0 < p) {l : Terms} (hl : WFTerms p l) :
    WFTerms p (gTermsRaw p l) := by
  intro t ht
  simp only [gTermsRaw, List.mem_append, List.mem_map] at ht
  rcases ht with ⟨s, hs, rfl⟩ | ⟨s, hs, rfl⟩
  · exact hl s hs
  · exact negMod_lt hp _

/-! ### Assembly -/

/-- **Correctness of the string algorithm.** On a decodable well-formed instance the output decodes
to exactly the term lists computed by `bridgeTerms`. -/
theorem decDivInstance_bridgeStr {s : List Bool} {p : ℕ} {l : Terms}
    (h : decRootInstance s = some (p, l)) (hwf : WFTerms p l) :
    decDivInstance (bridgeStr s) = some (p, (bridgeTerms p l).1, (bridgeTerms p l).2) := by
  have hflag : validRootFlag s = [true] := (validRootFlag_eq_true_iff s).2 ⟨p, l, h, hwf⟩
  obtain ⟨a, ts, rfl, rfl, rfl⟩ := decRootInstance_eq_some_iff.1 h
  have hts : ∀ t ∈ ts, decNat t.1 < decNat a := (wf_decodeTerms_iff _ _).1 hwf
  simp only [bridgeStr, hflag, caseBit₀_cons, Bool.cond_true, pairFst_pair, pairSnd_pair,
    bridgeBody, normalizeStr_frameTerms]
  have hn : decodeTerms (normalizeS a ts) = normalize (decNat a) (decodeTerms ts) := by
    rw [decodeTerms_normalizeS a hts, normalizeL_eq_normalize_of_wf hwf]
  by_cases hnil : normalizeS a ts = []
  · -- The zero polynomial: the guarded pair.
    rw [hnil, decodeTerms_nil] at hn
    rw [hnil, frameTerms_nil, nonemptyFlag_nil, caseBit₀_nil,
      bridgeTerms_of_normalize_eq_nil hn.symm]
    simp [guardedStr, guardedTerms, decDivInstance]
  · -- A nonzero polynomial: generation and collection.
    have hne : normalize (decNat a) (decodeTerms ts) ≠ [] := by
      rw [← hn]
      exact (decodeTerms_eq_nil_iff _).not.2 hnil
    have hp : 0 < decNat a := by
      have hl : decodeTerms ts ≠ [] := fun h0 ↦ hne (by rw [h0]; rfl)
      obtain ⟨t, r, htr⟩ := List.exists_cons_of_ne_nil hl
      have := hwf t (by rw [htr]; exact List.mem_cons_self ..)
      omega
    have hnf : nonemptyFlag (frameTerms (normalizeS a ts)) = [true] := by
      obtain ⟨b, r, hbr⟩ := List.exists_cons_of_ne_nil ((frameTerms_eq_nil_iff _).not.2 hnil)
      rw [hbr, nonemptyFlag_cons]
    have hwfn : WFTerms (decNat a) (normalize (decNat a) (decodeTerms ts)) :=
      fun t ht ↦ ((normalized_normalize hp _).2 t ht).2
    have hn' : ∀ t ∈ normalizeS a ts, decNat t.1 < decNat a := by
      rw [← wf_decodeTerms_iff, hn]
      exact hwfn
    have hf : ∀ t ∈ fS a (normalizeS a ts), decNat t.1 < decNat a := by
      rw [← wf_decodeTerms_iff, decodeTerms_fS a hn', hn]
      exact wf_fTermsRaw hp hwfn
    have hg : ∀ t ∈ gS a (normalizeS a ts), decNat t.1 < decNat a := by
      rw [← wf_decodeTerms_iff, decodeTerms_gS a hn', hn]
      exact wf_gTermsRaw hp hwfn
    rw [hnf, caseBit₀_cons, Bool.cond_true, bridgeTerms_of_normalize_ne_nil hne,
      fTermsStr_frameTerms, gTermsStr_frameTerms, normalizeStr_frameTerms, normalizeStr_frameTerms,
      decDivInstance_pair_pair, decodeTerms_normalizeS a hf, decodeTerms_normalizeS a hg,
      decodeTerms_fS a hn', decodeTerms_gS a hn', hn, normalizeL_eq_normalize hp,
      normalizeL_eq_normalize hp]

end SparseDiv
