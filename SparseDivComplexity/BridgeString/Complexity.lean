import SparseDivComplexity.BridgeString

/-!
# Complexity of the bridge string transformation

`bridgeStr ∈ FP` (through Cobham's characterization `CobhamFP_eq_FP`) and an explicit conservative
output-length bound.

## Method

Cobham membership is built compositionally, mirroring the definitions of `BridgeString.lean`. The
two loops (`mapBlocks`, `foldBlocks`) are handled by `cobham_mapBlocks` / `cobham_foldBlocks` of
`StringArith/Blocks.lean`, which require polynomial length bounds for the block functions. The
growth bound demanded by `cobham_foldBlocks` is uniform in the loop parameters, so for the two
insertion folds (`insertStr`, `normalizeStr`) the parameters are first *packed into the blocks*
(`mapBlocks (fun b ↦ pair b params)`) and the step reads them back with `pairFst`/`pairSnd`; the
packed fold agrees with the original fold on every input.

The length analysis tracks, for the fold inside `insertStr`, the invariant that the accumulator
grows by at most one framed block per processed block plus a one-time budget (the inserted or
merged term), and for the outer folds a per-block budget summed over the blocks. All bounds hold
for *arbitrary* (possibly malformed) inputs; no well-formedness is assumed.
-/

open Complexity SparseDiv.StringArith

namespace SparseDiv

/-! ### Elementary length facts -/

/-- `pairFst` consumes two input bits per output bit. -/
private theorem two_mul_length_pairFst_le : ∀ z : List Bool, 2 * (pairFst z).length ≤ z.length
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

/-- The two components read by `pairFst`/`pairSnd` fit in the string (with the separator). -/
private theorem two_mul_length_pairFst_add_length_pairSnd_le (z : List Bool) :
    2 * (pairFst z).length + (pairSnd z).length ≤ z.length := by
  rcases hu : unpair? z with _ | ⟨x, y⟩
  · have h : pairSnd z = [] := by simp [pairSnd, hu]
    rw [h, List.length_nil, add_zero]
    exact two_mul_length_pairFst_le z
  · rw [eq_pair_of_unpair?_eq_some hu, pairFst_pair, pairSnd_pair, pair_length]
    omega

private theorem length_pairFst_le (z : List Bool) : (pairFst z).length ≤ z.length := by
  have := two_mul_length_pairFst_le z
  omega

private theorem length_coefOf_le (b : List Bool) : (coefOf b).length ≤ b.length :=
  length_pairFst_le b

private theorem length_expOf_le (b : List Bool) : (expOf b).length ≤ b.length :=
  pairSnd_length_le b

/-- A bit dispatch is bounded by any common bound of its two branches. -/
private theorem caseBit₀_length_le_of {s x y : List Bool} {N : ℕ} (hx : x.length ≤ N)
    (hy : y.length ≤ N) : (caseBit₀ s x y).length ≤ N := by
  cases s with
  | nil => exact hy
  | cons b s => cases b <;> simpa

/-- Variant of `caseBit₀_length_le_of` with a fixed prefix length. -/
private theorem add_caseBit₀_length_le_of {s x y : List Bool} {a N : ℕ} (hx : a + x.length ≤ N)
    (hy : a + y.length ≤ N) : a + (caseBit₀ s x y).length ≤ N := by
  cases s with
  | nil => exact hy
  | cons b s => cases b <;> simpa

private theorem length_addModStr_le (p c c' : List Bool) :
    (addModStr p c c').length ≤ c.length + c'.length + p.length + 4 := by
  unfold addModStr
  have h1 := length_addBits_le c c'
  have h2 := length_subBits_le (addBits c c') p
  exact caseBit₀_length_le_of (by omega) (by omega)

private theorem length_negModStr_le (p c : List Bool) :
    (negModStr p c).length ≤ p.length + c.length + 2 := by
  unfold negModStr
  exact caseBit₀_length_le_of (by simp) (length_subBits_le p c)

/-- The framed inserted term `(c, e)` (or nothing when `c = 0`). -/
private theorem length_insBlock_le (c e : List Bool) :
    (caseBit₀ (isZeroBits c) [] (delimit (pair c e))).length ≤
      4 * c.length + 2 * e.length + 6 := by
  refine caseBit₀_length_le_of (by simp) ?_
  rw [delimit_length, pair_length]
  omega

/-! ### Cobham membership of the arithmetic-level pieces -/

private theorem cobham_delimit_comp {n : ℕ} {g : (Fin n → List Bool) → List Bool} (hg : Cobham g) :
    Cobham fun v : Fin n → List Bool ↦ delimit (g v) :=
  (cobham_pair_comp hg (Cobham.const [])).of_eq fun v ↦ by simp [pair]

private theorem cobham_coefOf_comp {n : ℕ} {g : (Fin n → List Bool) → List Bool} (hg : Cobham g) :
    Cobham fun v : Fin n → List Bool ↦ coefOf (g v) :=
  cobham_pairFst_comp hg

private theorem cobham_expOf_comp {n : ℕ} {g : (Fin n → List Bool) → List Bool} (hg : Cobham g) :
    Cobham fun v : Fin n → List Bool ↦ expOf (g v) :=
  cobham_pairSnd_comp hg

private theorem cobham_negModStr_comp {n : ℕ} {gp gc : (Fin n → List Bool) → List Bool}
    (hp : Cobham gp) (hc : Cobham gc) :
    Cobham fun v : Fin n → List Bool ↦ negModStr (gp v) (gc v) :=
  Cobham.iteFn (cobham_isZeroBits_comp hc) (Cobham.const []) (cobham_subBits_comp hp hc)

private theorem cobham_addModStr_comp {n : ℕ} {gp gc gc' : (Fin n → List Bool) → List Bool}
    (hp : Cobham gp) (hc : Cobham gc) (hc' : Cobham gc') :
    Cobham fun v : Fin n → List Bool ↦ addModStr (gp v) (gc v) (gc' v) :=
  Cobham.iteFn (cobham_ltBits_comp (cobham_addBits_comp hc hc') hp) (cobham_addBits_comp hc hc')
    (cobham_subBits_comp (cobham_addBits_comp hc hc') hp)

/-- `insertStep` as a Cobham function of Cobham arguments (parameters `p c e`, state, block). -/
private theorem cobham_insertStep_comp {n : ℕ} {gp gc ge gst gb : (Fin n → List Bool) → List Bool}
    (hp : Cobham gp) (hc : Cobham gc) (he : Cobham ge) (hst : Cobham gst) (hb : Cobham gb) :
    Cobham fun v : Fin n → List Bool ↦ insertStep (gp v) (gc v) (ge v) (gst v) (gb v) := by
  have hins := cobham_pairFst_comp hst
  have hacc := cobham_pairSnd_comp hst
  have hc' := cobham_pairFst_comp hb
  have he' := cobham_pairSnd_comp hb
  have hdb := cobham_delimit_comp hb
  have hX := Cobham.iteFn (cobham_isZeroBits_comp hc) (Cobham.const [])
    (cobham_delimit_comp (cobham_pair_comp hc he))
  have hm := cobham_addModStr_comp hp hc hc'
  have hY := Cobham.iteFn (cobham_isZeroBits_comp hm) (Cobham.const [])
    (cobham_delimit_comp (cobham_pair_comp hm he))
  exact Cobham.iteFn hins (cobham_pair_comp hins (Cobham.appendFn hacc hdb))
    (Cobham.iteFn (cobham_ltBits_comp he he')
      (cobham_pair_comp (Cobham.const [true]) (Cobham.appendFn (Cobham.appendFn hacc hX) hdb))
      (Cobham.iteFn (cobham_eqBits_comp he he')
        (cobham_pair_comp (Cobham.const [true]) (Cobham.appendFn hacc hY))
        (cobham_pair_comp (Cobham.const [false]) (Cobham.appendFn hacc hdb))))

/-! ### The insertion step: crude growth bound and packed form -/

/-- Crude growth of one insertion step, uniform in the state shape. -/
private theorem length_insertStep_le (p c e st b : List Bool) :
    (insertStep p c e st b).length ≤
      st.length + 4 * b.length + 4 * c.length + 4 * p.length + 2 * e.length + 26 := by
  have h1 := two_mul_length_pairFst_add_length_pairSnd_le st
  have h2 := pairSnd_length_le st
  have h3 := two_mul_length_pairFst_le b
  have h4 := length_insBlock_le c e
  have h5 := length_insBlock_le (addModStr p c (coefOf b)) e
  have h6 := length_addModStr_le p c (coefOf b)
  simp only [coefOf] at h5 h6
  simp only [insertStep, coefOf, expOf]
  refine caseBit₀_length_le_of ?_ (caseBit₀_length_le_of ?_ (caseBit₀_length_le_of ?_ ?_))
  · rw [pair_length, List.length_append, delimit_length]
    omega
  · rw [pair_length, List.length_append, List.length_append, delimit_length]
    simp only [List.length_cons, List.length_nil]
    omega
  · rw [pair_length, List.length_append]
    simp only [List.length_cons, List.length_nil]
    omega
  · rw [pair_length, List.length_append, delimit_length]
    simp only [List.length_cons, List.length_nil]
    omega

/-- The insertion step reading its parameters from the packed block
`pair b (pair p (pair c e))`. -/
private def insertStepPacked (st b' : List Bool) : List Bool :=
  insertStep (pairFst (pairSnd b')) (pairFst (pairSnd (pairSnd b')))
    (pairSnd (pairSnd (pairSnd b'))) st (pairFst b')

private theorem insertStepPacked_pair (p c e st b : List Bool) :
    insertStepPacked st (pair b (pair p (pair c e))) = insertStep p c e st b := by
  simp [insertStepPacked]

private theorem length_insertStepPacked_le (st b' : List Bool) :
    (insertStepPacked st b').length ≤ st.length + 26 * (b'.length + 1) := by
  unfold insertStepPacked
  refine (length_insertStep_le _ _ _ _ _).trans ?_
  have h1 := length_pairFst_le b'
  have h2 := pairSnd_length_le b'
  have h3 := length_pairFst_le (pairSnd b')
  have h4 := pairSnd_length_le (pairSnd b')
  have h5 := length_pairFst_le (pairSnd (pairSnd b'))
  have h6 := pairSnd_length_le (pairSnd (pairSnd b'))
  omega

private theorem cobham_insertStepPacked :
    Cobham fun w : Fin 2 → List Bool ↦ insertStepPacked (w 0) (w 1) := by
  have h1 : Cobham fun w : Fin 2 → List Bool ↦ w 1 := Cobham.proj 1
  exact cobham_insertStep_comp (cobham_pairFst_comp (cobham_pairSnd_comp h1))
    (cobham_pairFst_comp (cobham_pairSnd_comp (cobham_pairSnd_comp h1)))
    (cobham_pairSnd_comp (cobham_pairSnd_comp (cobham_pairSnd_comp h1))) (Cobham.proj 0)
    (cobham_pairFst_comp h1)

/-- The inner fold of `insertStr` equals the packed fold over the packed blocks. -/
private theorem foldBlocks_insertStep_eq (p c e init acc : List Bool) :
    foldBlocks (insertStep p c e) init acc =
      foldBlocks insertStepPacked init (mapBlocks (fun b ↦ pair b (pair p (pair c e))) acc) := by
  simp only [foldBlocks, mapBlocks, blocks_frame, List.foldl_map, insertStepPacked_pair]

/-- Composition with four Cobham arguments. -/
private theorem cobham_comp₄ {n : ℕ} {f : (Fin 4 → List Bool) → List Bool} (hf : Cobham f)
    {g₀ g₁ g₂ g₃ : (Fin n → List Bool) → List Bool}
    (h₀ : Cobham g₀) (h₁ : Cobham g₁) (h₂ : Cobham g₂) (h₃ : Cobham g₃) :
    Cobham fun v : Fin n → List Bool ↦ f ![g₀ v, g₁ v, g₂ v, g₃ v] := by
  refine (Cobham.comp hf (gs := ![g₀, g₁, g₂, g₃]) ?_).of_eq fun v ↦ ?_
  · intro i
    fin_cases i <;> assumption
  · congr 1
    funext i
    fin_cases i <;> rfl

/-- The inner fold of `insertStr` is Cobham in its parameters and the accumulator. -/
private theorem cobham_foldBlocks_insertStep_comp {n : ℕ}
    {gp gc ge gacc : (Fin n → List Bool) → List Bool}
    (hp : Cobham gp) (hc : Cobham gc) (he : Cobham ge) (hacc : Cobham gacc) :
    Cobham fun v : Fin n → List Bool ↦
      foldBlocks (insertStep (gp v) (gc v) (ge v)) (pair [false] []) (gacc v) := by
  have hpack : Cobham fun w : Fin 4 → List Bool ↦ pair (w 0) (pair (w 1) (pair (w 2) (w 3))) :=
    cobham_pair_comp (Cobham.proj 0)
      (cobham_pair_comp (Cobham.proj 1) (cobham_pair_comp (Cobham.proj 2) (Cobham.proj 3)))
  have hM : Cobham fun v : Fin 4 → List Bool ↦
      mapBlocks (fun b ↦ pair b (pair (v 1) (pair (v 2) (v 3)))) (v 0) :=
    (cobham_mapBlocks (n := 3) hpack (2 * Polynomial.X + 6) fun w ↦ by
      simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Polynomial.eval_add, Polynomial.eval_mul,
        Polynomial.eval_X, Polynomial.eval_ofNat, pair_length]
      simp
      omega).of_eq fun v ↦ rfl
  have hF : Cobham fun v : Fin 1 → List Bool ↦
      foldBlocks insertStepPacked (pair [false] []) (v 0) :=
    (cobham_foldBlocks (n := 0) cobham_insertStepPacked (init := fun _ ↦ pair [false] [])
      (Cobham.const _) 26 fun w ↦ length_insertStepPacked_le (w 0) (w 1)).of_eq fun v ↦ rfl
  have hM' : Cobham fun v : Fin n → List Bool ↦
      mapBlocks (fun b ↦ pair b (pair (gp v) (pair (gc v) (ge v)))) (gacc v) :=
    (cobham_comp₄ hM hacc hp hc he).of_eq fun v ↦ by simp
  exact (Cobham.comp hF fun _ : Fin 1 ↦ hM').of_eq fun v ↦ (foldBlocks_insertStep_eq _ _ _ _ _).symm

/-- `insertStr` as a Cobham function of Cobham arguments. -/
private theorem cobham_insertStr_comp {n : ℕ} {gp gc ge gacc : (Fin n → List Bool) → List Bool}
    (hp : Cobham gp) (hc : Cobham gc) (he : Cobham ge) (hacc : Cobham gacc) :
    Cobham fun v : Fin n → List Bool ↦ insertStr (gp v) (gc v) (ge v) (gacc v) := by
  have hr := cobham_foldBlocks_insertStep_comp hp hc he hacc
  have hX := Cobham.iteFn (cobham_isZeroBits_comp hc) (Cobham.const [])
    (cobham_delimit_comp (cobham_pair_comp hc he))
  exact Cobham.iteFn (cobham_pairFst_comp hr) (cobham_pairSnd_comp hr)
    (Cobham.appendFn (cobham_pairSnd_comp hr) hX)

/-! ### Length of one insertion -/

/-- The one-time budget of an insertion: the framed inserted term, or the growth of a merged
coefficient (`addModStr` pads its output to `|c| + |c'| + |p| + 4` bits). -/
private def insBudget (p c e : List Bool) : ℕ :=
  4 * c.length + 2 * e.length + 4 * p.length + 20

/-- The framed merged term replaces the framed block `b` (of length `≥ 4 |coefOf b| + 2`) at the
cost of the budget. -/
private theorem length_mergeBlock_le (p c c' e : List Bool) :
    (caseBit₀ (isZeroBits (addModStr p c c')) [] (delimit (pair (addModStr p c c') e))).length ≤
      4 * c'.length + 2 + insBudget p c e := by
  refine (length_insBlock_le _ _).trans ?_
  have := length_addModStr_le p c c'
  unfold insBudget
  omega

private theorem insertStep_pair_true (p c e acc b : List Bool) :
    insertStep p c e (pair [true] acc) b = pair [true] (acc ++ delimit b) := by
  simp [insertStep]

private theorem insertStep_pair_false (p c e acc b : List Bool) :
    insertStep p c e (pair [false] acc) b =
      caseBit₀ (ltBits e (expOf b))
        (pair [true] (acc ++ caseBit₀ (isZeroBits c) [] (delimit (pair c e)) ++ delimit b))
        (caseBit₀ (eqBits e (expOf b))
          (pair [true] (acc ++ caseBit₀ (isZeroBits (addModStr p c (coefOf b))) []
            (delimit (pair (addModStr p c (coefOf b)) e))))
          (pair [false] (acc ++ delimit b))) := by
  simp [insertStep]

/-- **Fold invariant of the insertion.** The state stays a flagged pair; the accumulator grows by
the framed processed blocks plus (once, when the flag flips) the insertion budget. -/
private theorem foldl_insertStep_length (p c e : List Bool) :
    ∀ (bs : List (List Bool)) (i : Bool) (acc₀ : List Bool),
      ∃ (i' : Bool) (acc' : List Bool),
        bs.foldl (insertStep p c e) (pair [i] acc₀) = pair [i'] acc' ∧
          acc'.length + (bif i' then 0 else insBudget p c e) ≤
            acc₀.length + (frame bs).length + (bif i then 0 else insBudget p c e)
  | [], i, acc₀ => ⟨i, acc₀, rfl, by simp [frame_nil]⟩
  | b :: bs, i, acc₀ => by
    rw [List.foldl_cons, frame_cons, List.length_append, delimit_length]
    cases i with
    | true =>
      rw [insertStep_pair_true]
      obtain ⟨i', acc', h1, h2⟩ := foldl_insertStep_length p c e bs true (acc₀ ++ delimit b)
      refine ⟨i', acc', h1, ?_⟩
      rw [List.length_append, delimit_length] at h2
      simp only [Bool.cond_true] at h2 ⊢
      omega
    | false =>
      rw [insertStep_pair_false]
      have hX := length_insBlock_le c e
      have hY := length_mergeBlock_le p c (coefOf b) e
      have hb := two_mul_length_pairFst_le b
      simp only [coefOf] at hY
      rcases ltBits_flag e (expOf b) with hlt | hlt <;> rw [hlt, caseBit₀_cons]
      · rw [Bool.cond_true]
        obtain ⟨i', acc', h1, h2⟩ := foldl_insertStep_length p c e bs true
          (acc₀ ++ caseBit₀ (isZeroBits c) [] (delimit (pair c e)) ++ delimit b)
        refine ⟨i', acc', h1, ?_⟩
        rw [List.length_append, List.length_append, delimit_length] at h2
        simp only [Bool.cond_true, Bool.cond_false] at h2 ⊢
        unfold insBudget at *
        omega
      · rw [Bool.cond_false]
        rcases eqBits_flag e (expOf b) with heq | heq <;> rw [heq, caseBit₀_cons]
        · rw [Bool.cond_true]
          obtain ⟨i', acc', h1, h2⟩ := foldl_insertStep_length p c e bs true
            (acc₀ ++ caseBit₀ (isZeroBits (addModStr p c (pairFst b))) []
              (delimit (pair (addModStr p c (pairFst b)) e)))
          refine ⟨i', acc', h1, ?_⟩
          rw [List.length_append] at h2
          simp only [Bool.cond_true, Bool.cond_false] at h2 ⊢
          omega
        · rw [Bool.cond_false]
          obtain ⟨i', acc', h1, h2⟩ := foldl_insertStep_length p c e bs false (acc₀ ++ delimit b)
          refine ⟨i', acc', h1, ?_⟩
          rw [List.length_append, delimit_length] at h2
          simp only [Bool.cond_false] at h2 ⊢
          omega

/-- **One insertion grows the accumulator by at most its budget.** -/
private theorem length_insertStr_le (p c e acc : List Bool) :
    (insertStr p c e acc).length ≤ acc.length + insBudget p c e := by
  have hX := length_insBlock_le c e
  obtain ⟨bs, rem, hs, hrem⟩ := exists_frame_append acc
  by_cases hne : rem = []
  · subst hne
    rw [List.append_nil] at hs
    subst hs
    obtain ⟨i', acc', h1, h2⟩ := foldl_insertStep_length p c e bs false []
    simp only [insertStr, foldBlocks, blocks_frame, h1, pairFst_pair, pairSnd_pair, caseBit₀_cons,
      List.length_nil, zero_add, Bool.cond_false] at h2 ⊢
    cases i'
    · simp only [Bool.cond_false, List.length_append] at h2 ⊢
      unfold insBudget at *
      omega
    · simp only [Bool.cond_true] at h2 ⊢
      omega
  · have hbad := hrem.resolve_left hne
    have hb : blocks acc = [] := by
      rw [hs]
      exact blocks_frame_append_of_bad bs hne hbad
    simp only [insertStr, foldBlocks, hb, List.foldl_nil, pairFst_pair, pairSnd_pair, caseBit₀_cons,
      Bool.cond_false, List.nil_append]
    unfold insBudget at *
    omega

/-! ### `normalizeStr` -/

/-- The normalization step reading `p` from the packed block `pair b p`. -/
private def normStepPacked (acc b' : List Bool) : List Bool :=
  insertStr (pairSnd b') (coefOf (pairFst b')) (expOf (pairFst b')) acc

private theorem normStepPacked_pair (p acc b : List Bool) :
    normStepPacked acc (pair b p) = insertStr p (coefOf b) (expOf b) acc := by
  simp [normStepPacked]

private theorem length_normStepPacked_le (acc b' : List Bool) :
    (normStepPacked acc b').length ≤ acc.length + 20 * (b'.length + 1) := by
  unfold normStepPacked
  refine (length_insertStr_le _ _ _ _).trans ?_
  unfold insBudget coefOf expOf
  have h1 := two_mul_length_pairFst_add_length_pairSnd_le (pairFst b')
  have h2 := length_pairFst_le b'
  have h3 := pairSnd_length_le b'
  omega

private theorem cobham_normStepPacked :
    Cobham fun w : Fin 2 → List Bool ↦ normStepPacked (w 0) (w 1) :=
  cobham_insertStr_comp (cobham_pairSnd_comp (Cobham.proj 1))
    (cobham_coefOf_comp (cobham_pairFst_comp (Cobham.proj 1)))
    (cobham_expOf_comp (cobham_pairFst_comp (Cobham.proj 1))) (Cobham.proj 0)

private theorem normalizeStr_eq_packed (p s : List Bool) :
    normalizeStr p s = foldBlocks normStepPacked [] (mapBlocks (fun b ↦ pair b p) s) := by
  simp only [normalizeStr, foldBlocks, mapBlocks, blocks_frame, List.foldl_map, normStepPacked_pair]

/-- `normalizeStr` as a Cobham function of Cobham arguments. -/
theorem cobham_normalizeStr_comp {n : ℕ} {gp gs : (Fin n → List Bool) → List Bool}
    (hp : Cobham gp) (hs : Cobham gs) :
    Cobham fun v : Fin n → List Bool ↦ normalizeStr (gp v) (gs v) := by
  have hM : Cobham fun v : Fin 2 → List Bool ↦ mapBlocks (fun b ↦ pair b (v 1)) (v 0) :=
    (cobham_mapBlocks (n := 1) Cobham.pairing (2 * Polynomial.X + 2) fun w ↦ by
      rw [Fin.sum_univ_two]
      simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_X,
        Polynomial.eval_ofNat, pair_length]
      omega).of_eq fun v ↦ rfl
  have hF : Cobham fun v : Fin 1 → List Bool ↦ foldBlocks normStepPacked [] (v 0) :=
    (cobham_foldBlocks (n := 0) cobham_normStepPacked (init := fun _ ↦ []) Cobham.empty 20
      fun w ↦ length_normStepPacked_le (w 0) (w 1)).of_eq fun v ↦ rfl
  have hM' : Cobham fun v : Fin n → List Bool ↦ mapBlocks (fun b ↦ pair b (gp v)) (gs v) :=
    (Cobham.comp₂ hM hs hp).of_eq fun v ↦ by simp
  exact (Cobham.comp hF fun _ : Fin 1 ↦ hM').of_eq fun v ↦ (normalizeStr_eq_packed _ _).symm

/-! ### The displayed term lists -/

/-- The block polynomial used for all four displayed-term maps: `(L + 3)^2`. -/
private theorem eval_blockPoly (m : ℕ) :
    ((Polynomial.X + 3) ^ 2 : Polynomial ℕ).eval m = (m + 3) ^ 2 := by
  simp

/-- `fTermsStr` as a Cobham function of Cobham arguments. -/
private theorem cobham_fTermsStr_comp {n : ℕ} {gp gs : (Fin n → List Bool) → List Bool}
    (hp : Cobham gp) (hs : Cobham gs) :
    Cobham fun v : Fin n → List Bool ↦ fTermsStr (gp v) (gs v) := by
  have hf₁ : Cobham fun w : Fin 2 → List Bool ↦ pair (coefOf (w 0)) (mulBits (w 1) (expOf (w 0))) :=
    cobham_pair_comp (cobham_coefOf_comp (Cobham.proj 0))
      (cobham_mulBits_comp (Cobham.proj 1) (cobham_expOf_comp (Cobham.proj 0)))
  have hf₂ : Cobham fun w : Fin 2 → List Bool ↦
      pair (negModStr (w 1) (coefOf (w 0))) (expOf (w 0)) :=
    cobham_pair_comp (cobham_negModStr_comp (Cobham.proj 1) (cobham_coefOf_comp (Cobham.proj 0)))
      (cobham_expOf_comp (Cobham.proj 0))
  have hM₁ : Cobham fun v : Fin 2 → List Bool ↦
      mapBlocks (fun b ↦ pair (coefOf b) (mulBits (v 1) (expOf b))) (v 0) :=
    (cobham_mapBlocks (n := 1) hf₁ ((Polynomial.X + 3) ^ 2) fun w ↦ by
      rw [Fin.sum_univ_two, eval_blockPoly, pair_length]
      have h1 := length_mulBits_le (w 1) (expOf (w 0))
      have h2 := length_expOf_le (w 0)
      have h3 := length_coefOf_le (w 0)
      nlinarith).of_eq fun v ↦ rfl
  have hM₂ : Cobham fun v : Fin 2 → List Bool ↦
      mapBlocks (fun b ↦ pair (negModStr (v 1) (coefOf b)) (expOf b)) (v 0) :=
    (cobham_mapBlocks (n := 1) hf₂ ((Polynomial.X + 3) ^ 2) fun w ↦ by
      rw [Fin.sum_univ_two, eval_blockPoly, pair_length]
      have h1 := length_negModStr_le (w 1) (coefOf (w 0))
      have h2 := length_expOf_le (w 0)
      have h3 := length_coefOf_le (w 0)
      nlinarith).of_eq fun v ↦ rfl
  exact Cobham.appendFn ((Cobham.comp₂ hM₁ hs hp).of_eq fun v ↦ by simp)
    ((Cobham.comp₂ hM₂ hs hp).of_eq fun v ↦ by simp)

/-- `gTermsStr` as a Cobham function of Cobham arguments. -/
private theorem cobham_gTermsStr_comp {n : ℕ} {gp gs : (Fin n → List Bool) → List Bool}
    (hp : Cobham gp) (hs : Cobham gs) :
    Cobham fun v : Fin n → List Bool ↦ gTermsStr (gp v) (gs v) := by
  have hg₁ : Cobham fun w : Fin 2 → List Bool ↦ pair (coefOf (w 0)) (addBits (w 1) (expOf (w 0))) :=
    cobham_pair_comp (cobham_coefOf_comp (Cobham.proj 0))
      (cobham_addBits_comp (Cobham.proj 1) (cobham_expOf_comp (Cobham.proj 0)))
  have hg₂ : Cobham fun w : Fin 2 → List Bool ↦
      pair (negModStr (w 1) (coefOf (w 0))) (succBits (expOf (w 0))) :=
    cobham_pair_comp (cobham_negModStr_comp (Cobham.proj 1) (cobham_coefOf_comp (Cobham.proj 0)))
      (cobham_succBits_comp (cobham_expOf_comp (Cobham.proj 0)))
  have hM₁ : Cobham fun v : Fin 2 → List Bool ↦
      mapBlocks (fun b ↦ pair (coefOf b) (addBits (v 1) (expOf b))) (v 0) :=
    (cobham_mapBlocks (n := 1) hg₁ ((Polynomial.X + 3) ^ 2) fun w ↦ by
      rw [Fin.sum_univ_two, eval_blockPoly, pair_length]
      have h1 := length_addBits_le (w 1) (expOf (w 0))
      have h2 := length_expOf_le (w 0)
      have h3 := length_coefOf_le (w 0)
      nlinarith).of_eq fun v ↦ rfl
  have hM₂ : Cobham fun v : Fin 2 → List Bool ↦
      mapBlocks (fun b ↦ pair (negModStr (v 1) (coefOf b)) (succBits (expOf b))) (v 0) :=
    (cobham_mapBlocks (n := 1) hg₂ ((Polynomial.X + 3) ^ 2) fun w ↦ by
      rw [Fin.sum_univ_two, eval_blockPoly, pair_length]
      have h1 := length_negModStr_le (w 1) (coefOf (w 0))
      have h2 := length_succBits_le (expOf (w 0))
      have h3 := length_expOf_le (w 0)
      have h4 := length_coefOf_le (w 0)
      nlinarith).of_eq fun v ↦ rfl
  exact Cobham.appendFn ((Cobham.comp₂ hM₁ hs hp).of_eq fun v ↦ by simp)
    ((Cobham.comp₂ hM₂ hs hp).of_eq fun v ↦ by simp)

/-! ### The body, the validity flag, and the bridge -/

/-- `bridgeBody` as a Cobham function of Cobham arguments. -/
private theorem cobham_bridgeBody_comp {n : ℕ} {gp gs : (Fin n → List Bool) → List Bool}
    (hp : Cobham gp) (hs : Cobham gs) :
    Cobham fun v : Fin n → List Bool ↦ bridgeBody (gp v) (gs v) := by
  have hn := cobham_normalizeStr_comp hp hs
  exact cobham_pair_comp hp (Cobham.iteFn (Cobham.nonemptyFn hn)
    (cobham_pair_comp (cobham_normalizeStr_comp hp (cobham_fTermsStr_comp hp hn))
      (cobham_normalizeStr_comp hp (cobham_gTermsStr_comp hp hn)))
    (Cobham.const guardedStr))

/-- `wfBlocksFlag` as a Cobham function of Cobham arguments. -/
private theorem cobham_wfBlocksFlag_comp {n : ℕ} {gp gs : (Fin n → List Bool) → List Bool}
    (hp : Cobham gp) (hs : Cobham gs) :
    Cobham fun v : Fin n → List Bool ↦ wfBlocksFlag (gp v) (gs v) := by
  have hstep : Cobham fun w : Fin 3 → List Bool ↦
      andBit (w 0) (andBit (hasBlockFlag (w 1)) (ltBits (coefOf (w 1)) (w 2))) :=
    Cobham.andFn (Cobham.proj 0) (Cobham.andFn (cobham_hasBlockFlag_comp (Cobham.proj 1))
      (cobham_ltBits_comp (cobham_coefOf_comp (Cobham.proj 1)) (Cobham.proj 2)))
  have hgrow : ∀ w : Fin 3 → List Bool,
      (andBit (w 0) (andBit (hasBlockFlag (w 1)) (ltBits (coefOf (w 1)) (w 2)))).length ≤
        (w 0).length + 1 * ((w 1).length + 1) := by
    intro w
    rcases andBit_flag (w 0) (andBit (hasBlockFlag (w 1)) (ltBits (coefOf (w 1)) (w 2)))
      with h | h <;> rw [h] <;> simp only [List.length_singleton] <;> omega
  have hF : Cobham fun v : Fin 2 → List Bool ↦ wfBlocksFlag (v 1) (v 0) :=
    (cobham_foldBlocks (n := 1) hstep (init := fun _ ↦ [true]) (Cobham.const _) 1 hgrow).of_eq
      fun v ↦ rfl
  exact (Cobham.comp₂ hF hs hp).of_eq fun v ↦ by simp

/-- **The bridge is polynomial-time computable.** -/
theorem bridgeStr_mem_FP : bridgeStr ∈ FP := by
  refine CobhamFP_subset_FP ?_
  show Cobham fun v : Fin 1 → List Bool ↦ bridgeStr (v 0)
  have hs : Cobham fun v : Fin 1 → List Bool ↦ v 0 := Cobham.proj 0
  have hp := cobham_pairFst_comp hs
  have ht := cobham_pairSnd_comp hs
  have hflag : Cobham fun v : Fin 1 → List Bool ↦ validRootFlag (v 0) :=
    Cobham.andFn (cobham_hasBlockFlag_comp hs)
      (Cobham.andFn (cobham_validBlocksFlag_comp ht) (cobham_wfBlocksFlag_comp hp ht))
  exact Cobham.iteFn hflag (cobham_bridgeBody_comp hp ht) (Cobham.const noInstance)

/-! ### The output-length bound -/

/-- Either a string is the framing of its blocks, or it has no blocks. -/
private theorem eq_frame_blocks_or_blocks_eq_nil (u : List Bool) :
    u = frame (blocks u) ∨ blocks u = [] := by
  obtain ⟨bs, rem, hs, hrem⟩ := exists_frame_append u
  by_cases hne : rem = []
  · subst hne
    rw [List.append_nil] at hs
    subst hs
    left
    rw [blocks_frame]
  · right
    rw [hs]
    exact blocks_frame_append_of_bad bs hne (hrem.resolve_left hne)

private theorem length_frame (bs : List (List Bool)) :
    (frame bs).length = 2 * (bs.map List.length).sum + 2 * bs.length := by
  induction bs with
  | nil => simp [frame_nil]
  | cons b bs ih =>
    rw [frame_cons, List.length_append, delimit_length, ih, List.map_cons, List.sum_cons,
      List.length_cons]
    ring

/-- The total block length and the block count of any string fit in it. -/
private theorem blocks_size_le (u : List Bool) :
    2 * ((blocks u).map List.length).sum + 2 * (blocks u).length ≤ u.length := by
  rcases eq_frame_blocks_or_blocks_eq_nil u with h | h
  · have := length_frame (blocks u)
    rw [← h] at this
    omega
  · rw [h]
    simp

/-- Left fold with a per-block budget. -/
private theorem length_foldl_le_sum (g : List Bool → List Bool → List Bool) (β : List Bool → ℕ) :
    ∀ (l : List (List Bool)) (acc : List Bool),
      (∀ acc b, b ∈ l → (g acc b).length ≤ acc.length + β b) →
      (l.foldl g acc).length ≤ acc.length + (l.map β).sum
  | [], acc, _ => by simp
  | b :: l, acc, hg => by
    rw [List.foldl_cons, List.map_cons, List.sum_cons]
    have h1 := length_foldl_le_sum g β l (g acc b)
      fun acc' b' hb' ↦ hg acc' b' (List.mem_cons_of_mem b hb')
    have h2 := hg acc b (List.mem_cons_self ..)
    omega

/-- Summing an affine per-block bound. -/
private theorem sum_le_of_forall_le (β : List Bool → ℕ) (A K : ℕ)
    (hβ : ∀ b, β b ≤ A * b.length + K) :
    ∀ bs : List (List Bool), (bs.map β).sum ≤ A * (bs.map List.length).sum + bs.length * K
  | [] => by simp
  | b :: bs => by
    rw [List.map_cons, List.sum_cons, List.map_cons, List.sum_cons, List.length_cons, Nat.mul_add,
      Nat.add_mul, Nat.one_mul]
    have h1 := sum_le_of_forall_le β A K hβ bs
    have h2 := hβ b
    omega

/-- The per-block budget of a normalization pass. -/
private def normBudget (p b : List Bool) : ℕ :=
  4 * (coefOf b).length + 2 * (expOf b).length + 4 * p.length + 20

private theorem length_normalizeStr_le_sum (p u : List Bool) :
    (normalizeStr p u).length ≤ ((blocks u).map (normBudget p)).sum := by
  have := length_foldl_le_sum (fun acc b ↦ insertStr p (coefOf b) (expOf b) acc) (normBudget p)
    (blocks u) [] fun acc b _ ↦ length_insertStr_le p (coefOf b) (expOf b) acc
  simpa [normalizeStr, foldBlocks] using this

/-- **First normalization pass**: linear in the input plus a merge budget per block. -/
private theorem length_normalizeStr_le (p u : List Bool) :
    (normalizeStr p u).length ≤ u.length + (blocks u).length * (4 * p.length + 18) := by
  refine (length_normalizeStr_le_sum p u).trans ?_
  have hsz := blocks_size_le u
  have h1 := sum_le_of_forall_le (normBudget p) 2 (4 * p.length + 20) (fun b ↦ by
    unfold normBudget coefOf expOf
    have := two_mul_length_pairFst_add_length_pairSnd_le b
    omega) (blocks u)
  have h2 : (blocks u).length * (4 * p.length + 20) =
      (blocks u).length * (4 * p.length + 18) + 2 * (blocks u).length := by ring
  omega

/-- **Second normalization pass** over the two displayed maps of the blocks of `n`. -/
private theorem length_normalizeStr_two_maps_le (p n : List Bool) (f₁ f₂ : List Bool → List Bool)
    (A₁ K₁ A₂ K₂ : ℕ) (h₁ : ∀ b, normBudget p (f₁ b) ≤ A₁ * b.length + K₁)
    (h₂ : ∀ b, normBudget p (f₂ b) ≤ A₂ * b.length + K₂) :
    (normalizeStr p (mapBlocks f₁ n ++ mapBlocks f₂ n)).length ≤
      (A₁ + A₂) * ((blocks n).map List.length).sum + (blocks n).length * (K₁ + K₂) := by
  refine (length_normalizeStr_le_sum p _).trans ?_
  rw [mapBlocks, mapBlocks, ← frame_append, blocks_frame, List.map_append, List.sum_append,
    List.map_map, List.map_map]
  have hs₁ := sum_le_of_forall_le (normBudget p ∘ f₁) A₁ K₁ h₁ (blocks n)
  have hs₂ := sum_le_of_forall_le (normBudget p ∘ f₂) A₂ K₂ h₂ (blocks n)
  rw [Nat.add_mul, Nat.mul_add]
  omega

private theorem length_normalizeStr_fTermsStr_le (p n : List Bool) :
    (normalizeStr p (fTermsStr p n)).length ≤ n.length * (7 * p.length + 27) := by
  have hsz := blocks_size_le n
  have h := length_normalizeStr_two_maps_le p n (fun b ↦ pair (coefOf b) (mulBits p (expOf b)))
    (fun b ↦ pair (negModStr p (coefOf b)) (expOf b)) (2 * p.length + 6) (6 * p.length + 26) 2
    (8 * p.length + 28)
    (fun b ↦ by
      simp only [normBudget, coefOf, expOf, pairFst_pair, pairSnd_pair]
      have h1 := length_mulBits_le p (pairSnd b)
      have h2 := two_mul_length_pairFst_add_length_pairSnd_le b
      nlinarith [Nat.mul_le_mul_left (2 * p.length + 6) h2])
    (fun b ↦ by
      simp only [normBudget, coefOf, expOf, pairFst_pair, pairSnd_pair]
      have h1 := length_negModStr_le p (pairFst b)
      have h2 := two_mul_length_pairFst_add_length_pairSnd_le b
      omega)
  rw [fTermsStr]
  refine h.trans ?_
  generalize ((blocks n).map List.length).sum = S at hsz ⊢
  generalize (blocks n).length = k at hsz ⊢
  generalize n.length = N at hsz ⊢
  generalize p.length = P
  nlinarith [Nat.mul_le_mul_left (P + 4) hsz, Nat.mul_le_mul_left (6 * P + 23) hsz,
    Nat.zero_le (P * S)]

private theorem length_normalizeStr_gTermsStr_le (p n : List Bool) :
    (normalizeStr p (gTermsStr p n)).length ≤ n.length * (7 * p.length + 27) := by
  have hsz := blocks_size_le n
  have h := length_normalizeStr_two_maps_le p n (fun b ↦ pair (coefOf b) (addBits p (expOf b)))
    (fun b ↦ pair (negModStr p (coefOf b)) (succBits (expOf b))) 2 (6 * p.length + 24) 2
    (8 * p.length + 30)
    (fun b ↦ by
      simp only [normBudget, coefOf, expOf, pairFst_pair, pairSnd_pair]
      have h1 := length_addBits_le p (pairSnd b)
      have h2 := two_mul_length_pairFst_add_length_pairSnd_le b
      omega)
    (fun b ↦ by
      simp only [normBudget, coefOf, expOf, pairFst_pair, pairSnd_pair]
      have h1 := length_negModStr_le p (pairFst b)
      have h2 := length_succBits_le (pairSnd b)
      have h3 := two_mul_length_pairFst_add_length_pairSnd_le b
      omega)
  rw [gTermsStr]
  refine h.trans ?_
  generalize ((blocks n).map List.length).sum = S at hsz ⊢
  generalize (blocks n).length = k at hsz ⊢
  generalize n.length = N at hsz ⊢
  generalize p.length = P
  nlinarith [Nat.mul_le_mul_left 2 hsz, Nat.mul_le_mul_left (7 * P + 25) hsz, Nat.zero_le (P * S)]

/-- The final arithmetic: `2P + 4 + 3 N (7P + 27) ≤ 100 (L + 1)^3` under the size constraints. -/
private theorem final_arith (P T k N L : ℕ) (hk : 2 * k ≤ T) (hL : 2 * P + T ≤ L)
    (hN : N ≤ T + k * (4 * P + 18)) :
    2 * P + 4 + 3 * (N * (7 * P + 27)) ≤ 100 * (L + 1) ^ 3 := by
  have h1 : N * (7 * P + 27) ≤ (T + k * (4 * P + 18)) * (7 * P + 27) :=
    Nat.mul_le_mul_right _ hN
  have h2 : 100 * (2 * P + T + 1) ^ 3 ≤ 100 * (L + 1) ^ 3 := by
    gcongr
  refine le_trans ?_ h2
  obtain ⟨r, rfl⟩ : ∃ r, T = 2 * k + r := ⟨T - 2 * k, by omega⟩
  cases k with
  | zero => nlinarith [Nat.zero_le (P * r), Nat.zero_le (P * P), Nat.zero_le (r * r)]
  | succ k =>
    nlinarith [Nat.zero_le (P * r), Nat.zero_le (P * P), Nat.zero_le (r * r), Nat.zero_le (k * P),
      Nat.zero_le (k * r), Nat.zero_le (k * k), Nat.zero_le (k * P * P), Nat.zero_le (k * k * P),
      Nat.zero_le (k * k * k), Nat.zero_le (P * P * P), Nat.zero_le (r * P * P),
      Nat.zero_le (r * r * P), Nat.zero_le (r * r * r), Nat.zero_le (k * r * P),
      Nat.zero_le (k * k * r), Nat.zero_le (k * r * r)]

/-- **Explicit output-length bound**: `|bridgeStr s| ≤ 100 (|s| + 1)^3`. -/
theorem length_bridgeStr_le (s : List Bool) : (bridgeStr s).length ≤ 100 * (s.length + 1) ^ 3 := by
  have hs := two_mul_length_pairFst_add_length_pairSnd_le s
  have hn := length_normalizeStr_le (pairFst s) (pairSnd s)
  have hk := blocks_size_le (pairSnd s)
  have hf := length_normalizeStr_fTermsStr_le (pairFst s) (normalizeStr (pairFst s) (pairSnd s))
  have hg := length_normalizeStr_gTermsStr_le (pairFst s) (normalizeStr (pairFst s) (pairSnd s))
  have harith := final_arith (pairFst s).length (pairSnd s).length (blocks (pairSnd s)).length
    (normalizeStr (pairFst s) (pairSnd s)).length s.length (by omega) hs hn
  have hno : noInstance.length = 18 := by decide
  have hgu : guardedStr.length = 34 := by decide
  have hcube : s.length + 1 ≤ (s.length + 1) ^ 3 := Nat.le_self_pow (by norm_num) _
  rw [bridgeStr]
  refine caseBit₀_length_le_of ?_ (by omega)
  simp only [bridgeBody]
  rw [pair_length]
  refine add_caseBit₀_length_le_of ?_ ?_
  · rw [pair_length]
    linarith
  · rw [hgu]
    omega

end SparseDiv
