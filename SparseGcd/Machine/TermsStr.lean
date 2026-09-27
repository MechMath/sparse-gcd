import SparseGcd.Machine.ArithStr
import SparseGcd.Machine.CnfStr
import SparseDivComplexity.BridgeString.Correctness

/-!
# Building the sparse instance as strings (Cobham layer)

Term lists are encoded by `SparseDiv.encTerms` (framed `pair (encNat c) (encNat e)` blocks).
The functions below implement `rawRterms`, `rawBterms`, `rawClauseTerms`, `rawConstraintTerms`,
`Hterms`, `normalize` of `Machine/TrialData.lean` / `Poly/Encoding.lean` / `Terms.lean`.

## Design

* Every emitted numeral is canonical (`canonBits`, `modBits`, `divBits`), so the string outputs are
  *literally* `encTerms` of the data-level lists.
* The out-of-range default `ℓ.getD i 2` of the data level is detected on strings by comparing
  `takeBlocksStr i ℓ` with `ℓ` (`TermsStr.primeBlock`).
* The clause product has `2^{|c|}` terms, so no polynomial-time function can agree with
  `rawClauseTerms` on unbounded clauses: `clauseTermsStr` unrolls the product for **three**
  literals (a fixed composition, hence in Cobham's algebra with no length analysis), and the
  correctness statements carry the bounded-clause hypothesis of the pipeline (`BoundedClauses`).
* the `SparseDivComplexity` support modules' `normalizeStr` merges coefficients with `addBits`, whose output is not a canonical
  numeral; the collected list is therefore canonicalized blockwise (`canonTermsStr`) before it is
  compared with `encTerms (normalize p l)`.
* Cobham membership of all `mapBlocks` loops uses the generic polynomial growth of Cobham
  functions (`TermsStr.cobham_exists_poly_bound`, from `Cobham.cobham_iff_FPn`).

All helpers live in the namespace `SparseGcd.TermsStr`; the interface (used by
`Machine/TrialStr.lean`) is in `SparseGcd`.
-/

open Complexity SAT SparseDiv SparseDiv.StringArith

namespace SparseGcd

namespace TermsStr

/-! ### Polynomial growth of Cobham functions -/

/-- The tuple encoding is linearly bounded by the total argument length. -/
theorem length_encodeVec_le : ∀ {n : ℕ} (v : Fin n → List Bool),
    (Cobham.encodeVec v).length ≤ 2 ^ n * (∑ i, (v i).length + 2 * n)
  | 0, v => by simp
  | n + 1, v => by
    have ih : (Cobham.encodeVec (Fin.tail v)).length ≤
        2 ^ n * (∑ i : Fin n, (v i.succ).length + 2 * n) := length_encodeVec_le (Fin.tail v)
    have hP : 1 ≤ 2 ^ n := Nat.one_le_two_pow
    rw [Cobham.encodeVec_succ, pair_length, Fin.sum_univ_succ, pow_succ]
    nlinarith [ih, hP]

/-- **Every Cobham function has polynomially bounded output length** (in the total input length). -/
theorem cobham_exists_poly_bound {n : ℕ} {f : (Fin n → List Bool) → List Bool} (hf : Cobham f) :
    ∃ q : Polynomial ℕ, ∀ v, (f v).length ≤ q.eval (∑ i, (v i).length) := by
  obtain ⟨g, hg, hgf⟩ := Cobham.cobham_iff_FPn.mp hf
  obtain ⟨p, hp⟩ := Cobham.output_length_poly_of_mem_FP hg
  refine ⟨p.comp (Polynomial.C (2 ^ n) * (Polynomial.X + Polynomial.C (2 * n))), fun v ↦ ?_⟩
  rw [← hgf v, Polynomial.eval_comp, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_add,
    Polynomial.eval_X, Polynomial.eval_C]
  exact (hp _).trans (polynomial_eval_mono_nat p (length_encodeVec_le v))

/-- `cobham_mapBlocks` without an explicit length bound. -/
theorem cobham_mapBlocks' {n : ℕ} {f : (Fin (n + 1) → List Bool) → List Bool} (hf : Cobham f) :
    Cobham fun v : Fin (n + 1) → List Bool ↦
      mapBlocks (fun b ↦ f (Fin.cons b (Fin.tail v))) (v 0) := by
  obtain ⟨q, hq⟩ := cobham_exists_poly_bound hf
  exact cobham_mapBlocks hf q hq

/-- Precomposition with `Fin.tail`. -/
theorem cobham_tail_comp {n : ℕ} {g : (Fin n → List Bool) → List Bool} (hg : Cobham g) :
    Cobham fun u : Fin (n + 1) → List Bool ↦ g (Fin.tail u) :=
  (Cobham.comp hg fun i ↦ Cobham.proj i.succ).of_eq fun _ ↦ rfl

/-- `mapBlocks` with a block function `F b params` (Cobham in the block and the parameters),
applied to a Cobham argument. -/
theorem cobham_mapBlocks_comp {n : ℕ} {F : List Bool → (Fin n → List Bool) → List Bool}
    (hF : Cobham fun u : Fin (n + 1) → List Bool ↦ F (u 0) (Fin.tail u))
    {g : (Fin n → List Bool) → List Bool} (hg : Cobham g) :
    Cobham fun v : Fin n → List Bool ↦ mapBlocks (fun b ↦ F b v) (g v) := by
  have h := cobham_mapBlocks' hF
  refine (Cobham.comp h (gs := fun i v ↦ (Fin.cons (g v) v : Fin (n + 1) → List Bool) i)
    ?_).of_eq fun v ↦ ?_
  · intro i
    refine Fin.cases ?_ (fun i ↦ ?_) i
    · exact hg
    · exact Cobham.proj i
  · simp only [Fin.cons_zero, Fin.tail_cons]

/-- A fixed number of iterations of a parametrized Cobham step is a composition. -/
theorem cobham_iterate {n : ℕ} {f : List Bool → (Fin n → List Bool) → List Bool}
    (hf : Cobham fun u : Fin (n + 1) → List Bool ↦ f (u 0) (Fin.tail u))
    {g : (Fin n → List Bool) → List Bool} (hg : Cobham g) :
    ∀ k : ℕ, Cobham fun v : Fin n → List Bool ↦ (fun s ↦ f s v)^[k] (g v)
  | 0 => hg
  | k + 1 => by
    have ih := cobham_iterate hf hg k
    refine (Cobham.comp hf
      (gs := fun i v ↦ (Fin.cons ((fun s ↦ f s v)^[k] (g v)) v : Fin (n + 1) → List Bool) i)
      ?_).of_eq fun v ↦ ?_
    · intro i
      refine Fin.cases ?_ (fun i ↦ ?_) i
      · exact ih
      · exact Cobham.proj i
    · rw [Function.iterate_succ_apply']
      exact rfl

/-- Composition with four inner functions. -/
theorem cobham_comp₄ {n : ℕ} {f : (Fin 4 → List Bool) → List Bool} (hf : Cobham f)
    {g₀ g₁ g₂ g₃ : (Fin n → List Bool) → List Bool}
    (h₀ : Cobham g₀) (h₁ : Cobham g₁) (h₂ : Cobham g₂) (h₃ : Cobham g₃) :
    Cobham fun v : Fin n → List Bool ↦ f ![g₀ v, g₁ v, g₂ v, g₃ v] := by
  refine (Cobham.comp hf (gs := ![g₀, g₁, g₂, g₃]) ?_).of_eq fun v ↦ ?_
  · intro i; fin_cases i <;> assumption
  · congr 1
    funext i
    fin_cases i <;> rfl

theorem cobham_delimit_comp {n : ℕ} {g : (Fin n → List Bool) → List Bool} (hg : Cobham g) :
    Cobham fun v : Fin n → List Bool ↦ delimit (g v) :=
  (cobham_pair_comp hg (Cobham.const [])).of_eq fun v ↦ by simp [pair]

/-! ### Elementary length facts -/

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

private theorem two_mul_length_pairFst_add_length_pairSnd_le (z : List Bool) :
    2 * (pairFst z).length + (pairSnd z).length ≤ z.length := by
  rcases hu : unpair? z with _ | ⟨x, y⟩
  · have h : pairSnd z = [] := by simp [pairSnd, hu]
    rw [h, List.length_nil, add_zero]
    exact two_mul_length_pairFst_le z
  · rw [eq_pair_of_unpair?_eq_some hu, pairFst_pair, pairSnd_pair, pair_length]
    omega

private theorem caseBit₀_length_le_of {s x y : List Bool} {N : ℕ} (hx : x.length ≤ N)
    (hy : y.length ≤ N) : (caseBit₀ s x y).length ≤ N := by
  cases s with
  | nil => exact hy
  | cons b s => cases b <;> simpa

/-! ### Block combinators -/

theorem frame_cons_eq_pair (b : List Bool) (bs : List (List Bool)) :
    frame (b :: bs) = pair b (frame bs) := by
  simp [frame, pair]

/-- Concatenate the blocks of a framed list. -/
def flattenBlocks (s : List Bool) : List Bool := foldBlocks (fun acc b ↦ acc ++ b) [] s

private theorem foldl_append (bs : List (List Bool)) (acc : List Bool) :
    bs.foldl (fun acc b ↦ acc ++ b) acc = acc ++ bs.flatten := by
  induction bs generalizing acc with
  | nil => simp
  | cons b bs ih => rw [List.foldl_cons, ih, List.flatten_cons, List.append_assoc]

theorem flattenBlocks_frame (bs : List (List Bool)) : flattenBlocks (frame bs) = bs.flatten := by
  rw [flattenBlocks, foldBlocks_frame, foldl_append, List.nil_append]

theorem cobham_flattenBlocks_comp {n : ℕ} {g : (Fin n → List Bool) → List Bool} (hg : Cobham g) :
    Cobham fun v : Fin n → List Bool ↦ flattenBlocks (g v) := by
  have h : Cobham fun v : Fin 1 → List Bool ↦ foldBlocks (fun acc b ↦ acc ++ b) [] (v 0) :=
    (cobham_foldBlocks (n := 0) (step := fun w : Fin 2 → List Bool ↦ w 0 ++ w 1)
      (Cobham.appendFn (.proj 0) (.proj 1)) (init := fun _ ↦ []) Cobham.empty 1
      fun w ↦ by simp only [List.length_append]; omega).of_eq fun v ↦ rfl
  exact (Cobham.comp h fun _ : Fin 1 ↦ hg).of_eq fun v ↦ rfl

/-- Reverse the block list of a framed list. -/
def revBlocks (s : List Bool) : List Bool := foldBlocks (fun acc b ↦ delimit b ++ acc) [] s

private theorem foldl_delimit_append (bs : List (List Bool)) (acc : List Bool) :
    bs.foldl (fun acc b ↦ delimit b ++ acc) acc = frame bs.reverse ++ acc := by
  induction bs generalizing acc with
  | nil => simp [frame_nil]
  | cons b bs ih =>
    rw [List.foldl_cons, ih, List.reverse_cons, frame_append, frame_cons, frame_nil,
      List.append_nil, List.append_assoc]

theorem revBlocks_frame (bs : List (List Bool)) : revBlocks (frame bs) = frame bs.reverse := by
  rw [revBlocks, foldBlocks_frame, foldl_delimit_append, List.append_nil]

theorem cobham_revBlocks_comp {n : ℕ} {g : (Fin n → List Bool) → List Bool} (hg : Cobham g) :
    Cobham fun v : Fin n → List Bool ↦ revBlocks (g v) := by
  have h : Cobham fun v : Fin 1 → List Bool ↦ foldBlocks (fun acc b ↦ delimit b ++ acc) [] (v 0) :=
    (cobham_foldBlocks (n := 0) (step := fun w : Fin 2 → List Bool ↦ delimit (w 1) ++ w 0)
      (Cobham.appendFn (cobham_delimit_comp (.proj 1)) (.proj 0)) (init := fun _ ↦ [])
      Cobham.empty 2
      fun w ↦ by simp only [List.length_append, delimit_length]; omega).of_eq fun v ↦ rfl
  exact (Cobham.comp h fun _ : Fin 1 ↦ hg).of_eq fun v ↦ rfl

/-- The number of blocks of a framed list, in unary. -/
def countBlocks (s : List Bool) : List Bool := foldBlocks (fun acc _ ↦ true :: acc) [] s

private theorem foldl_cons_true (bs : List (List Bool)) (acc : List Bool) :
    bs.foldl (fun acc _ ↦ true :: acc) acc = List.replicate bs.length true ++ acc := by
  induction bs generalizing acc with
  | nil => simp
  | cons b bs ih =>
    rw [List.foldl_cons, ih, List.length_cons, List.replicate_succ', List.append_assoc,
      List.singleton_append]

theorem countBlocks_frame (bs : List (List Bool)) : countBlocks (frame bs) = unaryN bs.length := by
  rw [countBlocks, foldBlocks_frame, foldl_cons_true, List.append_nil, unaryN]

theorem cobham_countBlocks_comp {n : ℕ} {g : (Fin n → List Bool) → List Bool} (hg : Cobham g) :
    Cobham fun v : Fin n → List Bool ↦ countBlocks (g v) := by
  have h : Cobham fun v : Fin 1 → List Bool ↦ foldBlocks (fun acc _ ↦ true :: acc) [] (v 0) :=
    (cobham_foldBlocks (n := 0) (step := fun w : Fin 2 → List Bool ↦ true :: w 0)
      (cobham_cons true (.proj 0)) (init := fun _ ↦ []) Cobham.empty 1
      fun w ↦ by simp only [List.length_cons]; omega).of_eq fun v ↦ rfl
  exact (Cobham.comp h fun _ : Fin 1 ↦ hg).of_eq fun v ↦ rfl

/-- One step of the block zip: the state is `pair remaining acc`; a block `b` is paired with the
next remaining block. -/
def zipStep (st b : List Bool) : List Bool :=
  caseBit₀ (nonemptyFlag (pairFst st))
    (pair (pairSnd (pairFst st)) (pairSnd st ++ delimit (pair b (pairFst (pairFst st))))) st

/-- `frame (zipWith pair us Fs)` from the framed lists `us`, `Fs`. -/
def zipBlocks (us Fs : List Bool) : List Bool := pairSnd (foldBlocks zipStep (pair Fs []) us)

private theorem zipStep_cons (F : List Bool) (Fs : List (List Bool)) (acc b : List Bool) :
    zipStep (pair (frame (F :: Fs)) acc) b = pair (frame Fs) (acc ++ delimit (pair b F)) := by
  rw [zipStep, frame_cons_eq_pair, pairFst_pair, pairSnd_pair,
    nonemptyFlag_of_ne_nil (pair_ne_nil _ _), caseBit₀_cons, Bool.cond_true, pairFst_pair,
    pairSnd_pair]

private theorem zipStep_nil (acc b : List Bool) : zipStep (pair [] acc) b = pair [] acc := by
  rw [zipStep, pairFst_pair, nonemptyFlag_nil, caseBit₀_nil]

private theorem foldl_zipStep_nil (us : List (List Bool)) (acc : List Bool) :
    us.foldl zipStep (pair [] acc) = pair [] acc := by
  induction us with
  | nil => rfl
  | cons u us ih => rw [List.foldl_cons, zipStep_nil, ih]

private theorem foldl_zipStep : ∀ (us Fs : List (List Bool)) (acc : List Bool),
    us.foldl zipStep (pair (frame Fs) acc) =
      pair (frame (Fs.drop us.length)) (acc ++ frame (List.zipWith pair us Fs))
  | [], Fs, acc => by simp [frame_nil]
  | u :: us, [], acc => by
    rw [frame_nil, List.foldl_cons, zipStep_nil, foldl_zipStep_nil]
    simp [frame_nil]
  | u :: us, F :: Fs, acc => by
    rw [List.foldl_cons, zipStep_cons, foldl_zipStep us Fs, List.length_cons,
      List.drop_succ_cons, List.zipWith_cons_cons, frame_cons, List.append_assoc]

theorem zipBlocks_frame (us Fs : List (List Bool)) :
    zipBlocks (frame us) (frame Fs) = frame (List.zipWith pair us Fs) := by
  rw [zipBlocks, foldBlocks_frame, foldl_zipStep, pairSnd_pair, List.nil_append]

private theorem length_zipStep_le (st b : List Bool) :
    (zipStep st b).length ≤ st.length + 8 * (b.length + 1) := by
  have h1 := two_mul_length_pairFst_add_length_pairSnd_le st
  have h2 := two_mul_length_pairFst_add_length_pairSnd_le (pairFst st)
  rw [zipStep]
  refine caseBit₀_length_le_of ?_ ?_
  · rw [pair_length, List.length_append, delimit_length, pair_length]
    omega
  · omega

theorem cobham_zipStep : Cobham fun w : Fin 3 → List Bool ↦ zipStep (w 0) (w 1) := by
  have hF := cobham_pairFst_comp (Cobham.proj (n := 3) 0)
  exact Cobham.iteFn (Cobham.nonemptyFn hF)
    (cobham_pair_comp (cobham_pairSnd_comp hF)
      (Cobham.appendFn (cobham_pairSnd_comp (.proj 0))
        (cobham_delimit_comp (cobham_pair_comp (.proj 1) (cobham_pairFst_comp hF)))))
    (.proj 0)

theorem cobham_zipBlocks : Cobham fun v : Fin 2 → List Bool ↦ zipBlocks (v 0) (v 1) := by
  have h := cobham_foldBlocks (n := 1) (step := fun w : Fin 3 → List Bool ↦ zipStep (w 0) (w 1))
    cobham_zipStep (init := fun u : Fin 1 → List Bool ↦ pair (u 0) [])
    (cobham_pair_comp (.proj 0) (Cobham.const [])) 8 fun w ↦ length_zipStep_le (w 0) (w 1)
  exact (cobham_pairSnd_comp h).of_eq fun v ↦ rfl

theorem cobham_zipBlocks_comp {n : ℕ} {g₀ g₁ : (Fin n → List Bool) → List Bool}
    (h₀ : Cobham g₀) (h₁ : Cobham g₁) :
    Cobham fun v : Fin n → List Bool ↦ zipBlocks (g₀ v) (g₁ v) :=
  (Cobham.comp₂ cobham_zipBlocks h₀ h₁).of_eq fun v ↦ by simp

/-- `frame [unaryN 0, …, unaryN (k-1)]` from a string of length `k`. -/
def idxBlocks : List Bool → List Bool
  | [] => []
  | _ :: x => idxBlocks x ++ delimit x

theorem idxBlocks_unaryN : ∀ k : ℕ, idxBlocks (unaryN k) = frame ((List.range k).map unaryN)
  | 0 => rfl
  | k + 1 => by
    have h : unaryN (k + 1) = true :: unaryN k := List.replicate_succ
    rw [h]
    simp only [idxBlocks]
    rw [idxBlocks_unaryN k, List.range_succ, List.map_append, frame_append, List.map_singleton,
      frame_cons, frame_nil, List.append_nil]

private theorem idxBlocks_eq_recNotation (x : List Bool) (v : Fin 0 → List Bool) :
    recNotation (fun _ : Fin 0 → List Bool ↦ []) (fun w : Fin 2 → List Bool ↦ w 1 ++ delimit (w 0))
      (fun w : Fin 2 → List Bool ↦ w 1 ++ delimit (w 0)) x v = idxBlocks x := by
  induction x with
  | nil => rfl
  | cons b x ih => cases b <;> simp [idxBlocks, ih]

private theorem length_idxBlocks_le (x : List Bool) :
    (idxBlocks x).length ≤ x.length * (2 * x.length + 2) := by
  induction x with
  | nil => simp [idxBlocks]
  | cons b x ih =>
    simp only [idxBlocks, List.length_append, delimit_length, List.length_cons]
    nlinarith [ih]

theorem cobham_idxBlocks : Cobham fun v : Fin 1 → List Bool ↦ idxBlocks (v 0) := by
  have hstep : Cobham fun w : Fin 2 → List Bool ↦ w 1 ++ delimit (w 0) :=
    Cobham.appendFn (.proj 1) (cobham_delimit_comp (.proj 0))
  have hj : Cobham fun u : Fin 1 → List Bool ↦
      Cobham.polyLen (Polynomial.X * (2 * Polynomial.X + 2)) (u 0) :=
    Cobham.polyLen_mem _ (.proj 0)
  refine (Cobham.boundedRec (n := 0) Cobham.empty hstep hstep hj ?_).of_eq fun v ↦ ?_
  · intro x v
    rw [idxBlocks_eq_recNotation, Cobham.polyLen_length, Fin.cons_zero]
    simp only [Polynomial.eval_mul, Polynomial.eval_add, Polynomial.eval_X, Polynomial.eval_ofNat]
    exact length_idxBlocks_le x
  · rw [idxBlocks_eq_recNotation]

theorem cobham_idxBlocks_comp {n : ℕ} {g : (Fin n → List Bool) → List Bool} (hg : Cobham g) :
    Cobham fun v : Fin n → List Bool ↦ idxBlocks (g v) :=
  (Cobham.comp cobham_idxBlocks fun _ : Fin 1 ↦ hg).of_eq fun _ ↦ rfl

/-! ### Encoded term lists -/

theorem encTerms_eq_frame (l : Terms) : encTerms l = frame (l.map encTerm) := by
  rw [encTerms, frame, List.map_map]
  rfl

theorem encTerms_append (l₁ l₂ : Terms) : encTerms (l₁ ++ l₂) = encTerms l₁ ++ encTerms l₂ := by
  simp [encTerms]

theorem encTerms_flatten (L : List Terms) : encTerms L.flatten = (L.map encTerms).flatten := by
  induction L with
  | nil => rfl
  | cons l L ih => rw [List.flatten_cons, encTerms_append, ih, List.map_cons, List.flatten_cons]

theorem decNat_true : decNat [true] = 1 := by simp [decNat_cons]

theorem encNat_zero : encNat 0 = [] := Nat.zero_bits

theorem encNat_one : encNat 1 = [true] := Nat.one_bits

theorem encNat_two : encNat 2 = [false, true] := by decide

theorem encTerms_one_zero : encTerms [(1, 0)] = delimit (pair [true] []) := by
  simp only [encTerms_cons, encTerms_nil, List.append_nil, encTerm, encNat_one, encNat_zero]

/-- `modBits` on a nonzero modulus is the canonical remainder numeral. -/
theorem modBits_eq_encNat (a b : List Bool) (hb : decNat b ≠ 0) :
    modBits a b = encNat (decNat a % decNat b) := by
  rw [modBits, divModVal_spec a b hb]

/-- Division with the data-level convention `a / 0 = 0`. -/
def divBits₀ (a b : List Bool) : List Bool := caseBit₀ (isZeroBits b) [] (divBits a b)

theorem divBits₀_eq_encNat (a b : List Bool) : divBits₀ a b = encNat (decNat a / decNat b) := by
  rw [divBits₀]
  rcases isZeroBits_flag b with h | h
  · rw [h, caseBit₀_cons, Bool.cond_true, (isZeroBits_eq_true_iff b).1 h, Nat.div_zero, encNat_zero]
  · have hb : decNat b ≠ 0 := fun h0 ↦ by
      have := (isZeroBits_eq_true_iff b).2 h0
      rw [h] at this
      simp at this
    rw [h, caseBit₀_cons, Bool.cond_false, divBits, divModVal_spec a b hb]

theorem cobham_divBits₀_comp {n : ℕ} {ga gb : (Fin n → List Bool) → List Bool}
    (ha : Cobham ga) (hb : Cobham gb) :
    Cobham fun v : Fin n → List Bool ↦ divBits₀ (ga v) (gb v) :=
  Cobham.iteFn (cobham_isZeroBits_comp hb) (Cobham.const []) (cobham_divBits_comp ha hb)

/-- A framed term block with canonical numerals. -/
def termBlock (c e : List Bool) : List Bool := delimit (pair (canonBits c) (canonBits e))

theorem termBlock_eq {c e : List Bool} {x y : ℕ} (hc : decNat c = x) (he : decNat e = y) :
    termBlock c e = delimit (encTerm (x, y)) := by
  rw [termBlock, canonBits, canonBits, hc, he]
  rfl

theorem cobham_termBlock_comp {n : ℕ} {gc ge : (Fin n → List Bool) → List Bool}
    (hc : Cobham gc) (he : Cobham ge) :
    Cobham fun v : Fin n → List Bool ↦ termBlock (gc v) (ge v) :=
  cobham_delimit_comp (cobham_pair_comp (cobham_canonBits_comp hc) (cobham_canonBits_comp he))

/-- Canonicalize both numerals of every term block. -/
def canonTermsStr (s : List Bool) : List Bool :=
  mapBlocks (fun b ↦ pair (canonBits (coefOf b)) (canonBits (expOf b))) s

theorem canonTermsStr_frameTerms (ts : List (List Bool × List Bool)) :
    canonTermsStr (frameTerms ts) = encTerms (decodeTerms ts) := by
  rw [canonTermsStr, frameTerms, mapBlocks_frame, encTerms_eq_frame, decodeTerms, List.map_map,
    List.map_map]
  congr 1
  exact List.map_congr_left fun t _ ↦ by
    simp only [Function.comp_def, blk, coefOf, expOf, pairFst_pair, pairSnd_pair, encTerm,
      canonBits]

theorem encTerms_eq_frameTerms (l : Terms) :
    encTerms l = frameTerms (l.map fun t ↦ (encNat t.1, encNat t.2)) := by
  rw [encTerms_eq_frame, frameTerms, List.map_map]
  rfl

theorem decodeTerms_encode (l : Terms) :
    decodeTerms (l.map fun t ↦ (encNat t.1, encNat t.2)) = l := by
  simp [decodeTerms, Function.comp_def]

theorem cobham_canonTermsStr_comp {n : ℕ} {g : (Fin n → List Bool) → List Bool} (hg : Cobham g) :
    Cobham fun v : Fin n → List Bool ↦ canonTermsStr (g v) := by
  unfold canonTermsStr
  refine cobham_mapBlocks_comp (F := fun b _ ↦ pair (canonBits (coefOf b)) (canonBits (expOf b)))
    ?_ hg
  exact cobham_pair_comp (cobham_canonBits_comp (cobham_pairFst_comp (.proj 0)))
    (cobham_canonBits_comp (cobham_pairSnd_comp (.proj 0)))

/-! ### Composition forms of the arithmetic layer -/

theorem cobham_powModStr_comp {n : ℕ} {gb ge gp : (Fin n → List Bool) → List Bool}
    (hb : Cobham gb) (he : Cobham ge) (hp : Cobham gp) :
    Cobham fun v : Fin n → List Bool ↦ powModStr (gb v) (ge v) (gp v) :=
  (Cobham.comp₃ cobham_powModStr hb he hp).of_eq fun v ↦ by simp

theorem cobham_takeBlocksStr_comp {n : ℕ} {gm gs : (Fin n → List Bool) → List Bool}
    (hm : Cobham gm) (hs : Cobham gs) :
    Cobham fun v : Fin n → List Bool ↦ takeBlocksStr (gm v) (gs v) :=
  (Cobham.comp₂ cobham_takeBlocksStr hm hs).of_eq fun v ↦ by simp

theorem cobham_nthBlockStr_comp {n : ℕ} {gi gs : (Fin n → List Bool) → List Bool}
    (hi : Cobham gi) (hs : Cobham gs) :
    Cobham fun v : Fin n → List Bool ↦ nthBlockStr (gi v) (gs v) :=
  (Cobham.comp₂ cobham_nthBlockStr hi hs).of_eq fun v ↦ by simp

theorem cobham_samplesStr_comp {n : ℕ} {gp gt gB gbits : (Fin n → List Bool) → List Bool}
    (hp : Cobham gp) (ht : Cobham gt) (hB : Cobham gB) (hbits : Cobham gbits) :
    Cobham fun v : Fin n → List Bool ↦ samplesStr (gp v) (gt v) (gB v) (gbits v) :=
  (cobham_comp₄ cobham_samplesStr hp ht hB hbits).of_eq fun v ↦ rfl

/-! ### The `i`-th Boolean prime -/

/-- `encNat (ℓ.getD i 2)` from the framed list `ℓ` and unary `i`: the block is out of range
exactly when the first `i` blocks are all of `ℓ`. -/
def primeBlock (i ℓ : List Bool) : List Bool :=
  caseBit₀ (Cobham.eqFlag (takeBlocksStr i ℓ) ℓ) [false, true] (nthBlockStr i ℓ)

theorem primeBlock_eq (ℓ : List ℕ) (i : ℕ) :
    primeBlock (unaryN i) (frame (ℓ.map encNat)) = encNat (ℓ.getD i 2) := by
  rw [primeBlock, takeBlocksStr_frame, nthBlockStr_frame]
  by_cases hi : i < ℓ.length
  · have hne : frame ((ℓ.map encNat).take i) ≠ frame (ℓ.map encNat) := by
      intro h
      have h' := congrArg blocks h
      rw [blocks_frame, blocks_frame] at h'
      have h'' := congrArg List.length h'
      rw [List.length_take, List.length_map] at h''
      omega
    have hflag : Cobham.eqFlag (frame ((ℓ.map encNat).take i)) (frame (ℓ.map encNat)) = [false] := by
      rcases Cobham.eqFlag_flag (frame ((ℓ.map encNat).take i)) (frame (ℓ.map encNat)) with h | h
      · exact absurd ((Cobham.eqFlag_eq_true_iff _ _).1 h) hne
      · exact h
    rw [hflag, caseBit₀_cons, Bool.cond_false, List.getD_eq_getElem _ _ (by simpa using hi),
      List.getD_eq_getElem _ _ hi, List.getElem_map]
  · push Not at hi
    rw [List.take_of_length_le (by simpa using hi), eqFlag_self, caseBit₀_cons, Bool.cond_true,
      List.getD_eq_default _ _ hi, encNat_two]

theorem cobham_primeBlock_comp {n : ℕ} {gi gℓ : (Fin n → List Bool) → List Bool}
    (hi : Cobham gi) (hℓ : Cobham gℓ) :
    Cobham fun v : Fin n → List Bool ↦ primeBlock (gi v) (gℓ v) :=
  Cobham.iteFn (Cobham.eqFlag_mem (cobham_takeBlocksStr_comp hi hℓ) hℓ)
    (Cobham.const [false, true]) (cobham_nthBlockStr_comp hi hℓ)

/-! ### Literal factors and products -/

/-- `encTerms (rawLitTerms p E ℓ w l)` from the literal block `encLitU l`. -/
def litTermsStr (p E ℓ w b : List Bool) : List Bool :=
  termBlock [true] (divBits₀ E (primeBlock (pairSnd b) ℓ)) ++
    termBlock (modBits (subBits p (modBits
      (caseBit₀ (pairFst b) (canonBits (powModStr w (divBits₀ E (primeBlock (pairSnd b) ℓ)) p))
        [true]) p)) p) []

theorem litTermsStr_eq (p E : ℕ) (ℓ : List ℕ) (w : ℕ) (l : Lit) (hp : p ≠ 0) :
    litTermsStr (encNat p) (encNat E) (frame (ℓ.map encNat)) (encNat w) (encLitU l) =
      encTerms (rawLitTerms p E ℓ w l) := by
  have hp' : decNat (encNat p) ≠ 0 := by rwa [decNat_encNat]
  have he : divBits₀ (encNat E) (primeBlock (unaryN l.var) (frame (ℓ.map encNat))) =
      encNat (E / ℓ.getD l.var 2) := by
    rw [primeBlock_eq, divBits₀_eq_encNat, decNat_encNat, decNat_encNat]
  have hz : decNat (caseBit₀ [l.sign]
      (canonBits (powModStr (encNat w) (encNat (E / ℓ.getD l.var 2)) (encNat p))) [true]) =
      if l.sign then powMod w (E / ℓ.getD l.var 2) p else 1 := by
    cases l.sign
    · simp [decNat_true]
    · simp [decNat_powModStr _ _ _ hp']
  have h2 : decNat (modBits (subBits (encNat p) (modBits (caseBit₀ [l.sign]
      (canonBits (powModStr (encNat w) (encNat (E / ℓ.getD l.var 2)) (encNat p))) [true])
      (encNat p))) (encNat p)) =
      (p - (if l.sign then powMod w (E / ℓ.getD l.var 2) p else 1) % p) % p := by
    rw [decNat_modBits _ _ hp', decNat_subBits, decNat_modBits _ _ hp', hz, decNat_encNat]
  rw [litTermsStr, encLitU, pairFst_pair, pairSnd_pair, he]
  simp only [rawLitTerms, encTerms_cons, encTerms_nil, List.append_nil]
  rw [termBlock_eq decNat_true (decNat_encNat _), termBlock_eq h2 decNat_nil]

theorem cobham_litTermsStr_comp {n : ℕ} {gp gE gℓ gw gb : (Fin n → List Bool) → List Bool}
    (hp : Cobham gp) (hE : Cobham gE) (hℓ : Cobham gℓ) (hw : Cobham gw) (hb : Cobham gb) :
    Cobham fun v : Fin n → List Bool ↦ litTermsStr (gp v) (gE v) (gℓ v) (gw v) (gb v) := by
  have he := cobham_divBits₀_comp hE (cobham_primeBlock_comp (cobham_pairSnd_comp hb) hℓ)
  have hz := Cobham.iteFn (cobham_pairFst_comp hb)
    (cobham_canonBits_comp (cobham_powModStr_comp hw he hp)) (Cobham.const [true])
  exact Cobham.appendFn (cobham_termBlock_comp (Cobham.const [true]) he)
    (cobham_termBlock_comp
      (cobham_modBits_comp (cobham_subBits_comp hp (cobham_modBits_comp hz hp)) hp)
      (Cobham.const []))

/-- The product of two term blocks. -/
def prodBlock (p b₁ b₂ : List Bool) : List Bool :=
  pair (modBits (mulBits (coefOf b₁) (coefOf b₂)) p) (canonBits (addBits (expOf b₁) (expOf b₂)))

theorem prodBlock_encTerm (p : ℕ) (s t : ℕ × ℕ) (hp : p ≠ 0) :
    prodBlock (encNat p) (encTerm s) (encTerm t) = encTerm ((s.1 * t.1) % p, s.2 + t.2) := by
  have hp' : decNat (encNat p) ≠ 0 := by rwa [decNat_encNat]
  simp only [prodBlock, encTerm, coefOf, expOf, pairFst_pair, pairSnd_pair]
  rw [modBits_eq_encNat _ _ hp', decNat_mulBits, canonBits, decNat_addBits, decNat_encNat,
    decNat_encNat, decNat_encNat, decNat_encNat, decNat_encNat]

theorem cobham_prodBlock_comp {n : ℕ} {gp g₁ g₂ : (Fin n → List Bool) → List Bool}
    (hp : Cobham gp) (h₁ : Cobham g₁) (h₂ : Cobham g₂) :
    Cobham fun v : Fin n → List Bool ↦ prodBlock (gp v) (g₁ v) (g₂ v) :=
  cobham_pair_comp
    (cobham_modBits_comp (cobham_mulBits_comp (cobham_pairFst_comp h₁) (cobham_pairFst_comp h₂)) hp)
    (cobham_canonBits_comp (cobham_addBits_comp (cobham_pairSnd_comp h₁) (cobham_pairSnd_comp h₂)))

/-- `encTerms (mulTerms p l₁ l₂)` on encoded term lists (all pairwise products). -/
def mulTermsStr (p l₁ l₂ : List Bool) : List Bool :=
  flattenBlocks (mapBlocks (fun b₁ ↦ mapBlocks (prodBlock p b₁) l₂) l₁)

theorem mulTermsStr_eq (p : ℕ) (l₁ l₂ : Terms) (hp : p ≠ 0) :
    mulTermsStr (encNat p) (encTerms l₁) (encTerms l₂) = encTerms (RootData.mulTerms p l₁ l₂) := by
  have hrow : ∀ s : ℕ × ℕ, mapBlocks (prodBlock (encNat p) (encTerm s)) (encTerms l₂) =
      encTerms (l₂.map fun t ↦ ((s.1 * t.1) % p, s.2 + t.2)) := by
    intro s
    rw [encTerms_eq_frame l₂, mapBlocks_frame, encTerms_eq_frame, List.map_map, List.map_map]
    exact congrArg frame (List.map_congr_left fun t _ ↦ prodBlock_encTerm p s t hp)
  rw [mulTermsStr, encTerms_eq_frame l₁, mapBlocks_frame, flattenBlocks_frame, RootData.mulTerms,
    List.flatMap_def, encTerms_flatten, List.map_map, List.map_map]
  exact congrArg List.flatten (List.map_congr_left fun s _ ↦ hrow s)

theorem cobham_mulTermsStr_comp {n : ℕ} {gp g₁ g₂ : (Fin n → List Bool) → List Bool}
    (hp : Cobham gp) (h₁ : Cobham g₁) (h₂ : Cobham g₂) :
    Cobham fun v : Fin n → List Bool ↦ mulTermsStr (gp v) (g₁ v) (g₂ v) := by
  unfold mulTermsStr
  refine cobham_flattenBlocks_comp ?_
  refine cobham_mapBlocks_comp (F := fun b v ↦ mapBlocks (prodBlock (gp v) b) (g₂ v)) ?_ h₁
  refine cobham_mapBlocks_comp (F := fun b' u ↦ prodBlock (gp (Fin.tail u)) (u 0) b') ?_
    (cobham_tail_comp h₂)
  exact cobham_prodBlock_comp (cobham_tail_comp (cobham_tail_comp hp)) (.proj 1) (.proj 0)

/-- One literal of the clause product: the state is `pair remainingLiterals acc`. -/
def clauseStep (p E ℓ w st : List Bool) : List Bool :=
  caseBit₀ (nonemptyFlag (pairFst st))
    (pair (pairSnd (pairFst st))
      (mulTermsStr p (litTermsStr p E ℓ w (pairFst (pairFst st))) (pairSnd st)))
    st

theorem clauseStep_cons (p E : ℕ) (ℓ : List ℕ) (w : ℕ) (l : Lit) (ls : List Lit) (A : Terms)
    (hp : p ≠ 0) :
    clauseStep (encNat p) (encNat E) (frame (ℓ.map encNat)) (encNat w)
        (pair (frame ((l :: ls).map encLitU)) (encTerms A)) =
      pair (frame (ls.map encLitU)) (encTerms (RootData.mulTerms p (rawLitTerms p E ℓ w l) A)) := by
  rw [clauseStep, List.map_cons, frame_cons_eq_pair, pairFst_pair, pairSnd_pair,
    nonemptyFlag_of_ne_nil (pair_ne_nil _ _), caseBit₀_cons, Bool.cond_true, pairFst_pair,
    pairSnd_pair, litTermsStr_eq _ _ _ _ _ hp, mulTermsStr_eq _ _ _ hp]

theorem clauseStep_nil (p E ℓ w A : List Bool) : clauseStep p E ℓ w (pair [] A) = pair [] A := by
  rw [clauseStep, pairFst_pair, nonemptyFlag_nil, caseBit₀_nil]

theorem clauseStep_iterate (p E : ℕ) (ℓ : List ℕ) (w : ℕ) (hp : p ≠ 0) :
    ∀ (k : ℕ) (ls : List Lit) (A : Terms), ls.length ≤ k →
      (clauseStep (encNat p) (encNat E) (frame (ℓ.map encNat)) (encNat w))^[k]
          (pair (frame (ls.map encLitU)) (encTerms A)) =
        pair [] (encTerms (ls.foldl (fun A l ↦ RootData.mulTerms p (rawLitTerms p E ℓ w l) A) A))
  | 0, ls, A, h => by
    rw [List.length_eq_zero_iff.mp (Nat.le_zero.mp h)]
    simp [frame_nil]
  | k + 1, [], A, _ => by
    rw [List.map_nil, frame_nil, Function.iterate_succ_apply, clauseStep_nil, List.foldl_nil]
    exact Function.iterate_fixed (clauseStep_nil _ _ _ _ _) k
  | k + 1, l :: ls, A, h => by
    rw [Function.iterate_succ_apply, clauseStep_cons _ _ _ _ _ _ _ hp,
      clauseStep_iterate p E ℓ w hp k ls _ (by simpa using h), List.foldl_cons]

theorem cobham_clauseStep_comp {n : ℕ} {gp gE gℓ gw gst : (Fin n → List Bool) → List Bool}
    (hp : Cobham gp) (hE : Cobham gE) (hℓ : Cobham gℓ) (hw : Cobham gw) (hst : Cobham gst) :
    Cobham fun v : Fin n → List Bool ↦ clauseStep (gp v) (gE v) (gℓ v) (gw v) (gst v) := by
  have hF := cobham_pairFst_comp hst
  exact Cobham.iteFn (Cobham.nonemptyFn hF)
    (cobham_pair_comp (cobham_pairSnd_comp hF)
      (cobham_mulTermsStr_comp hp (cobham_litTermsStr_comp hp hE hℓ hw (cobham_pairFst_comp hF))
        (cobham_pairSnd_comp hst)))
    hst

/-! ### Scaling -/

/-- Scale one term block by `u`. -/
def scaleBlock (p u b : List Bool) : List Bool := pair (modBits (mulBits u (coefOf b)) p) (expOf b)

/-- `encTerms (scaleTerms p u F)`. -/
def scaleTermsStr (p u F : List Bool) : List Bool := mapBlocks (scaleBlock p u) F

theorem scaleTermsStr_eq (p u : ℕ) (F : Terms) (hp : p ≠ 0) :
    scaleTermsStr (encNat p) (encNat u) (encTerms F) = encTerms (RootData.scaleTerms p u F) := by
  have hp' : decNat (encNat p) ≠ 0 := by rwa [decNat_encNat]
  have hb : ∀ t : ℕ × ℕ,
      scaleBlock (encNat p) (encNat u) (encTerm t) = encTerm ((u * t.1) % p, t.2) := by
    intro t
    simp only [scaleBlock, encTerm, coefOf, expOf, pairFst_pair, pairSnd_pair]
    rw [modBits_eq_encNat _ _ hp', decNat_mulBits, decNat_encNat, decNat_encNat, decNat_encNat]
  rw [scaleTermsStr, encTerms_eq_frame F, mapBlocks_frame, RootData.scaleTerms, encTerms_eq_frame,
    List.map_map, List.map_map]
  exact congrArg frame (List.map_congr_left fun t _ ↦ hb t)

theorem cobham_scaleTermsStr_comp {n : ℕ} {gp gu gF : (Fin n → List Bool) → List Bool}
    (hp : Cobham gp) (hu : Cobham gu) (hF : Cobham gF) :
    Cobham fun v : Fin n → List Bool ↦ scaleTermsStr (gp v) (gu v) (gF v) := by
  unfold scaleTermsStr
  refine cobham_mapBlocks_comp (F := fun b v ↦ scaleBlock (gp v) (gu v) b) ?_ hF
  exact cobham_pair_comp
    (cobham_modBits_comp (cobham_mulBits_comp (cobham_tail_comp hu) (cobham_pairFst_comp (.proj 0)))
      (cobham_tail_comp hp))
    (cobham_pairSnd_comp (.proj 0))

theorem countBlocks_encCNFU (ψ : CNF) : countBlocks (encCNFU ψ) = unaryN ψ.length := by
  rw [encCNFU, countBlocks_frame, List.length_map]

end TermsStr

open TermsStr in
/-- `encTerms (rawRterms p E)`. -/
def RtermsStr (p E : List Bool) : List Bool :=
  termBlock (subBits p [true]) [] ++ termBlock [true] E

theorem RtermsStr_eq (p E : ℕ) : RtermsStr (encNat p) (encNat E) = encTerms (rawRterms p E) := by
  have h1 : decNat (subBits (encNat p) [true]) = p - 1 := by
    rw [decNat_subBits, decNat_encNat, TermsStr.decNat_true]
  rw [RtermsStr, rawRterms, encTerms_cons, encTerms_cons, encTerms_nil, List.append_nil,
    TermsStr.termBlock_eq h1 decNat_nil, TermsStr.termBlock_eq TermsStr.decNat_true (decNat_encNat E)]

theorem cobham_RtermsStr : Cobham fun v : Fin 2 → List Bool ↦ RtermsStr (v 0) (v 1) :=
  Cobham.appendFn
    (TermsStr.cobham_termBlock_comp (cobham_subBits_comp (.proj 0) (Cobham.const [true]))
      (Cobham.const []))
    (TermsStr.cobham_termBlock_comp (Cobham.const [true]) (.proj 1))

open TermsStr in
/-- `encTerms (rawBterms p E ℓ w i)` with `i` unary and `ℓ` framed. -/
def BtermsStr (p E ℓ w i : List Bool) : List Bool :=
  termBlock [true] (addBits (divBits₀ E (primeBlock i ℓ)) (divBits₀ E (primeBlock i ℓ))) ++
    (termBlock (modBits (subBits p (modBits
        (succBits (canonBits (powModStr w (divBits₀ E (primeBlock i ℓ)) p))) p)) p)
      (divBits₀ E (primeBlock i ℓ)) ++
      termBlock (canonBits (powModStr w (divBits₀ E (primeBlock i ℓ)) p)) [])

theorem BtermsStr_eq (p E : ℕ) (ℓ : List ℕ) (w i : ℕ) (hp : p ≠ 0) :
    BtermsStr (encNat p) (encNat E) (frame (ℓ.map encNat)) (encNat w) (unaryN i) =
      encTerms (rawBterms p E ℓ w i) := by
  have hp' : decNat (encNat p) ≠ 0 := by rwa [decNat_encNat]
  have he : TermsStr.divBits₀ (encNat E) (TermsStr.primeBlock (unaryN i) (frame (ℓ.map encNat))) =
      encNat (E / ℓ.getD i 2) := by
    rw [TermsStr.primeBlock_eq, TermsStr.divBits₀_eq_encNat, decNat_encNat, decNat_encNat]
  have hz : decNat (canonBits (powModStr (encNat w) (encNat (E / ℓ.getD i 2)) (encNat p))) =
      powMod w (E / ℓ.getD i 2) p := by
    rw [decNat_canonBits, decNat_powModStr _ _ _ hp', decNat_encNat, decNat_encNat, decNat_encNat]
  have h1 : decNat (addBits (encNat (E / ℓ.getD i 2)) (encNat (E / ℓ.getD i 2))) =
      2 * (E / ℓ.getD i 2) := by
    rw [decNat_addBits, decNat_encNat]
    ring
  have h2 : decNat (modBits (subBits (encNat p) (modBits (succBits
      (canonBits (powModStr (encNat w) (encNat (E / ℓ.getD i 2)) (encNat p)))) (encNat p)))
      (encNat p)) = (p - (1 + powMod w (E / ℓ.getD i 2) p) % p) % p := by
    rw [decNat_modBits _ _ hp', decNat_subBits, decNat_modBits _ _ hp', decNat_succBits, hz,
      decNat_encNat, add_comm]
  rw [BtermsStr, he]
  simp only [rawBterms, encTerms_cons, encTerms_nil, List.append_nil]
  rw [TermsStr.termBlock_eq TermsStr.decNat_true h1, TermsStr.termBlock_eq h2 (decNat_encNat _),
    TermsStr.termBlock_eq hz decNat_nil]

theorem cobham_BtermsStr_comp {n : ℕ} {gp gE gℓ gw gi : (Fin n → List Bool) → List Bool}
    (hp : Cobham gp) (hE : Cobham gE) (hℓ : Cobham gℓ) (hw : Cobham gw) (hi : Cobham gi) :
    Cobham fun v : Fin n → List Bool ↦ BtermsStr (gp v) (gE v) (gℓ v) (gw v) (gi v) := by
  have he := TermsStr.cobham_divBits₀_comp hE (TermsStr.cobham_primeBlock_comp hi hℓ)
  have hz := cobham_canonBits_comp (TermsStr.cobham_powModStr_comp hw he hp)
  exact Cobham.appendFn (TermsStr.cobham_termBlock_comp (Cobham.const [true]) (cobham_addBits_comp he he))
    (Cobham.appendFn
      (TermsStr.cobham_termBlock_comp
        (cobham_modBits_comp (cobham_subBits_comp hp (cobham_modBits_comp (cobham_succBits_comp hz) hp))
          hp) he)
      (TermsStr.cobham_termBlock_comp hz (Cobham.const [])))

open TermsStr in
/-- `encTerms (rawClauseTerms p E ℓ w c)` with `c` in the internal clause encoding (clauses of at
most three literals; the product is unrolled three times from the reversed literal list, matching
the `foldr` of `rawClauseTerms`). -/
def clauseTermsStr (p E ℓ w c : List Bool) : List Bool :=
  pairSnd ((clauseStep p E ℓ w)^[3] (pair (revBlocks c) (delimit (pair [true] []))))

theorem clauseTermsStr_eq (p E : ℕ) (ℓ : List ℕ) (w : ℕ) (c : Clause) (hp : p ≠ 0)
    (hc : c.length ≤ 3) :
    clauseTermsStr (encNat p) (encNat E) (frame (ℓ.map encNat)) (encNat w) (encClauseU c) =
      encTerms (rawClauseTerms p E ℓ w c) := by
  rw [clauseTermsStr, encClauseU, TermsStr.revBlocks_frame, ← List.map_reverse,
    ← TermsStr.encTerms_one_zero,
    TermsStr.clauseStep_iterate p E ℓ w hp 3 c.reverse [(1, 0)] (by simpa using hc), pairSnd_pair,
    rawClauseTerms, List.foldl_reverse, List.foldr_map]

theorem cobham_clauseTermsStr_comp {n : ℕ} {gp gE gℓ gw gc : (Fin n → List Bool) → List Bool}
    (hp : Cobham gp) (hE : Cobham gE) (hℓ : Cobham gℓ) (hw : Cobham gw) (hc : Cobham gc) :
    Cobham fun v : Fin n → List Bool ↦ clauseTermsStr (gp v) (gE v) (gℓ v) (gw v) (gc v) := by
  unfold clauseTermsStr
  refine cobham_pairSnd_comp ?_
  refine TermsStr.cobham_iterate
    (f := fun s v ↦ TermsStr.clauseStep (gp v) (gE v) (gℓ v) (gw v) s) ?_
    (cobham_pair_comp (TermsStr.cobham_revBlocks_comp hc) (Cobham.const _)) 3
  exact TermsStr.cobham_clauseStep_comp (TermsStr.cobham_tail_comp hp) (TermsStr.cobham_tail_comp hE)
    (TermsStr.cobham_tail_comp hℓ) (TermsStr.cobham_tail_comp hw) (.proj 0)

open TermsStr in
/-- The framed list of encoded constraint term lists, from `(p, E, ℓ, w, unary m, encCNFU ψ)`. -/
def constraintTermsStr (p E ℓ w m ψ : List Bool) : List Bool :=
  mapBlocks (fun b ↦ BtermsStr p E ℓ w b) (idxBlocks m) ++
    mapBlocks (fun b ↦ clauseTermsStr p E ℓ w b) ψ

theorem constraintTermsStr_eq (p E : ℕ) (ℓ : List ℕ) (w m : ℕ) (ψ : CNF) (hp : p ≠ 0)
    (hψ : BoundedClauses ψ) :
    constraintTermsStr (encNat p) (encNat E) (frame (ℓ.map encNat)) (encNat w) (unaryN m) (encCNFU ψ) =
      frame ((rawConstraintTerms p E ℓ w m ψ).map encTerms) := by
  rw [constraintTermsStr, TermsStr.idxBlocks_unaryN, mapBlocks_frame, encCNFU, mapBlocks_frame,
    rawConstraintTerms, List.map_append, frame_append]
  simp only [List.map_map]
  exact congrArg₂ (· ++ ·)
    (congrArg frame (List.map_congr_left fun i _ ↦ BtermsStr_eq p E ℓ w i hp))
    (congrArg frame (List.map_congr_left fun c hc ↦ clauseTermsStr_eq p E ℓ w c hp (hψ c hc)))

theorem cobham_constraintTermsStr_comp {n : ℕ}
    {gp gE gℓ gw gm gψ : (Fin n → List Bool) → List Bool}
    (hp : Cobham gp) (hE : Cobham gE) (hℓ : Cobham gℓ) (hw : Cobham gw) (hm : Cobham gm)
    (hψ : Cobham gψ) :
    Cobham fun v : Fin n → List Bool ↦
      constraintTermsStr (gp v) (gE v) (gℓ v) (gw v) (gm v) (gψ v) := by
  unfold constraintTermsStr
  refine Cobham.appendFn ?_ ?_
  · refine TermsStr.cobham_mapBlocks_comp (F := fun b v ↦ BtermsStr (gp v) (gE v) (gℓ v) (gw v) b) ?_
      (TermsStr.cobham_idxBlocks_comp hm)
    exact cobham_BtermsStr_comp (TermsStr.cobham_tail_comp hp) (TermsStr.cobham_tail_comp hE)
      (TermsStr.cobham_tail_comp hℓ) (TermsStr.cobham_tail_comp hw) (.proj 0)
  · refine TermsStr.cobham_mapBlocks_comp
      (F := fun b v ↦ clauseTermsStr (gp v) (gE v) (gℓ v) (gw v) b) ?_ hψ
    exact cobham_clauseTermsStr_comp (TermsStr.cobham_tail_comp hp) (TermsStr.cobham_tail_comp hE)
      (TermsStr.cobham_tail_comp hℓ) (TermsStr.cobham_tail_comp hw) (.proj 0)

open TermsStr in
/-- `encTerms (Hterms p us Fs)` from the framed coefficient list and the framed constraint list. -/
def HtermsStr (p us Fs : List Bool) : List Bool :=
  flattenBlocks (mapBlocks (fun b ↦ scaleTermsStr p (pairFst b) (pairSnd b)) (zipBlocks us Fs))

theorem HtermsStr_eq (p : ℕ) (us : List ℕ) (Fs : List Terms) (hp : p ≠ 0) :
    HtermsStr (encNat p) (frame (us.map encNat)) (frame (Fs.map encTerms)) =
      encTerms (RootData.Hterms p us Fs) := by
  rw [HtermsStr, TermsStr.zipBlocks_frame, mapBlocks_frame, TermsStr.flattenBlocks_frame,
    RootData.Hterms, TermsStr.encTerms_flatten]
  congr 1
  induction us generalizing Fs with
  | nil => simp
  | cons u us ih =>
    cases Fs with
    | nil => simp
    | cons F Fs =>
      simp only [List.map_cons, List.zipWith_cons_cons, pairFst_pair, pairSnd_pair,
        TermsStr.scaleTermsStr_eq _ _ _ hp, ih]

theorem cobham_HtermsStr_comp {n : ℕ} {gp gus gFs : (Fin n → List Bool) → List Bool}
    (hp : Cobham gp) (hus : Cobham gus) (hFs : Cobham gFs) :
    Cobham fun v : Fin n → List Bool ↦ HtermsStr (gp v) (gus v) (gFs v) := by
  unfold HtermsStr
  refine TermsStr.cobham_flattenBlocks_comp ?_
  refine TermsStr.cobham_mapBlocks_comp
    (F := fun b v ↦ TermsStr.scaleTermsStr (gp v) (pairFst b) (pairSnd b)) ?_
    (TermsStr.cobham_zipBlocks_comp hus hFs)
  exact TermsStr.cobham_scaleTermsStr_comp (TermsStr.cobham_tail_comp hp)
    (cobham_pairFst_comp (.proj 0)) (cobham_pairSnd_comp (.proj 0))

/-- Normalization (the `SparseDivComplexity` support modules' `normalizeStr`) on encoded terms, followed by canonicalization of the
merged coefficient numerals (`addBits` does not produce canonical numerals). -/
theorem normalizeStr_encTerms (p : ℕ) (l : Terms) (hp : 0 < p) (hl : ∀ t ∈ l, t.1 < p) :
    TermsStr.canonTermsStr (normalizeStr (encNat p) (encTerms l)) = encTerms (normalize p l) := by
  have hts : ∀ t ∈ l.map (fun t : ℕ × ℕ ↦ (encNat t.1, encNat t.2)),
      decNat t.1 < decNat (encNat p) := by
    intro t ht
    obtain ⟨s, hs, rfl⟩ := List.mem_map.mp ht
    simpa using hl s hs
  rw [TermsStr.encTerms_eq_frameTerms, normalizeStr_frameTerms, TermsStr.canonTermsStr_frameTerms,
    decodeTerms_normalizeS _ hts, TermsStr.decodeTerms_encode, decNat_encNat,
    normalizeL_eq_normalize hp]

open TermsStr in
/-- `encTerms (buildH …)` from `(p, E, ℓ, w, unary m, encCNFU ψ, unary B, bits)`. -/
def buildHStr (p E ℓ w m ψ B bits : List Bool) : List Bool :=
  canonTermsStr (normalizeStr p (HtermsStr p (samplesStr p (m ++ countBlocks ψ) B bits)
    (constraintTermsStr p E ℓ w m ψ)))

theorem buildHStr_eq (p E : ℕ) (ℓ : List ℕ) (w m : ℕ) (ψ : CNF) (B : ℕ) (bits : List Bool)
    (hp : 0 < p) (hψ : BoundedClauses ψ) :
    buildHStr (encNat p) (encNat E) (frame (ℓ.map encNat)) (encNat w) (unaryN m) (encCNFU ψ)
        (unaryN B) bits =
      encTerms (buildH p E ℓ w m ψ B bits) := by
  have hp' : p ≠ 0 := hp.ne'
  have hp'' : decNat (encNat p) ≠ 0 := by rwa [decNat_encNat]
  have ht : unaryN m ++ TermsStr.countBlocks (encCNFU ψ) = unaryN (m + ψ.length) := by
    rw [TermsStr.countBlocks_encCNFU]
    simp only [unaryN, List.replicate_add]
  rw [buildHStr, ht, samplesStr_eq _ _ _ _ hp'', decNat_encNat,
    constraintTermsStr_eq _ _ _ _ _ _ hp' hψ, HtermsStr_eq _ _ _ hp', buildH,
    normalizeStr_encTerms _ _ hp]
  intro t ht
  obtain ⟨u, -, F, -, s, -, rfl⟩ := RootData.exists_of_mem_Hterms ht
  exact Nat.mod_lt _ hp

theorem cobham_buildHStr :
    Cobham fun v : Fin 8 → List Bool ↦
      buildHStr (v 0) (v 1) (v 2) (v 3) (v 4) (v 5) (v 6) (v 7) := by
  have hFs := cobham_constraintTermsStr_comp (n := 8) (.proj 0) (.proj 1) (.proj 2) (.proj 3)
    (.proj 4) (.proj 5)
  have ht := Cobham.appendFn (Cobham.proj (n := 8) 4) (TermsStr.cobham_countBlocks_comp (.proj 5))
  have hus := TermsStr.cobham_samplesStr_comp (.proj 0) ht (.proj 6) (.proj 7)
  exact TermsStr.cobham_canonTermsStr_comp
    (cobham_normalizeStr_comp (.proj 0) (cobham_HtermsStr_comp (.proj 0) hus hFs))

end SparseGcd
