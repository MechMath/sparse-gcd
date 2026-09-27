import SparseGcd.Machine.TrialData
import SparseDivComplexity.StringArith.Gcd
import SparseDivComplexity.StringArith.Blocks
import SparseDivComplexity.BridgeString.Complexity

/-!
# Field arithmetic and sampling as strings (Cobham layer)

Binary numerals are LSB-first lists (`SparseDiv.encNat`/`decNat`); `Complexity.pair`/`delimit`
frames are used for lists. Everything here is proved (a) correct with respect to the data-level
functions of `Machine/TrialData.lean` and (b) in `FP` (through Cobham's algebra).

## Implementation notes

* `redStr x p` is the *total* reduction modulo `p` (`[]` when `p` denotes `0`), `divStr` the total
  quotient (`[]` on a zero divisor, matching `n / 0 = 0`); both are canonical numerals, which keeps
  every loop state short.
* `powModStr` is a recursion on the notation of the exponent (MSB-first square-and-multiply).
* The loops (`takeBlocksStr`, `nthBlockStr`, `samplesStr`, the first-success search `searchLoop`
  behind `findOmegaStr`/`packageStr`, `unaryToBinStr`) are clocked iterations
  (`Complexity.Cobham.iterFn`) over a unary counter; their length side conditions are discharged
  by trajectory invariants that hold for *all* inputs.
-/

open Complexity SparseDiv SparseDiv.StringArith

namespace SparseGcd

/-! ### Generic Cobham helpers -/

/-- Reindexing the arguments of a member of the class. -/
theorem cobham_reindex {m n : ℕ} {f : (Fin m → List Bool) → List Bool} (hf : Cobham f)
    (σ : Fin m → Fin n) : Cobham fun v : Fin n → List Bool ↦ f fun i ↦ v (σ i) :=
  Cobham.comp hf fun i ↦ Cobham.proj (σ i)

/-- A function of the parameters, as a function of the state and the parameters. -/
theorem cobham_tail_comp {n : ℕ} {g : (Fin n → List Bool) → List Bool} (hg : Cobham g) :
    Cobham fun w : Fin (n + 1) → List Bool ↦ g (Fin.tail w) :=
  (Cobham.comp hg fun i ↦ Cobham.proj i.succ).of_eq fun _ ↦ rfl

/-- Substituting a member of the class for the first argument of another. -/
theorem cobham_consArg {n : ℕ} {g : (Fin (n + 1) → List Bool) → List Bool} (hg : Cobham g)
    {h : (Fin (n + 1) → List Bool) → List Bool} (hh : Cobham h) :
    Cobham fun w : Fin (n + 1) → List Bool ↦ g (Fin.cons (h w) (Fin.tail w)) := by
  refine (Cobham.comp hg (gs := fun i (w : Fin (n + 1) → List Bool) ↦
    (Fin.cons (h w) (Fin.tail w) : Fin (n + 1) → List Bool) i) ?_).of_eq fun w ↦ rfl
  intro i
  refine Fin.cases ?_ (fun i ↦ ?_) i
  · exact hh
  · exact Cobham.proj i.succ

theorem cobham_smash_comp {n : ℕ} {g₀ g₁ : (Fin n → List Bool) → List Bool}
    (h₀ : Cobham g₀) (h₁ : Cobham g₁) :
    Cobham fun v : Fin n → List Bool ↦ Complexity.smash (g₀ v) (g₁ v) :=
  (Cobham.comp₂ Cobham.smash h₀ h₁).of_eq fun v ↦ by simp

theorem cobham_delimit_comp {n : ℕ} {g : (Fin n → List Bool) → List Bool} (hg : Cobham g) :
    Cobham fun v : Fin n → List Bool ↦ delimit (g v) :=
  (cobham_pair_comp hg (Cobham.const [])).of_eq fun v ↦ by simp [pair]

/-! ### Elementary facts -/

theorem caseBit₀_cases (s x y : List Bool) : caseBit₀ s x y = x ∨ caseBit₀ s x y = y := by
  cases s with
  | nil => exact Or.inr rfl
  | cons b s => cases b <;> simp

theorem andBit_length (x y : List Bool) : (andBit x y).length = 1 := by
  rcases andBit_flag x y with h | h <;> simp [h]

theorem frame_cons_eq_pair (b : List Bool) (bs : List (List Bool)) :
    frame (b :: bs) = pair b (frame bs) := rfl

theorem length_pairFst_le : ∀ z : List Bool, (pairFst z).length ≤ z.length
  | [] => by simp [pairFst]
  | [b] => by cases b <;> simp [pairFst]
  | false :: false :: z => by
    have := length_pairFst_le z
    simp [pairFst]
    omega
  | true :: true :: z => by
    have := length_pairFst_le z
    simp [pairFst]
    omega
  | false :: true :: z => by simp [pairFst]
  | true :: false :: z => by simp [pairFst]

theorem isZeroBits_eq_false {p : List Bool} (hp : decNat p ≠ 0) : isZeroBits p = [false] := by
  rcases isZeroBits_flag p with h | h
  · exact absurd ((isZeroBits_eq_true_iff p).mp h) hp
  · exact h

theorem eqBits_eq_decide (a b : List Bool) : eqBits a b = [decide (decNat a = decNat b)] := by
  rcases eqBits_flag a b with h | h
  · rw [h, decide_eq_true ((eqBits_eq_true_iff a b).mp h)]
  · rw [h]
    have hne : ¬ decNat a = decNat b := fun heq ↦ by
      rw [(eqBits_eq_true_iff a b).mpr heq] at h
      simp at h
    rw [decide_eq_false hne]

theorem hasBlockFlag_flag (s : List Bool) : hasBlockFlag s = [true] ∨ hasBlockFlag s = [false] :=
  Cobham.eqFlag_flag _ _

theorem validBlocksFlag_flag (s : List Bool) :
    validBlocksFlag s = [true] ∨ validBlocksFlag s = [false] :=
  Cobham.eqFlag_flag _ _

/-! ### Total reduction and division -/

/-- Total reduction modulo `p`: the canonical numeral of `x mod p`, `[]` when `p` denotes `0`. -/
def redStr (x p : List Bool) : List Bool := caseBit₀ (isZeroBits p) [] (modBits x p)

theorem redStr_eq_encNat (x p : List Bool) (hp : decNat p ≠ 0) :
    redStr x p = encNat (decNat x % decNat p) := by
  rw [redStr, isZeroBits_eq_false hp, caseBit₀_cons, Bool.cond_false, modBits, divModVal_spec x p hp]

theorem decNat_redStr (x p : List Bool) (hp : decNat p ≠ 0) :
    decNat (redStr x p) = decNat x % decNat p := by
  rw [redStr_eq_encNat x p hp, decNat_encNat]

theorem length_redStr_le (x p : List Bool) : (redStr x p).length ≤ p.length := by
  by_cases hp : decNat p = 0
  · rw [redStr, (isZeroBits_eq_true_iff p).mpr hp]
    simp
  · rw [redStr_eq_encNat x p hp]
    exact length_encNat_le_of_lt
      ((Nat.mod_lt _ (Nat.pos_of_ne_zero hp)).trans (decNat_lt_two_pow_length p))

theorem cobham_redStr_comp {n : ℕ} {gx gp : (Fin n → List Bool) → List Bool}
    (hx : Cobham gx) (hp : Cobham gp) :
    Cobham fun v : Fin n → List Bool ↦ redStr (gx v) (gp v) :=
  Cobham.iteFn (cobham_isZeroBits_comp hp) (Cobham.const []) (cobham_modBits_comp hx hp)

/-- Total quotient: `[]` on a zero divisor (matching `n / 0 = 0`). -/
def divStr (x q : List Bool) : List Bool := caseBit₀ (isZeroBits q) [] (divBits x q)

theorem decNat_divStr (x q : List Bool) : decNat (divStr x q) = decNat x / decNat q := by
  by_cases hq : decNat q = 0
  · rw [divStr, (isZeroBits_eq_true_iff q).mpr hq, hq, Nat.div_zero]
    simp
  · rw [divStr, isZeroBits_eq_false hq, caseBit₀_cons, Bool.cond_false, decNat_divBits x q hq]

theorem cobham_divStr_comp {n : ℕ} {gx gq : (Fin n → List Bool) → List Bool}
    (hx : Cobham gx) (hq : Cobham gq) :
    Cobham fun v : Fin n → List Bool ↦ divStr (gx v) (gq v) :=
  Cobham.iteFn (cobham_isZeroBits_comp hq) (Cobham.const []) (cobham_divBits_comp hx hq)

/-! ### Modular exponentiation -/

/-- `b^e mod p` by recursion on the notation of `e` (MSB-first square-and-multiply); every
intermediate value is reduced modulo `p`. -/
def powModAux (b p : List Bool) : List Bool → List Bool
  | [] => redStr [true] p
  | false :: x => redStr (mulBits (powModAux b p x) (powModAux b p x)) p
  | true :: x => redStr (mulBits (mulBits (powModAux b p x) (powModAux b p x)) b) p

/-- Modular exponentiation `b^e mod p` (square-and-multiply along the bits of `e`). -/
def powModStr (b e p : List Bool) : List Bool := powModAux b p e

theorem powModAux_eq_encNat (b p e : List Bool) (hp : decNat p ≠ 0) :
    powModAux b p e = encNat (decNat b ^ decNat e % decNat p) := by
  induction e with
  | nil => simp [powModAux, redStr_eq_encNat _ _ hp, decNat_cons]
  | cons bit x ih =>
    cases bit
    · rw [powModAux, redStr_eq_encNat _ _ hp, decNat_mulBits, ih, decNat_encNat, decNat_cons]
      congr 1
      have h : decNat b ^ ((if false then 1 else 0) + 2 * decNat x) =
          decNat b ^ decNat x * decNat b ^ decNat x := by
        simp only [Bool.false_eq_true, ↓reduceIte, zero_add]
        ring
      rw [h]
      exact (Nat.mod_modEq _ _).mul (Nat.mod_modEq _ _)
    · rw [powModAux, redStr_eq_encNat _ _ hp, decNat_mulBits, decNat_mulBits, ih, decNat_encNat,
        decNat_cons]
      congr 1
      have h : decNat b ^ ((if true then 1 else 0) + 2 * decNat x) =
          decNat b ^ decNat x * decNat b ^ decNat x * decNat b := by
        simp only [↓reduceIte]
        ring
      rw [h]
      exact ((Nat.mod_modEq _ _).mul (Nat.mod_modEq _ _)).mul (Nat.ModEq.refl _)

theorem powModStr_eq_encNat (b e p : List Bool) (hp : decNat p ≠ 0) :
    powModStr b e p = encNat (powMod (decNat b) (decNat e) (decNat p)) :=
  powModAux_eq_encNat b p e hp

theorem decNat_powModStr (b e p : List Bool) (hp : decNat p ≠ 0) :
    decNat (powModStr b e p) = powMod (decNat b) (decNat e) (decNat p) := by
  rw [powModStr_eq_encNat b e p hp, decNat_encNat]

theorem length_powModAux_le (b p e : List Bool) : (powModAux b p e).length ≤ p.length := by
  cases e with
  | nil => exact length_redStr_le _ _
  | cons bit x => cases bit <;> exact length_redStr_le _ _

theorem length_powModStr_le (b e p : List Bool) : (powModStr b e p).length ≤ p.length + 2 :=
  (length_powModAux_le b p e).trans (by omega)

/-- The exponentiation as a recursion on notation on the exponent, with parameters `(b, p)`. -/
theorem recNotation_powModAux (e : List Bool) (v : Fin 2 → List Bool) :
    recNotation (fun u : Fin 2 → List Bool ↦ redStr [true] (u 1))
      (fun w : Fin 4 → List Bool ↦ redStr (mulBits (w 1) (w 1)) (w 3))
      (fun w : Fin 4 → List Bool ↦ redStr (mulBits (mulBits (w 1) (w 1)) (w 2)) (w 3)) e v =
      powModAux (v 0) (v 1) e := by
  induction e with
  | nil => rfl
  | cons bit x ih =>
    cases bit
    · show redStr (mulBits (recNotation _ _ _ x v) (recNotation _ _ _ x v)) (v 1) = _
      rw [ih]
      rfl
    · show redStr (mulBits (mulBits (recNotation _ _ _ x v) (recNotation _ _ _ x v)) (v 0))
        (v 1) = _
      rw [ih]
      rfl

theorem cobham_powModStr : Cobham fun v : Fin 3 → List Bool ↦ powModStr (v 0) (v 1) (v 2) := by
  have hg : Cobham fun u : Fin 2 → List Bool ↦ redStr [true] (u 1) :=
    cobham_redStr_comp (Cobham.const [true]) (.proj 1)
  have h₀ : Cobham fun w : Fin 4 → List Bool ↦ redStr (mulBits (w 1) (w 1)) (w 3) :=
    cobham_redStr_comp (cobham_mulBits_comp (.proj 1) (.proj 1)) (.proj 3)
  have h₁ : Cobham fun w : Fin 4 → List Bool ↦
      redStr (mulBits (mulBits (w 1) (w 1)) (w 2)) (w 3) :=
    cobham_redStr_comp (cobham_mulBits_comp (cobham_mulBits_comp (.proj 1) (.proj 1)) (.proj 2))
      (.proj 3)
  have hrec := Cobham.boundedRec hg h₀ h₁ (Cobham.proj (2 : Fin 3)) (by
    intro x v
    rw [recNotation_powModAux]
    exact length_powModAux_le _ _ _)
  exact (Cobham.comp₃ hrec (.proj 1) (.proj 0) (.proj 2)).of_eq fun v ↦ by
    rw [recNotation_powModAux]
    rfl

theorem cobham_powModStr_comp {n : ℕ} {g₀ g₁ g₂ : (Fin n → List Bool) → List Bool}
    (h₀ : Cobham g₀) (h₁ : Cobham g₁) (h₂ : Cobham g₂) :
    Cobham fun v : Fin n → List Bool ↦ powModStr (g₀ v) (g₁ v) (g₂ v) :=
  (Cobham.comp₃ cobham_powModStr h₀ h₁ h₂).of_eq fun _ ↦ rfl

/-! ### Products -/

/-- Product of a framed list of numerals. -/
def prodStr (s : List Bool) : List Bool :=
  foldBlocks (fun acc b ↦ canonBits (mulBits acc b)) [true] s

theorem foldl_canonBits_mulBits (ℓ : List ℕ) : ∀ acc : List Bool,
    decNat ((ℓ.map encNat).foldl (fun acc b ↦ canonBits (mulBits acc b)) acc) =
      decNat acc * ℓ.prod := by
  induction ℓ with
  | nil => intro acc; simp
  | cons q ℓ ih =>
    intro acc
    rw [List.map_cons, List.foldl_cons, ih, decNat_canonBits, decNat_mulBits, decNat_encNat,
      List.prod_cons]
    ring

theorem decNat_prodStr (ℓ : List ℕ) : decNat (prodStr (frame (ℓ.map encNat))) = ℓ.prod := by
  rw [prodStr, foldBlocks_frame, foldl_canonBits_mulBits]
  simp [decNat_cons]

theorem length_canonBits_mulBits_le (a b : List Bool) :
    (canonBits (mulBits a b)).length ≤ a.length + b.length := by
  rw [canonBits, decNat_mulBits]
  apply length_encNat_le_of_lt
  rw [pow_add]
  exact Nat.mul_lt_mul'' (decNat_lt_two_pow_length a) (decNat_lt_two_pow_length b)

theorem cobham_prodStr : Cobham fun v : Fin 1 → List Bool ↦ prodStr (v 0) := by
  have hstep : Cobham fun w : Fin 2 → List Bool ↦ canonBits (mulBits (w 0) (w 1)) :=
    cobham_canonBits_comp (cobham_mulBits_comp (.proj 0) (.proj 1))
  refine (cobham_foldBlocks (n := 0) hstep (init := fun _ ↦ [true]) (Cobham.const [true]) 1
    fun w ↦ ?_).of_eq fun v ↦ rfl
  have := length_canonBits_mulBits_le (w 0) (w 1)
  omega

/-! ### Taking and indexing blocks -/

/-- The first `|m|` blocks of a framed list (`m` unary). -/
def takeBlocksStr (m s : List Bool) : List Bool :=
  pairSnd ((blockStep (fun acc b ↦ acc ++ delimit b) (pair [] []))^[m.length] (pair s []))

theorem takeBlocksStr_frame (m : ℕ) (bs : List (List Bool)) :
    takeBlocksStr (unaryN m) (frame bs) = frame (bs.take m) := by
  rw [takeBlocksStr, unaryN, List.length_replicate,
    blockStep_iterate_of_nil _ _ (List.append_nil (frame bs)).symm rfl [] m, pairSnd_pair]
  have := foldl_append_delimit id (bs.take m) []
  simpa using this

theorem cobham_takeBlocksStr : Cobham fun v : Fin 2 → List Bool ↦ takeBlocksStr (v 0) (v 1) := by
  have hg : Cobham fun x : Fin 3 → List Bool ↦ x 0 ++ delimit (x 1) :=
    Cobham.appendFn (.proj 0) (cobham_delimit_comp (.proj 1))
  have hstep : Cobham fun w : Fin 2 → List Bool ↦
      blockStep (fun acc b ↦ acc ++ delimit b) (pair [] []) (w 0) :=
    (cobham_blockStep (n := 1) hg (bad := fun _ ↦ pair [] []) (Cobham.const _)).of_eq
      fun w ↦ rfl
  have he : Cobham fun u : Fin 1 → List Bool ↦ pair (u 0) [] :=
    cobham_pair_comp (.proj 0) (Cobham.const [])
  have hruler : Cobham fun u : Fin 1 → List Bool ↦
      false :: false :: (u 0 ++ u 0) ++ Complexity.smash (u 0) (u 0) :=
    Cobham.appendFn (cobham_cons false (cobham_cons false (Cobham.appendFn (.proj 0) (.proj 0))))
      (cobham_smash_comp (.proj 0) (.proj 0))
  have hiter := Cobham.iterFn he hstep (cobham_tail_comp hruler) (by
    intro c v
    simp only [Fin.tail_cons, Fin.cons_zero]
    refine le_trans (blockStep_iterate_length_le _ _ (blockStep_pair_nil _ _ _) (v 0) []
      (v 0).length ?_ ?_ c.length) ?_
    · intro acc b hb
      simp only [List.length_append, delimit_length]
      omega
    · simp only [pair_length, List.length_nil]
      omega
    · simp only [List.length_append, List.length_cons, List.length_nil, smash_length]
      omega)
  exact (cobham_pairSnd_comp hiter).of_eq fun v ↦ rfl

/-- The `|i|`-th block of a framed list (`i` unary), `[]` if absent. -/
def nthBlockStr (i s : List Bool) : List Bool := pairFst (pairSnd^[i.length] s)

theorem pairSnd_iterate_frame (k : ℕ) : ∀ bs : List (List Bool),
    pairSnd^[k] (frame bs) = frame (bs.drop k) := by
  induction k with
  | zero => intro bs; rfl
  | succ k ih =>
    intro bs
    cases bs with
    | nil =>
      have h0 : pairSnd [] = [] := rfl
      rw [Function.iterate_succ_apply, frame_nil, h0]
      simpa [frame_nil] using ih []
    | cons b bs =>
      rw [Function.iterate_succ_apply, frame_cons_eq_pair, pairSnd_pair, ih, List.drop_succ_cons]

theorem nthBlockStr_frame (i : ℕ) (bs : List (List Bool)) :
    nthBlockStr (unaryN i) (frame bs) = bs.getD i [] := by
  rw [nthBlockStr, unaryN, List.length_replicate, pairSnd_iterate_frame]
  rcases h : bs.drop i with _ | ⟨b, rest⟩
  · rw [frame_nil, List.getD_eq_default bs [] (List.drop_eq_nil_iff.mp h)]
    rfl
  · have hb : bs[i]? = some b := by
      rw [← Nat.add_zero i, ← List.getElem?_drop, h]
      rfl
    rw [frame_cons_eq_pair, pairFst_pair, List.getD_eq_getElem?_getD, hb]
    rfl

theorem length_pairSnd_iterate_le (k : ℕ) (s : List Bool) : (pairSnd^[k] s).length ≤ s.length := by
  induction k with
  | zero => exact le_rfl
  | succ k ih =>
    rw [Function.iterate_succ_apply']
    exact (pairSnd_length_le _).trans ih

theorem cobham_nthBlockStr : Cobham fun v : Fin 2 → List Bool ↦ nthBlockStr (v 0) (v 1) := by
  have hf : Cobham fun w : Fin 2 → List Bool ↦ pairSnd (w 0) := cobham_pairSnd_comp (.proj 0)
  have hiter := Cobham.iterFn (n := 1) (Cobham.proj 0) hf (cobham_tail_comp (Cobham.proj 0)) (by
    intro c v
    simp only [Fin.tail_cons, Fin.cons_zero]
    exact length_pairSnd_iterate_le _ _)
  exact (cobham_pairFst_comp hiter).of_eq fun v ↦ rfl

/-! ### Fixed-width samples -/

/-- One step of the sampling loop on the state `pair rem acc`: reduce the next `|B|` bits modulo
`p` and append the framed canonical numeral to the accumulator. -/
def sampleStep (p B st : List Bool) : List Bool :=
  pair ((pairFst st).drop B.length)
    (pairSnd st ++ delimit (redStr ((pairFst st).take B.length) p))

/-- Fixed-width samples: the framed list of the `|t|` blocks of width `|B|` of `bits`
(`t`, `B` unary), each reduced modulo `p` (as a canonical numeral). -/
def samplesStr (p t B bits : List Bool) : List Bool :=
  pairSnd ((sampleStep p B)^[t.length] (pair bits []))

theorem coeffs_succ (p B t : ℕ) (bits : List Bool) :
    coeffs p B (t + 1) bits = (decNat (bits.take B) % p) :: coeffs p B t (bits.drop B) := by
  rw [coeffs, coeffs, List.range_succ_eq_map, List.map_cons, List.map_map]
  congr 1
  · simp [sampleMod, block]
  · apply List.map_congr_left
    intro i _
    show decNat (List.take B (List.drop ((i + 1) * B) bits)) % p =
      decNat (List.take B (List.drop (i * B) (List.drop B bits))) % p
    rw [List.drop_drop, show (i + 1) * B = B + i * B by ring]

theorem sampleStep_iterate (p B : List Bool) (hp : decNat p ≠ 0) (t : ℕ) :
    ∀ bits acc : List Bool, (sampleStep p B)^[t] (pair bits acc) =
      pair (bits.drop (t * B.length))
        (acc ++ frame ((coeffs (decNat p) B.length t bits).map encNat)) := by
  induction t with
  | zero => intro bits acc; simp [coeffs, frame]
  | succ t ih =>
    intro bits acc
    rw [Function.iterate_succ_apply, sampleStep, pairFst_pair, pairSnd_pair, ih, List.drop_drop,
      coeffs_succ, List.map_cons, frame_cons, redStr_eq_encNat _ _ hp, List.append_assoc,
      show B.length + t * B.length = (t + 1) * B.length by ring]

theorem samplesStr_eq (p : List Bool) (t B : ℕ) (bits : List Bool) (hp : decNat p ≠ 0) :
    samplesStr p (unaryN t) (unaryN B) bits =
      frame ((coeffs (decNat p) B t bits).map encNat) := by
  simp only [samplesStr, unaryN, List.length_replicate]
  rw [sampleStep_iterate p _ hp, pairSnd_pair, List.length_replicate, List.nil_append]

theorem sampleStep_iterate_length_le (p B bits : List Bool) (k : ℕ) :
    ((sampleStep p B)^[k] (pair bits [])).length ≤
      2 * bits.length + 2 + k * (2 * p.length + 2) := by
  suffices h : ∀ k, ∃ r a : List Bool, (sampleStep p B)^[k] (pair bits []) = pair r a ∧
      r.length ≤ bits.length ∧ a.length ≤ k * (2 * p.length + 2) by
    obtain ⟨r, a, h1, h2, h3⟩ := h k
    rw [h1, pair_length]
    omega
  intro k
  induction k with
  | zero => exact ⟨bits, [], rfl, le_rfl, by simp⟩
  | succ k ih =>
    obtain ⟨r, a, h1, h2, h3⟩ := ih
    refine ⟨r.drop B.length, a ++ delimit (redStr (r.take B.length) p), ?_, ?_, ?_⟩
    · rw [Function.iterate_succ_apply', h1, sampleStep, pairFst_pair, pairSnd_pair]
    · simp only [List.length_drop]
      omega
    · have := length_redStr_le (r.take B.length) p
      have hk : (k + 1) * (2 * p.length + 2) = k * (2 * p.length + 2) + (2 * p.length + 2) := by
        ring
      simp only [List.length_append, delimit_length]
      omega

theorem cobham_sampleStep_comp {n : ℕ} {gp gB gst : (Fin n → List Bool) → List Bool}
    (hp : Cobham gp) (hB : Cobham gB) (hst : Cobham gst) :
    Cobham fun v : Fin n → List Bool ↦ sampleStep (gp v) (gB v) (gst v) :=
  cobham_pair_comp (Cobham.dropFn hB (cobham_pairFst_comp hst))
    (Cobham.appendFn (cobham_pairSnd_comp hst)
      (cobham_delimit_comp (cobham_redStr_comp (Cobham.takeFn hB (cobham_pairFst_comp hst)) hp)))

theorem cobham_samplesStr :
    Cobham fun v : Fin 4 → List Bool ↦ samplesStr (v 0) (v 1) (v 2) (v 3) := by
  -- The loop over `u = (t, p, B, bits)`.
  have he : Cobham fun v : Fin 3 → List Bool ↦ pair (v 2) [] :=
    cobham_pair_comp (.proj 2) (Cobham.const [])
  have hf : Cobham fun w : Fin 4 → List Bool ↦ sampleStep (Fin.tail w 0) (Fin.tail w 1) (w 0) :=
    cobham_sampleStep_comp (cobham_tail_comp (.proj 0)) (cobham_tail_comp (.proj 1)) (.proj 0)
  have hj : Cobham fun w : Fin 4 → List Bool ↦
      false :: false :: (Fin.tail w 2 ++ Fin.tail w 2) ++
        Complexity.smash (w 0) (false :: false :: (Fin.tail w 0 ++ Fin.tail w 0)) :=
    Cobham.appendFn (cobham_cons false (cobham_cons false
        (Cobham.appendFn (cobham_tail_comp (.proj 2)) (cobham_tail_comp (.proj 2)))))
      (cobham_smash_comp (.proj 0) (cobham_cons false (cobham_cons false
        (Cobham.appendFn (cobham_tail_comp (.proj 0)) (cobham_tail_comp (.proj 0))))))
  have hiter := Cobham.iterFn he hf hj (by
    intro c v
    simp only [Fin.tail_cons, Fin.cons_zero]
    refine le_trans (sampleStep_iterate_length_le (v 0) (v 1) (v 2) c.length) ?_
    simp only [List.length_append, List.length_cons, smash_length]
    have h1 : c.length * (2 * (v 0).length + 2) ≤
        c.length * ((v 0).length + (v 0).length + 1 + 1) := Nat.mul_le_mul_left _ (by omega)
    omega)
  exact (cobham_pairSnd_comp (cobham_reindex hiter ![1, 0, 2, 3])).of_eq fun v ↦ rfl

/-! ### The order test -/

/-- The order test on `(p, E, framed ℓ, w)`. -/
def orderTestStr (p E ℓ w : List Bool) : List Bool :=
  andBit (eqBits (powModStr w E p) (redStr [true] p))
    (foldBlocks (fun acc q ↦
      andBit acc (notBit (eqBits (powModStr w (divStr E q) p) (redStr [true] p)))) [true] ℓ)

theorem foldl_andBit_all {α : Type*} (g : α → Bool) :
    ∀ (l : List α) (a : Bool), l.foldl (fun acc q ↦ andBit acc [g q]) [a] = [a && l.all g]
  | [], a => by simp
  | q :: l, a => by
    rw [List.foldl_cons, andBit_single, foldl_andBit_all g l, List.all_cons, Bool.and_assoc]

theorem orderTestStr_eq (p E : List Bool) (ℓ : List ℕ) (w : List Bool) (hp : decNat p ≠ 0) :
    orderTestStr p E (frame (ℓ.map encNat)) w =
      [orderTestNat (decNat p) (decNat E) ℓ (decNat w)] := by
  have h1 : decNat (redStr [true] p) = 1 % decNat p := by
    rw [decNat_redStr _ _ hp]
    simp [decNat_cons]
  have hstep : (fun acc q ↦
      andBit acc (notBit (eqBits (powModStr w (divStr E q) p) (redStr [true] p)))) =
      fun acc q ↦ andBit acc
        [!decide (powMod (decNat w) (decNat E / decNat q) (decNat p) = 1 % decNat p)] := by
    funext acc q
    rw [eqBits_eq_decide, notBit_single, h1, decNat_powModStr _ _ _ hp, decNat_divStr]
  rw [orderTestStr, foldBlocks_frame, hstep, List.foldl_map]
  simp only [decNat_encNat]
  rw [foldl_andBit_all (fun q ↦
    !decide (powMod (decNat w) (decNat E / q) (decNat p) = 1 % decNat p)) ℓ true,
    eqBits_eq_decide, h1, decNat_powModStr _ _ _ hp, andBit_single]
  rfl

theorem cobham_orderTestStr :
    Cobham fun v : Fin 4 → List Bool ↦ orderTestStr (v 0) (v 1) (v 2) (v 3) := by
  -- The fold over `u = (ℓ, p, E, w)`; the step sees `(acc, q, p, E, w)`.
  have hstep : Cobham fun x : Fin 5 → List Bool ↦
      andBit (x 0) (notBit (eqBits (powModStr (x 4) (divStr (x 3) (x 1)) (x 2))
        (redStr [true] (x 2)))) :=
    Cobham.andFn (.proj 0) (Cobham.notFn (cobham_eqBits_comp
      (cobham_powModStr_comp (.proj 4) (cobham_divStr_comp (.proj 3) (.proj 1)) (.proj 2))
      (cobham_redStr_comp (Cobham.const [true]) (.proj 2))))
  have hfold := cobham_foldBlocks (n := 3) hstep (init := fun _ ↦ [true]) (Cobham.const [true]) 1
    (fun w ↦ by rw [andBit_length]; omega)
  have hall := Cobham.andFn (cobham_eqBits_comp (cobham_powModStr_comp (.proj 3) (.proj 2) (.proj 1))
    (cobham_redStr_comp (Cobham.const [true]) (.proj 1))) hfold
  exact (cobham_reindex hall ![2, 0, 1, 3]).of_eq fun v ↦ rfl

/-! ### First-success search over fixed-width blocks -/

/-- One step of a first-success search over width-`|W|` blocks, on the state
`pair flag (pair rem res)`: once the flag is set the state is frozen; otherwise the next block is
tested with `ok`, and on success the result `out` of the block is stored and the flag set. -/
def searchStep (ok out : List Bool → List Bool) (W st : List Bool) : List Bool :=
  caseBit₀ (pairFst st) st
    (caseBit₀ (ok ((pairFst (pairSnd st)).take W.length))
      (pair [true] (pair [] (out ((pairFst (pairSnd st)).take W.length))))
      (pair [false] (pair ((pairFst (pairSnd st)).drop W.length) [])))

/-- The search over `|t|` blocks: `pair [true] res` for the first success, `[false]` otherwise. -/
def searchLoop (ok out : List Bool → List Bool) (t W bits : List Bool) : List Bool :=
  caseBit₀ (pairFst ((searchStep ok out W)^[t.length] (pair [false] (pair bits []))))
    (pair [true] (pairSnd (pairSnd ((searchStep ok out W)^[t.length] (pair [false] (pair bits []))))))
    [false]

theorem searchStep_found (ok out : List Bool → List Bool) (W x : List Bool) :
    searchStep ok out W (pair [true] x) = pair [true] x := by
  simp [searchStep]

theorem searchStep_pending (ok out : List Bool → List Bool) (W bits : List Bool) :
    searchStep ok out W (pair [false] (pair bits [])) =
      caseBit₀ (ok (bits.take W.length)) (pair [true] (pair [] (out (bits.take W.length))))
        (pair [false] (pair (bits.drop W.length) [])) := by
  simp [searchStep]

/-- **Correctness of the search.** `F` is the data-level test/extraction on a block, `enc` the
encoding of its result; `ok`/`out` must agree with `F` blockwise. -/
theorem searchStep_iterate' {α : Type*} (ok out : List Bool → List Bool) (W : List Bool)
    (F : List Bool → Option α) (enc : α → List Bool)
    (hF : ∀ blk, (ok blk = [true] ∧ ∃ a, F blk = some a ∧ out blk = enc a) ∨
      (ok blk = [false] ∧ F blk = none)) (t : ℕ) :
    ∀ bits : List Bool,
      (∀ a, (List.range t).findSome? (fun i ↦ F (block bits (i * W.length) W.length)) = some a →
        (searchStep ok out W)^[t] (pair [false] (pair bits [])) = pair [true] (pair [] (enc a))) ∧
      ((List.range t).findSome? (fun i ↦ F (block bits (i * W.length) W.length)) = none →
        (searchStep ok out W)^[t] (pair [false] (pair bits [])) =
          pair [false] (pair (bits.drop (t * W.length)) [])) := by
  induction t with
  | zero =>
    intro bits
    refine ⟨fun a h ↦ by simp at h, fun _ ↦ by simp⟩
  | succ t ih =>
    intro bits
    have hblk : block bits (0 * W.length) W.length = bits.take W.length := by simp [block]
    have hshift : ((fun i ↦ F (block bits (i * W.length) W.length)) ∘ Nat.succ) =
        fun i ↦ F (block (bits.drop W.length) (i * W.length) W.length) := by
      funext i
      simp only [Function.comp, block, List.drop_drop]
      rw [show (i + 1) * W.length = W.length + i * W.length by ring]
    rw [List.range_succ_eq_map, List.findSome?_cons, List.findSome?_map, hshift, hblk,
      Function.iterate_succ_apply, searchStep_pending]
    rcases hF (bits.take W.length) with ⟨hok, a₀, hFa, hout⟩ | ⟨hok, hFa⟩
    · rw [hok, hFa, caseBit₀_cons, Bool.cond_true, hout]
      refine ⟨fun a h ↦ ?_, fun h ↦ by simp at h⟩
      simp only [Option.some.injEq] at h
      subst h
      exact Function.iterate_fixed (searchStep_found _ _ _ _) t
    · rw [hok, hFa, caseBit₀_cons, Bool.cond_false]
      simp only []
      obtain ⟨ih1, ih2⟩ := ih (bits.drop W.length)
      refine ⟨ih1, fun h ↦ ?_⟩
      rw [ih2 h, List.drop_drop, show W.length + t * W.length = (t + 1) * W.length by ring]

theorem searchStep_iterate_length_le (ok out : List Bool → List Bool) (W bits : List Bool) (M : ℕ)
    (hout : ∀ blk : List Bool, blk.length ≤ W.length → (out blk).length ≤ M) (k : ℕ) :
    ((searchStep ok out W)^[k] (pair [false] (pair bits []))).length ≤
      2 * bits.length + M + 8 := by
  suffices h : ∀ k, ∃ f r x : List Bool,
      (searchStep ok out W)^[k] (pair [false] (pair bits [])) = pair f (pair r x) ∧
        f.length = 1 ∧ r.length ≤ bits.length ∧ x.length ≤ M by
    obtain ⟨f, r, x, h1, h2, h3, h4⟩ := h k
    rw [h1, pair_length, pair_length]
    omega
  intro k
  induction k with
  | zero => exact ⟨[false], bits, [], rfl, rfl, le_rfl, by simp⟩
  | succ k ih =>
    obtain ⟨f, r, x, h1, h2, h3, h4⟩ := ih
    rw [Function.iterate_succ_apply', h1]
    obtain ⟨b, rfl⟩ := List.length_eq_one_iff.mp h2
    cases b
    · simp only [searchStep, pairFst_pair, pairSnd_pair, caseBit₀_cons, Bool.cond_false]
      rcases caseBit₀_cases (ok (r.take W.length)) (pair [true] (pair [] (out (r.take W.length))))
        (pair [false] (pair (r.drop W.length) [])) with h | h
      · rw [h]
        exact ⟨[true], [], out (r.take W.length), rfl, rfl, by simp,
          hout _ (List.length_take_le _ _)⟩
      · rw [h]
        exact ⟨[false], r.drop W.length, [], rfl, rfl, by simp only [List.length_drop]; omega,
          by simp⟩
    · rw [searchStep_found]
      exact ⟨[true], r, x, rfl, rfl, h3, h4⟩

theorem cobham_searchStep {n : ℕ} {ok out : (Fin (n + 1) → List Bool) → List Bool}
    (hok : Cobham ok) (hout : Cobham out) {W : (Fin n → List Bool) → List Bool} (hW : Cobham W) :
    Cobham fun w : Fin (n + 1) → List Bool ↦
      searchStep (fun blk ↦ ok (Fin.cons blk (Fin.tail w))) (fun blk ↦ out (Fin.cons blk (Fin.tail w)))
        (W (Fin.tail w)) (w 0) := by
  have hst : Cobham fun w : Fin (n + 1) → List Bool ↦ w 0 := .proj 0
  have hflag := cobham_pairFst_comp hst
  have hrem := cobham_pairFst_comp (cobham_pairSnd_comp hst)
  have hW' : Cobham fun w : Fin (n + 1) → List Bool ↦ W (Fin.tail w) := cobham_tail_comp hW
  have hblk := Cobham.takeFn hW' hrem
  have hok' := cobham_consArg hok hblk
  have hout' := cobham_consArg hout hblk
  exact Cobham.iteFn hflag hst (Cobham.iteFn hok'
    (cobham_pair_comp (Cobham.const [true]) (cobham_pair_comp (Cobham.const []) hout'))
    (cobham_pair_comp (Cobham.const [false])
      (cobham_pair_comp (Cobham.dropFn hW' hrem) (Cobham.const []))))

/-- **The search loop is in the class.** `u 0` is the unary counter, `Fin.tail u` the parameters;
`ok`/`out` receive the block first, then the parameters; `M` is a ruler bounding `out` on blocks of
width at most `|W|`. -/
theorem cobham_searchLoop {n : ℕ} {ok out : (Fin (n + 1) → List Bool) → List Bool}
    (hok : Cobham ok) (hout : Cobham out) {W bits M : (Fin n → List Bool) → List Bool}
    (hW : Cobham W) (hbits : Cobham bits) (hM : Cobham M)
    (hlen : ∀ (v : Fin n → List Bool) (blk : List Bool), blk.length ≤ (W v).length →
      (out (Fin.cons blk v)).length ≤ (M v).length) :
    Cobham fun u : Fin (n + 1) → List Bool ↦
      searchLoop (fun blk ↦ ok (Fin.cons blk (Fin.tail u))) (fun blk ↦ out (Fin.cons blk (Fin.tail u)))
        (u 0) (W (Fin.tail u)) (bits (Fin.tail u)) := by
  have he : Cobham fun v : Fin n → List Bool ↦ pair [false] (pair (bits v) []) :=
    cobham_pair_comp (Cobham.const [false]) (cobham_pair_comp hbits (Cobham.const []))
  have hf := cobham_searchStep hok hout hW
  have hj : Cobham fun w : Fin (n + 1) → List Bool ↦
      (bits (Fin.tail w) ++ bits (Fin.tail w)) ++ M (Fin.tail w) ++ List.replicate 8 false :=
    cobham_tail_comp (Cobham.appendFn (Cobham.appendFn (Cobham.appendFn hbits hbits) hM)
      (Cobham.const _))
  have hiter := Cobham.iterFn he hf hj (by
    intro c v
    simp only [Fin.tail_cons, Fin.cons_zero]
    refine le_trans (searchStep_iterate_length_le _ _ _ _ (M v).length
      (fun blk hblk ↦ hlen v blk hblk) c.length) ?_
    simp only [List.length_append, List.length_replicate]
    omega)
  exact (Cobham.iteFn (cobham_pairFst_comp hiter)
    (cobham_pair_comp (Cobham.const [true]) (cobham_pairSnd_comp (cobham_pairSnd_comp hiter)))
    (Cobham.const [false])).of_eq fun u ↦ rfl

/-! ### The search for `ω` -/

/-- The candidate `a^{(p-1)/E} mod p` from a sample block. -/
def omegaCand (p E blk : List Bool) : List Bool :=
  powModStr (redStr blk p) (divStr (subBits p [true]) E) p

/-- Search for `ω` among `|t|` samples of width `|B|`: `pair [true] (encNat w)` or `[false]`. -/
def findOmegaStr (p E ℓ t B bits : List Bool) : List Bool :=
  searchLoop (fun blk ↦ orderTestStr p E ℓ (omegaCand p E blk)) (omegaCand p E) t B bits

theorem omegaCand_eq_encNat (p E blk : List Bool) (hp : decNat p ≠ 0) :
    omegaCand p E blk =
      encNat (powMod (decNat blk % decNat p) ((decNat p - 1) / decNat E) (decNat p)) := by
  rw [omegaCand, powModStr_eq_encNat _ _ _ hp, decNat_redStr _ _ hp, decNat_divStr, decNat_subBits]
  simp [decNat_cons]

theorem findOmegaStr_eq (p E : List Bool) (ℓ : List ℕ) (t B : ℕ) (bits : List Bool)
    (hp : decNat p ≠ 0) :
    findOmegaStr p E (frame (ℓ.map encNat)) (unaryN t) (unaryN B) bits =
      match findOmega (decNat p) (decNat E) ℓ t B bits with
      | some w => pair [true] (encNat w)
      | none => [false] := by
  have hF := searchStep_iterate' (fun blk ↦ orderTestStr p E (frame (ℓ.map encNat))
      (omegaCand p E blk)) (omegaCand p E) (unaryN B)
    (fun blk ↦
      let w := powMod (decNat blk % decNat p) ((decNat p - 1) / decNat E) (decNat p)
      if orderTestNat (decNat p) (decNat E) ℓ w then some w else none) encNat
    (fun blk ↦ by
      rw [orderTestStr_eq _ _ _ _ hp, omegaCand_eq_encNat _ _ _ hp, decNat_encNat]
      cases h : orderTestNat (decNat p) (decNat E) ℓ
        (powMod (decNat blk % decNat p) ((decNat p - 1) / decNat E) (decNat p))
      · exact Or.inr ⟨rfl, by simp [h]⟩
      · exact Or.inl ⟨rfl, _, by simp [h], rfl⟩) t bits
  have hB : (unaryN B).length = B := by simp [unaryN]
  have ht : (unaryN t).length = t := by simp [unaryN]
  rw [hB] at hF
  have hfo : findOmega (decNat p) (decNat E) ℓ t B bits = (List.range t).findSome? fun i ↦
      (fun blk ↦
        let w := powMod (decNat blk % decNat p) ((decNat p - 1) / decNat E) (decNat p)
        if orderTestNat (decNat p) (decNat E) ℓ w then some w else none)
        (block bits (i * B) B) := rfl
  rcases h : findOmega (decNat p) (decNat E) ℓ t B bits with _ | w
  · rw [hfo] at h
    simp only [findOmegaStr, searchLoop, ht, hF.2 h, pairFst_pair, caseBit₀_cons, Bool.cond_false]
  · rw [hfo] at h
    simp only [findOmegaStr, searchLoop, ht, hF.1 w h, pairFst_pair, pairSnd_pair, caseBit₀_cons,
      Bool.cond_true]

theorem cobham_findOmegaStr :
    Cobham fun v : Fin 6 → List Bool ↦ findOmegaStr (v 0) (v 1) (v 2) (v 3) (v 4) (v 5) := by
  -- The loop over `u = (t, p, E, ℓ, B, bits)`; `ok`/`out` see `(blk, p, E, ℓ, B, bits)`.
  have hcand : Cobham fun x : Fin 6 → List Bool ↦ omegaCand (x 1) (x 2) (x 0) :=
    cobham_powModStr_comp (cobham_redStr_comp (.proj 0) (.proj 1))
      (cobham_divStr_comp (cobham_subBits_comp (.proj 1) (Cobham.const [true])) (.proj 2)) (.proj 1)
  have hok : Cobham fun x : Fin 6 → List Bool ↦
      orderTestStr (x 1) (x 2) (x 3) (omegaCand (x 1) (x 2) (x 0)) :=
    (Cobham.comp cobham_orderTestStr (gs := fun i (x : Fin 6 → List Bool) ↦
      (![x 1, x 2, x 3, omegaCand (x 1) (x 2) (x 0)] : Fin 4 → List Bool) i) (by
        intro i
        refine Fin.cases ?_ (fun i ↦ Fin.cases ?_ (fun i ↦ Fin.cases ?_ (fun i ↦ Fin.cases ?_
          (fun i ↦ i.elim0) i) i) i) i
        · exact .proj 1
        · exact .proj 2
        · exact .proj 3
        · exact hcand)).of_eq fun x ↦ rfl
  have hloop := cobham_searchLoop (n := 5) hok hcand (W := fun v ↦ v 3) (bits := fun v ↦ v 4)
    (M := fun v ↦ false :: false :: v 0) (.proj 3) (.proj 4)
    (cobham_cons false (cobham_cons false (.proj 0))) (fun v blk _ ↦ by
      show (omegaCand (v 0) (v 1) blk).length ≤ (false :: false :: v 0).length
      simp only [List.length_cons]
      have := length_powModStr_le (redStr blk (v 0)) (divStr (subBits (v 0) [true]) (v 1)) (v 0)
      exact this)
  exact (cobham_reindex hloop ![3, 0, 1, 2, 4, 5]).of_eq fun v ↦ rfl

/-! ### The prime construction -/

/-- Success flag of one construction attempt: the output is a pair whose first component is a
well-formed block list (exactly `(decPackage y).isSome`). -/
def pkgOk (y : List Bool) : List Bool := andBit (hasBlockFlag y) (validBlocksFlag (pairFst y))

/-- The canonical re-encoding of a successful construction output. -/
def pkgOut (y : List Bool) : List Bool :=
  pair (mapBlocks canonBits (pairFst y)) (canonBits (pairSnd y))

/-- The bounded-attempt prime construction on `(unary N, unary t, unary L, bits)`:
`pair [true] (encPackage ℓ c)` on success, `[false]` otherwise. -/
def packageStr (C : PrimeConstruction) (N t L bits : List Bool) : List Bool :=
  searchLoop (fun blk ↦ pkgOk (C.build (pair N blk))) (fun blk ↦ pkgOut (C.build (pair N blk)))
    t L bits

theorem hasBlockFlag_eq_false {y : List Bool} (h : unpair? y = none) : hasBlockFlag y = [false] := by
  rcases hasBlockFlag_flag y with h' | h'
  · have := (hasBlockFlag_eq_true_iff y).mp h'
    rw [h] at this
    simp at this
  · exact h'

theorem validBlocksFlag_eq_false {a : List Bool} (h : undelimitBlocks a = none) :
    validBlocksFlag a = [false] := by
  rcases validBlocksFlag_flag a with h' | h'
  · have := (validBlocksFlag_eq_true_iff a).mp h'
    rw [h] at this
    simp at this
  · exact h'

theorem eq_frame_of_undelimitBlocks_eq_some {a : List Bool} {bs : List (List Bool)}
    (h : undelimitBlocks a = some bs) : a = frame bs := by
  have h1 : validBlocksFlag a = [true] := (validBlocksFlag_eq_true_iff a).mpr (by rw [h]; rfl)
  rw [validBlocksFlag, Cobham.eqFlag_eq_true_iff, mapBlocks, List.map_id] at h1
  rw [← h1]
  congr 1
  simp [blocks, h]

theorem decPackage_cases (y : List Bool) :
    (pkgOk y = [true] ∧ ∃ a : List ℕ × ℕ, decPackage y = some a ∧ pkgOut y = encPackage a.1 a.2) ∨
      (pkgOk y = [false] ∧ decPackage y = none) := by
  rcases hu : unpair? y with _ | ⟨a, c⟩
  · right
    refine ⟨?_, by simp [decPackage, hu]⟩
    rw [pkgOk, hasBlockFlag_eq_false hu]
    rfl
  · obtain rfl := eq_pair_of_unpair?_eq_some hu
    have hb : hasBlockFlag (pair a c) = [true] :=
      (hasBlockFlag_eq_true_iff _).mpr (by rw [unpair?_pair]; rfl)
    rcases hd : undelimitBlocks a with _ | bs
    · right
      refine ⟨?_, by simp [decPackage, unpair?_pair, hd]⟩
      rw [pkgOk, pairFst_pair, hb, validBlocksFlag_eq_false hd]
      rfl
    · left
      refine ⟨?_, (bs.map decNat, decNat c), by simp [decPackage, unpair?_pair, hd], ?_⟩
      · rw [pkgOk, pairFst_pair, hb, (validBlocksFlag_eq_true_iff a).mpr (by rw [hd]; rfl)]
        rfl
      · rw [pkgOut, pairFst_pair, pairSnd_pair, eq_frame_of_undelimitBlocks_eq_some hd,
          mapBlocks_frame, encPackage, List.map_map]
        rfl

theorem packageStr_eq (C : PrimeConstruction) (N t L : ℕ) (bits : List Bool) :
    packageStr C (unaryN N) (unaryN t) (unaryN L) bits =
      match C.firstPackage N t L bits with
      | some (ℓ, c) => pair [true] (encPackage ℓ c)
      | none => [false] := by
  have hF := searchStep_iterate' (fun blk ↦ pkgOk (C.build (pair (unaryN N) blk)))
    (fun blk ↦ pkgOut (C.build (pair (unaryN N) blk))) (unaryN L)
    (fun blk ↦ decPackage (C.build (pair (unaryN N) blk))) (fun a ↦ encPackage a.1 a.2)
    (fun blk ↦ decPackage_cases _) t bits
  have hL : (unaryN L).length = L := by simp [unaryN]
  have ht : (unaryN t).length = t := by simp [unaryN]
  rw [hL] at hF
  have hfp : C.firstPackage N t L bits = (List.range t).findSome? fun i ↦
      (fun blk ↦ decPackage (C.build (pair (unaryN N) blk))) (block bits (i * L) L) := rfl
  rcases h : C.firstPackage N t L bits with _ | ⟨ℓ, c⟩
  · rw [hfp] at h
    simp only [packageStr, searchLoop, ht, hF.2 h, pairFst_pair, caseBit₀_cons, Bool.cond_false]
  · rw [hfp] at h
    simp only [packageStr, searchLoop, ht, hF.1 (ℓ, c) h, pairFst_pair, pairSnd_pair, caseBit₀_cons,
      Bool.cond_true]

theorem length_frame_map_le (f : List Bool → List Bool) (hf : ∀ b, (f b).length ≤ b.length) :
    ∀ bs : List (List Bool), (frame (bs.map f)).length ≤ (frame bs).length
  | [] => le_rfl
  | b :: bs => by
    rw [List.map_cons, frame_cons, frame_cons, List.length_append, List.length_append,
      delimit_length, delimit_length]
    have := hf b
    have := length_frame_map_le f hf bs
    omega

theorem length_mapBlocks_le (f : List Bool → List Bool) (hf : ∀ b, (f b).length ≤ b.length)
    (s : List Bool) : (mapBlocks f s).length ≤ s.length := by
  obtain ⟨bs, rem, hs, hrem⟩ := exists_frame_append s
  by_cases hne : rem = []
  · subst hne
    rw [List.append_nil] at hs
    subst hs
    rw [mapBlocks_frame]
    exact length_frame_map_le f hf bs
  · rw [mapBlocks, hs, blocks_frame_append_of_bad bs hne (hrem.resolve_left hne)]
    simp [frame]

theorem length_pkgOut_le (y : List Bool) : (pkgOut y).length ≤ 3 * y.length + 2 := by
  rw [pkgOut, pair_length]
  have h1 := length_mapBlocks_le canonBits length_canonBits_le (pairFst y)
  have h2 := length_canonBits_le (pairSnd y)
  have h3 := length_pairFst_le y
  have h4 := pairSnd_length_le y
  omega

theorem cobham_mapBlocks_canonBits_comp {n : ℕ} {g : (Fin n → List Bool) → List Bool}
    (hg : Cobham g) : Cobham fun v : Fin n → List Bool ↦ mapBlocks canonBits (g v) := by
  have h : Cobham fun v : Fin (0 + 1) → List Bool ↦
      mapBlocks (fun b ↦ (fun w : Fin (0 + 1) → List Bool ↦ canonBits (w 0))
        (Fin.cons b (Fin.tail v))) (v 0) :=
    cobham_mapBlocks (cobham_canonBits_comp (Cobham.proj 0)) Polynomial.X
      fun v ↦ by simp [length_canonBits_le]
  exact (Cobham.comp h fun _ : Fin 1 ↦ hg).of_eq fun v ↦ rfl

theorem cobham_pkgOk_comp {n : ℕ} {g : (Fin n → List Bool) → List Bool} (hg : Cobham g) :
    Cobham fun v : Fin n → List Bool ↦ pkgOk (g v) :=
  Cobham.andFn (cobham_hasBlockFlag_comp hg) (cobham_validBlocksFlag_comp (cobham_pairFst_comp hg))

theorem cobham_pkgOut_comp {n : ℕ} {g : (Fin n → List Bool) → List Bool} (hg : Cobham g) :
    Cobham fun v : Fin n → List Bool ↦ pkgOut (g v) :=
  cobham_pair_comp (cobham_mapBlocks_canonBits_comp (cobham_pairFst_comp hg))
    (cobham_canonBits_comp (cobham_pairSnd_comp hg))

theorem cobham_packageStr (C : PrimeConstruction) :
    Cobham fun v : Fin 4 → List Bool ↦ packageStr C (v 0) (v 1) (v 2) (v 3) := by
  obtain ⟨q, hq⟩ := Cobham.output_length_poly_of_mem_FP C.build_mem_FP
  -- The loop over `u = (t, N, L, bits)`; `ok`/`out` see `(blk, N, L, bits)`.
  have hy : Cobham fun x : Fin 4 → List Bool ↦ C.build (pair (x 1) (x 0)) :=
    (Cobham.comp (FP_subset_CobhamFP C.build_mem_FP)
      fun _ : Fin 1 ↦ cobham_pair_comp (.proj 1) (.proj 0)).of_eq fun _ ↦ rfl
  have hM : Cobham fun v : Fin 3 → List Bool ↦
      Cobham.polyLen (Polynomial.C 3 * q + Polynomial.C 2) (v 0 ++ v 0 ++ v 1 ++ [false, false]) :=
    Cobham.polyLen_mem _ (Cobham.appendFn (Cobham.appendFn (Cobham.appendFn (.proj 0) (.proj 0))
      (.proj 1)) (Cobham.const _))
  have hloop := cobham_searchLoop (n := 3) (cobham_pkgOk_comp hy) (cobham_pkgOut_comp hy)
    (W := fun v ↦ v 1) (bits := fun v ↦ v 2) (.proj 1) (.proj 2) hM (fun v blk hblk ↦ by
      show (pkgOut (C.build (pair (v 0) blk))).length ≤ _
      rw [Cobham.polyLen_length]
      simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C, List.length_append,
        List.length_cons, List.length_nil]
      have h1 := length_pkgOut_le (C.build (pair (v 0) blk))
      have h2 := hq (pair (v 0) blk)
      rw [pair_length] at h2
      have h3 : q.eval (2 * (v 0).length + 2 + blk.length) ≤
          q.eval ((v 0).length + (v 0).length + (v 1).length + (0 + 1 + 1)) :=
        polynomial_eval_mono_nat q (by omega)
      omega)
  exact (cobham_reindex hloop ![1, 0, 2, 3]).of_eq fun v ↦ rfl

/-! ### Unary to binary -/

/-- Unary to binary. -/
def unaryToBinStr (u : List Bool) : List Bool := (fun s ↦ canonBits (succBits s))^[u.length] []

theorem canonBits_succBits_iterate (n : ℕ) :
    (fun s ↦ canonBits (succBits s))^[n] [] = encNat n := by
  induction n with
  | zero => simp [encNat]
  | succ n ih => rw [Function.iterate_succ_apply', ih, canonBits, decNat_succBits, decNat_encNat]

theorem unaryToBinStr_unaryN (n : ℕ) : unaryToBinStr (unaryN n) = encNat n := by
  rw [unaryToBinStr, unaryN, List.length_replicate, canonBits_succBits_iterate]

theorem cobham_unaryToBinStr : Cobham fun v : Fin 1 → List Bool ↦ unaryToBinStr (v 0) := by
  have hf : Cobham fun w : Fin 1 → List Bool ↦ canonBits (succBits (w 0)) :=
    cobham_canonBits_comp (cobham_succBits_comp (.proj 0))
  refine (Cobham.iterFn (n := 0) Cobham.empty hf (Cobham.proj 0) ?_).of_eq fun v ↦ rfl
  intro c v
  simp only [Fin.cons_zero]
  rw [canonBits_succBits_iterate, length_encNat]
  exact Nat.size_le.mpr Nat.lt_two_pow_self

/-! ### Polynomial rulers -/

/-- The polynomial-length ruler `unaryN (q.eval |s|)` (complexitylib's `polyLen` returns a string
of that length; we normalize it to all-`true`). -/
noncomputable def polyUnary (q : Polynomial ℕ) (s : List Bool) : List Bool :=
  unaryN (Cobham.polyLen q s).length

theorem polyUnary_eq (q : Polynomial ℕ) (s : List Bool) : polyUnary q s = unaryN (q.eval s.length) := by
  rw [polyUnary, Cobham.polyLen_length]

theorem cobham_polyUnary (q : Polynomial ℕ) {n : ℕ} {g : (Fin n → List Bool) → List Bool}
    (hg : Cobham g) : Cobham fun v ↦ polyUnary q (g v) :=
  (cobham_smash_comp (Cobham.polyLen_mem q hg) (Cobham.const [true])).of_eq fun v ↦ by
    simp [Complexity.smash, polyUnary, unaryN]

end SparseGcd
