import SparseGcd.Machine.StageLemmas
import SparseGcd.Machine.ArithStr
import Complexitylib.Classes.P.Cobham.Internal.Simulate
import Complexitylib.Models.TuringMachine.OutputBounds

/-!
# The clocked output-sensitive gcd solver (Theorem 18, oracle side)

A `GcdSolver` is only guaranteed to halt on well-formed instances, within
`time(T + bitLength Δ + bitLength p)` steps where `T` includes the size of the *answer*. The
reduction knows that on the successful compression event the answer has at most two terms, so it
clocks the machine with `T' = max(|f|, |g|, 2)`: `Cobham.simFn` simulates the machine for as many
steps as the clock string is long and returns whatever is on the output tape. On promised inputs
this is exactly the machine's output (`simFn_eq_of_outputsWithin`); off promise the simulation still
halts in polynomial time and its output is simply not trusted. The positive-degree test reads the
returned term list and looks for a nonzero exponent.
-/

open Complexity SparseDiv SparseDiv.StringArith Polynomial

namespace SparseGcd

/-- Per-input version of complexitylib's `Cobham.simFn_eq`. -/
theorem simFn_eq_of_outputsWithin {k : ℕ} (tm : TM k) {x y : List Bool} {t : ℕ}
    (h : OutputsWithin tm x y t) (u : List Bool)
    (hlen : t + x.length + Fintype.card tm.Q + 2 ≤ u.length) : Cobham.simFn tm u x = y := by
  have hu1 : 1 ≤ u.length := by omega
  have hR : Cobham.clockRuler u = Cobham.blockRuler (u.length - 1) := Cobham.clockRuler_eq hu1
  have htail : u.tail.length = u.length - 1 := List.length_tail
  have hq : Fintype.card tm.Q ≤ Cobham.blockWidth (u.length - 1) := by
    rw [Cobham.blockWidth]; omega
  obtain ⟨c', s, hs, hreach, hhalt, hout⟩ := h
  have hylen : y.length ≤ s := TM.output_length_le_of_reachesIn hreach hout
  have hrunW : TM.runCfg tm (tm.initCfg x) (u.length - 1) = c' := by
    rw [show u.length - 1 = s + (u.length - 1 - s) from by omega, TM.runCfg_add,
      TM.runCfg_of_reachesIn tm hreach, TM.runCfg_of_halted tm hhalt]
  have hrun : Cobham.runFn tm u x = Cobham.cfgCode (u.length - 1) c' := by
    rw [Cobham.runFn, hR, htail, Cobham.initFn_eq tm _ x (by omega),
      Cobham.iterate_stepFn tm _ x hq _ le_rfl, hrunW]
  obtain ⟨hinv, hWh⟩ := Cobham.cfgTapes_runCfg_inv tm x (u.length - 1) (u.length - 1) le_rfl
  rw [hrunW] at hinv hWh
  have hmem : c'.output ∈ Cobham.cfgTapes c' := by simp [Cobham.cfgTapes]
  have hstart : c'.output.StartInvariant := hinv _ hmem
  have hhead : c'.output.head ≤ u.length - 1 := hWh _ hmem
  obtain ⟨hb3, hb4⟩ :=
    Cobham.blockAt_cfgCode_tape (u.length - 1) c' 1 (by rw [Cobham.cfgTapes_length]; omega)
  have hidx : (Cobham.cfgTapes c')[1]'(by rw [Cobham.cfgTapes_length]; omega) = c'.output := rfl
  rw [hidx, show 2 * 1 + 1 = 3 from rfl] at hb3
  rw [hidx, show 2 * 1 + 2 = 4 from rfl] at hb4
  have hpair : blockAt (Cobham.clockRuler u) (Cobham.runFn tm u x) 3
      ++ blockAt (Cobham.clockRuler u) (Cobham.runFn tm u x) 4 =
        Cobham.pairCode (u.length - 1) c'.output := by
    rw [hrun, hR, hb3, hb4, Cobham.pairCode]
  have hrew : Cobham.outPairFn tm u x
      = Cobham.pairCode (u.length - 1) { head := 0, cells := c'.output.cells } := by
    rw [Cobham.outPairFn, hpair, hR, Cobham.iterate_rewindFn c'.output hstart hhead u.length,
      Cobham.rewound c'.output (by omega)]
  have hdropeq : (Cobham.outPairFn tm u x).drop (Cobham.clockRuler u).length
      = Cobham.cellsCode c'.output 0 (u.length - 1 + 1) := by
    rw [hrew, hR, Cobham.drop_pairCode_rewound]
  rw [Cobham.simFn, htail, hdropeq]
  exact Cobham.output_of_cellsCode c'.output y hout (by omega)

/-- A unary parameter string of length `≥ gcdParam p f g` whenever the answer has `≤ 2` terms.
The instance string itself is long enough: `max(|f|,|g|,2) ≤ |f| + |g| + 2`, every listed
term costs six bits plus its exponent numeral (which bounds the degree's bit length), and `p`'s
numeral is a component of the instance — so the unary string of the instance's own length is
used (`gcdParam_le_length_paramStr`). -/
def paramStr (z : List Bool) : List Bool := List.replicate z.length true

@[simp] theorem length_paramStr (z : List Bool) : (paramStr z).length = z.length :=
  List.length_replicate

/-- `Nat.size` of a maximum is at most the sum of the sizes. -/
private theorem size_max_le (a b : ℕ) : Nat.size (max a b) ≤ Nat.size a + Nat.size b := by
  rcases le_total a b with hab | hab
  · rw [max_eq_right hab]; exact Nat.le_add_left _ _
  · rw [max_eq_left hab]; exact Nat.le_add_right _ _

/-- The bit length of the degree is at most the total bit length of the listed exponents. -/
private theorem size_natDegree_toPoly_le (p : ℕ) (l : Terms) :
    Nat.size (toPoly p l).natDegree ≤ (l.map fun t ↦ Nat.size t.2).sum := by
  refine (Nat.size_le_size (natDegree_toPoly_le p l)).trans ?_
  induction l with
  | nil => simp
  | cons t l ih =>
    rw [List.map_cons, List.foldr_cons, List.map_cons, List.sum_cons]
    exact (size_max_le _ _).trans (Nat.add_le_add_left ih _)

/-- Every listed term costs six bits plus its exponent numeral. -/
private theorem sum_size_exp_le_length_encTerms (l : Terms) :
    (l.map fun t ↦ Nat.size t.2).sum + 6 * l.length ≤ (encTerms l).length := by
  induction l with
  | nil => simp
  | cons t l ih =>
    rw [encTerms_cons, List.length_append, delimit_length, length_encTerm, List.map_cons,
      List.sum_cons, List.length_cons]
    omega

theorem gcdParam_le_length_paramStr {p : ℕ} {f g : Terms} (h : WFGcd p f g)
    (h2 : haveI : Fact p.Prime := ⟨h.1⟩; (gcdTerms p f g).length ≤ 2) :
    haveI : Fact p.Prime := ⟨h.1⟩
    gcdParam p f g ≤ (paramStr (encDivInstance p f g)).length := by
  have : Fact p.Prime := ⟨h.1⟩
  rw [length_paramStr, length_encDivInstance, gcdParam]
  have hm : max (max f.length g.length) (gcdTerms p f g).length ≤ f.length + g.length + 2 :=
    max_le (max_le (by omega) (by omega)) (by omega)
  have hd := size_max_le (toPoly p f).natDegree (toPoly p g).natDegree
  have hf := size_natDegree_toPoly_le p f
  have hg := size_natDegree_toPoly_le p g
  have hf' := sum_size_exp_le_length_encTerms f
  have hg' := sum_size_exp_le_length_encTerms g
  omega

theorem cobham_paramStr : Cobham fun v : Fin 1 → List Bool ↦ paramStr (v 0) :=
  (cobham_polyUnary Polynomial.X (Cobham.proj (0 : Fin 1))).of_eq fun v ↦ by
    simp only [polyUnary, Cobham.polyLen_length, Polynomial.eval_X, unaryN, paramStr]

/-- The clock string. -/
noncomputable def clockStr (S : GcdSolver) (z : List Bool) : List Bool :=
  polyUnary S.time (paramStr z) ++ z ++ unaryN (Fintype.card S.tm.Q + 2)

/-- The clocked solver. -/
noncomputable def clockedSolver (S : GcdSolver) (z : List Bool) : List Bool :=
  Cobham.simFn S.tm (clockStr S z) z

/-- Polynomials with natural coefficients are monotone on `ℕ`. -/
theorem eval_le_eval_of_le (q : Polynomial ℕ) {a b : ℕ} (h : a ≤ b) : q.eval a ≤ q.eval b := by
  rw [Polynomial.eval_eq_sum_range, Polynomial.eval_eq_sum_range]
  exact Finset.sum_le_sum fun i _ ↦ Nat.mul_le_mul_left _ (Nat.pow_le_pow_left h i)

theorem clockedSolver_eq (S : GcdSolver) {p : ℕ} {f g : Terms} (h : WFGcd p f g)
    (h2 : haveI : Fact p.Prime := ⟨h.1⟩; (gcdTerms p f g).length ≤ 2) :
    haveI : Fact p.Prime := ⟨h.1⟩
    clockedSolver S (encDivInstance p f g) = encTerms (gcdTerms p f g) := by
  have : Fact p.Prime := ⟨h.1⟩
  unfold clockedSolver
  refine simFn_eq_of_outputsWithin S.tm (S.correct p f g h) _ ?_
  have h3 := eval_le_eval_of_le S.time (gcdParam_le_length_paramStr h h2)
  simp only [clockStr, List.length_append, polyUnary, unaryN, List.length_replicate,
    Cobham.polyLen_length]
  omega

theorem clockedSolver_mem_FP (S : GcdSolver) : clockedSolver S ∈ FP := by
  refine CobhamFP_subset_FP ?_
  have hu : Cobham fun v : Fin 1 → List Bool ↦ clockStr S (v 0) :=
    Cobham.appendFn (Cobham.appendFn (cobham_polyUnary S.time cobham_paramStr) (Cobham.proj 0))
      (Cobham.const _)
  exact (Cobham.simFn_mem S.tm hu).of_eq fun v ↦ rfl

/-- One step of the positive-degree fold: `acc ∨ (the block's exponent is nonzero)`. -/
def degStep (acc b : List Bool) : List Bool := orBit acc (notBit (isZeroBits (expOf b)))

/-- Positive-degree test on an encoded term list: some block has a nonzero exponent. -/
def degTestStr (y : List Bool) : List Bool := foldBlocks degStep [false] y

/-- An encoded term list is the framing of the encoded terms. -/
theorem encTerms_eq_frame (l : Terms) : encTerms l = frame (l.map encTerm) := by
  rw [encTerms, frame, List.map_map]; rfl

private theorem isZeroBits_encNat (e : ℕ) : isZeroBits (encNat e) = [decide (e = 0)] := by
  rcases isZeroBits_flag (encNat e) with h | h
  · have := (isZeroBits_eq_true_iff _).1 h
    rw [decNat_encNat] at this
    rw [h, this]; simp
  · have hne : ¬ e = 0 := fun h0 ↦ by
      have := (isZeroBits_eq_true_iff (encNat e)).2 (by rw [decNat_encNat]; exact h0)
      rw [h] at this
      simp at this
    simp [h, hne]

private theorem degStep_encTerm (a : Bool) (t : ℕ × ℕ) :
    degStep [a] (encTerm t) = [a || decide (0 < t.2)] := by
  rw [degStep, expOf, encTerm, pairSnd_pair, isZeroBits_encNat, notBit_single, orBit_single]
  rcases Nat.eq_zero_or_pos t.2 with h0 | h0
  · simp [h0]
  · simp [h0, h0.ne']

theorem degTestStr_encTerms (l : Terms) : degTestStr (encTerms l) = [decide (∃ t ∈ l, 0 < t.2)] := by
  rw [degTestStr, encTerms_eq_frame, foldBlocks_frame]
  suffices ∀ a : Bool, (l.map encTerm).foldl degStep [a] = [a || decide (∃ t ∈ l, 0 < t.2)] by
    simpa using this false
  induction l with
  | nil => intro a; simp
  | cons t l ih =>
    intro a
    rw [List.map_cons, List.foldl_cons, degStep_encTerm, ih]
    simp only [List.mem_cons, exists_eq_or_imp, Bool.decide_or, Bool.or_assoc]

theorem cobham_degTestStr : Cobham fun v : Fin 1 → List Bool ↦ degTestStr (v 0) := by
  have hstep : Cobham fun w : Fin 2 → List Bool ↦
      orBit (w 0) (notBit (isZeroBits (pairSnd (w 1)))) :=
    Cobham.orFn (Cobham.proj 0)
      (Cobham.notFn (cobham_isZeroBits_comp (cobham_pairSnd_comp (Cobham.proj 1))))
  exact (cobham_foldBlocks (n := 0) hstep (init := fun _ ↦ [false]) (Cobham.const _) 1
    fun w ↦ by rw [Cobham.orBit_length]; omega).of_eq fun v ↦ rfl

theorem degTestStr_mem_FP : degTestStr ∈ FP := CobhamFP_subset_FP cobham_degTestStr

/-- **The degree oracle of Theorem 18** (deterministic; seed and count ignored). -/
noncomputable def gcdOracle (S : GcdSolver) : DegreeOracle where
  inst := encDivInstance
  instStr := id
  O := fun z ↦ degTestStr (clockedSolver S (pairFst (pairSnd z)))
  σ := 0
  O_mem_FP := by
    refine CobhamFP_subset_FP ?_
    have h1 : Cobham fun v : Fin 1 → List Bool ↦ degTestStr (v 0) :=
      FP_subset_CobhamFP degTestStr_mem_FP
    have h2 : Cobham fun v : Fin 1 → List Bool ↦ clockedSolver S (v 0) :=
      FP_subset_CobhamFP (clockedSolver_mem_FP S)
    have h3 : Cobham fun v : Fin 1 → List Bool ↦ pairFst (pairSnd (v 0)) :=
      cobham_pairFst_comp (cobham_pairSnd_comp (Cobham.proj 0))
    have h4 : Cobham fun v : Fin 1 → List Bool ↦ clockedSolver S (pairFst (pairSnd (v 0))) :=
      (Cobham.comp h2 fun _ : Fin 1 ↦ h3).of_eq fun _ ↦ rfl
    exact (Cobham.comp h1 fun _ : Fin 1 ↦ h4).of_eq fun _ ↦ rfl
  instStr_mem_FP := id_mem_FP
  instStr_eq := fun _ _ _ ↦ rfl
  inst_length_le := fun _ _ _ ↦ by omega
  O_prefix := fun _ _ _ ↦ by simp only [pairFst_pair, pairSnd_pair]
  correct := by
    intro c d ψ us hψ _ hcard hZ
    set H := normalize d.p (RootData.Hterms d.p us (d.constraintTerms ψ)) with hH
    have hN : Normalized d.p H := normalized_normalize d.hp.pos _
    have hwf : WFGcd d.p (rawRterms d.p d.E) H := wfGcd_instance d H hN
    have hlen : (gcdTerms d.p (rawRterms d.p d.E) H).length ≤ 2 :=
      length_gcdTerms_le_two d hψ hcard hN (by rw [hH, toPoly_normalize]; exact hZ)
    have hout : clockedSolver S (encDivInstance d.p (rawRterms d.p d.E) H) =
        encTerms (gcdTerms d.p (rawRterms d.p d.E) H) := clockedSolver_eq S hwf hlen
    rw [Finset.filter_eq_self.2 ?_, eventProb_univ]
    · exact sub_le_self _ (by positivity)
    · intro r _
      simp only [pairFst_pair, pairSnd_pair]
      rw [hout, degTestStr_encTerms, ← exists_pos_exponent_gcdTerms_iff d H]
      simp

end SparseGcd
