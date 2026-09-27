import SparseGcd.Machine.SamplingProb

/-!
# Splitting a trial seed into its six segments

`trialData` reads its seed through six disjoint windows

```
[ k bits | hash bits | package attempts | ω attempts | coefficients | oracle seed ]
   KB s      HB s        tp * Lp s          ta*Bb s      Tmax*Bb s      σOr s
```

(the first two windows are only used through their prefixes of length `kBits m₀`, `hashBits m₀`).
This file makes that factorisation available to the probability analysis:

* §1 **probability plumbing** on top of `Basic/Seeds.lean`: the exact "average of the conditional
  probabilities" formula `eventProb_eq_sum_slices`, the conditional upper bound
  `eventProb_le_of_good_prefix`, the fact that an event reading only a prefix (resp. two disjoint
  prefixes) of the seed has the probability of the corresponding shorter event
  (`eventProb_filter_take_eq`, `eventProb_filter_two_prefix`), the decomposition
  `ofFn_eq_append_blocks` of a seed into prefix and suffix, and list-level *splitting* lemmas
  (`eventProb_filter_le_of_split`, `eventProb_filter_ge_of_split`,
  `eventProb_filter_le_of_good_split`) which are the ones the analysis actually applies;
* §2 `block` on a concatenation;
* §3 `trialOf`, the segment-wise form of `trialData`, the identity `trialData_eq_trialOf`,
  the accepting set `trialAccept` and the two ready-made splittings
  `eventProb_trialAccept_le_of_stages` / `eventProb_trialAccept_ge_of_prefix`;
* §4 structural facts shared by the two bound proofs: the `RootData` of a successful
  package + ω stage (`stageData`), the transported oracle guarantee
  (`eventProb_oracle_correct`) and the isolation bound on the padded segment 1-2
  (`eventProb_isolateSeed_unique_padded`).
-/

open Complexity SAT SparseDiv Polynomial Finset

namespace SparseGcd

/-! ## §1 Probability plumbing -/

private theorem card_fiber_blockFst' {a b : ℕ} (E : Finset (BitString (a + b))) (u : BitString a) :
    (E.filter fun w ↦ blockFst a b w = u).card =
      (univ.filter fun v : BitString b ↦ blockAppend a b u v ∈ E).card := by
  apply Finset.card_bij' (fun w _ ↦ blockSnd a b w) (fun v _ ↦ blockAppend a b u v)
  · intro w hw
    simp only [mem_filter, mem_univ, true_and] at hw ⊢
    rw [← hw.2, blockAppend_fst_snd]
    exact hw.1
  · intro v hv
    simp only [mem_filter, mem_univ, true_and] at hv ⊢
    exact ⟨hv, blockFst_append a b u v⟩
  · intro w hw
    simp only [mem_filter] at hw
    rw [← hw.2]
    exact blockAppend_fst_snd a b w
  · intro v _
    exact blockSnd_append a b u v

private theorem card_eq_sum_slices' {a b : ℕ} (E : Finset (BitString (a + b))) :
    E.card = ∑ u : BitString a, (univ.filter fun v : BitString b ↦ blockAppend a b u v ∈ E).card := by
  rw [Finset.card_eq_sum_card_fiberwise (f := blockFst a b) (t := univ) (fun _ _ ↦ mem_univ _)]
  exact Finset.sum_congr rfl fun u _ ↦ card_fiber_blockFst' E u

/-- **The probability of an event is the average of its conditional probabilities.** -/
theorem eventProb_eq_sum_slices {a b : ℕ} (E : Finset (BitString (a + b))) :
    eventProb E =
      (∑ u : BitString a,
        eventProb (univ.filter fun v : BitString b ↦ blockAppend a b u v ∈ E)) / 2 ^ a := by
  unfold eventProb
  rw [card_eq_sum_slices' E, ← Finset.sum_div, div_div, ← pow_add, add_comm b a]
  push_cast
  rfl

/-- Conditional upper bound: `Pr[E] ≤ Pr[Gᶜ] + max_{u ∈ G} Pr[E | u]`. -/
theorem eventProb_le_of_good_prefix {a b : ℕ} (E : Finset (BitString (a + b)))
    (G : Finset (BitString a)) (q₁ q₂ : ℚ) (h₀ : 0 ≤ q₂) (h₁ : eventProb Gᶜ ≤ q₁)
    (h₂ : ∀ u ∈ G, eventProb (univ.filter fun v : BitString b ↦ blockAppend a b u v ∈ E) ≤ q₂) :
    eventProb E ≤ q₁ + q₂ := by
  classical
  have hsub : E ⊆ (univ.filter fun w : BitString (a + b) ↦ blockFst a b w ∈ Gᶜ) ∪
      (univ.filter fun w : BitString (a + b) ↦ blockFst a b w ∈ G ∧ w ∈ E) := by
    intro w hw
    rw [mem_union, mem_filter, mem_filter]
    by_cases hg : blockFst a b w ∈ G
    · exact Or.inr ⟨mem_univ _, hg, hw⟩
    · exact Or.inl ⟨mem_univ _, by simpa using hg⟩
  refine le_trans (eventProb_mono hsub) (le_trans (eventProb_union_le _ _) (add_le_add ?_ ?_))
  · rw [eventProb_filter_blockFst]
    exact h₁
  · refine eventProb_le_of_slices _ q₂ fun u ↦ ?_
    by_cases hu : u ∈ G
    · refine le_trans (eventProb_mono ?_) (h₂ u hu)
      intro v hv
      simp only [mem_filter, mem_univ, true_and] at hv ⊢
      exact hv.2
    · have : (univ.filter fun v : BitString b ↦
          blockAppend a b u v ∈ univ.filter fun w : BitString (a + b) ↦
            blockFst a b w ∈ G ∧ w ∈ E) = ∅ := by
        rw [Finset.filter_eq_empty_iff]
        intro v _
        simp only [mem_filter, mem_univ, true_and, blockFst_append]
        exact fun h ↦ hu h.1
      rw [this]
      simpa [eventProb] using h₀
  
/-- An event that reads only the first `a` bits of an `T`-bit seed has the probability of the
corresponding event on `a` bits. -/
theorem eventProb_filter_take_eq {T a : ℕ} (hT : a ≤ T) (Q : List Bool → Prop) [DecidablePred Q]
    (hQ : ∀ l : List Bool, Q (l.take a) ↔ Q l) :
    eventProb (univ.filter fun w : BitString T ↦ Q (List.ofFn w)) =
      eventProb (univ.filter fun u : BitString a ↦ Q (List.ofFn u)) := by
  classical
  obtain ⟨b, rfl⟩ : ∃ b, T = a + b := ⟨T - a, by omega⟩
  rw [← eventProb_filter_blockFst (b := b) (univ.filter fun u : BitString a ↦ Q (List.ofFn u))]
  congr 1
  refine Finset.filter_congr fun w _ ↦ ?_
  simp only [mem_filter, mem_univ, true_and, ofFn_blockFst]
  rw [hQ]

private theorem sum_comp_blockFst {k a : ℕ} (f : BitString k → ℚ) :
    ∑ u : BitString (k + a), f (blockFst k a u) = 2 ^ a * ∑ u : BitString k, f u := by
  classical
  rw [← Equiv.sum_comp (blockEquiv k a).symm (fun u ↦ f (blockFst k a u))]
  have hb : ∀ p : BitString k × BitString a, (blockEquiv k a).symm p = blockAppend k a p.1 p.2 := by
    intro p
    rw [blockAppend]
  calc ∑ p : BitString k × BitString a, f (blockFst k a ((blockEquiv k a).symm p))
      = ∑ p : BitString k × BitString a, f p.1 := by
        refine Finset.sum_congr rfl fun p _ ↦ ?_
        rw [hb p, blockFst_append]
    _ = ∑ u : BitString k, ∑ _x : BitString a, f u := Fintype.sum_prod_type _
    _ = 2 ^ a * ∑ u : BitString k, f u := by
        simp only [Finset.sum_const, card_univ, card_finArrowBool, nsmul_eq_mul]
        rw [Finset.mul_sum]
        push_cast
        rfl

/-- **Two disjoint prefix windows.** An event on a `K + H`-bit seed that reads only the first `k`
bits and the `h` bits starting at `K` has the probability of the corresponding `k + h`-bit event. -/
theorem eventProb_filter_two_prefix {K H k h : ℕ} (hk : k ≤ K) (hh : h ≤ H)
    (R : List Bool → List Bool → Prop) [∀ x y, Decidable (R x y)] :
    eventProb (univ.filter fun w : BitString (K + H) ↦
        R ((List.ofFn w).take k) (((List.ofFn w).drop K).take h)) =
      eventProb (univ.filter fun w : BitString (k + h) ↦
        R ((List.ofFn w).take k) ((List.ofFn w).drop k)) := by
  classical
  obtain ⟨a, rfl⟩ : ∃ a, K = k + a := ⟨K - k, by omega⟩
  obtain ⟨b, rfl⟩ : ∃ b, H = h + b := ⟨H - h, by omega⟩
  set f : BitString k → ℚ := fun u ↦
    eventProb (univ.filter fun v : BitString h ↦ R (List.ofFn u) (List.ofFn v)) with hf
  have hbig : eventProb (univ.filter fun w : BitString ((k + a) + (h + b)) ↦
      R ((List.ofFn w).take k) (((List.ofFn w).drop (k + a)).take h)) =
      (∑ u : BitString (k + a), f (blockFst k a u)) / 2 ^ (k + a) := by
    rw [eventProb_eq_sum_slices]
    congr 1
    refine Finset.sum_congr rfl fun u _ ↦ ?_
    have hslice : (univ.filter fun v : BitString (h + b) ↦
        blockAppend (k + a) (h + b) u v ∈ univ.filter fun w : BitString ((k + a) + (h + b)) ↦
          R ((List.ofFn w).take k) (((List.ofFn w).drop (k + a)).take h)) =
        univ.filter fun v : BitString (h + b) ↦
          blockFst h b v ∈ univ.filter fun v' : BitString h ↦
            R (List.ofFn (blockFst k a u)) (List.ofFn v') := by
      refine Finset.filter_congr fun v _ ↦ ?_
      simp only [mem_filter, mem_univ, true_and, ofFn_blockAppend]
      rw [List.take_append_of_le_length (by simp), List.drop_left' (by simp),
        ← ofFn_blockFst, ← ofFn_blockFst]
    rw [hslice, eventProb_filter_blockFst, hf]
  have hsmall : eventProb (univ.filter fun w : BitString (k + h) ↦
      R ((List.ofFn w).take k) ((List.ofFn w).drop k)) = (∑ u : BitString k, f u) / 2 ^ k := by
    rw [eventProb_eq_sum_slices]
    congr 1
    refine Finset.sum_congr rfl fun u _ ↦ ?_
    congr 1
    refine Finset.filter_congr fun v _ ↦ ?_
    simp only [mem_filter, mem_univ, true_and, ofFn_blockAppend]
    rw [List.take_left' (by simp), List.drop_left' (by simp)]
  rw [hbig, hsmall, sum_comp_blockFst, pow_add]
  have h2a : ((2:ℚ) ^ a) ≠ 0 := by positivity
  have h2k : ((2:ℚ) ^ k) ≠ 0 := by positivity
  field_simp

/-- A seed as the concatenation of its prefix and its suffix. -/
theorem ofFn_eq_append_blocks {a b : ℕ} (w : BitString (a + b)) :
    List.ofFn w = List.ofFn (blockFst a b w) ++ List.ofFn (blockSnd a b w) := by
  rw [← ofFn_blockAppend, blockAppend_fst_snd]

/-! ### List-level splitting -/

/-- Upper bound by conditioning on the first `a` bits, at the level of lists. -/
theorem eventProb_filter_le_of_split {n a b : ℕ} (hn : n = a + b) (P : List Bool → Prop)
    [DecidablePred P] (q : ℚ)
    (hP : ∀ u : List Bool, u.length = a →
      eventProb (univ.filter fun v : BitString b ↦ P (u ++ List.ofFn v)) ≤ q) :
    eventProb (univ.filter fun w : BitString n ↦ P (List.ofFn w)) ≤ q := by
  classical
  subst hn
  refine eventProb_le_of_slices _ q fun u ↦ ?_
  refine le_trans (le_of_eq ?_) (hP (List.ofFn u) (by simp))
  congr 1
  refine Finset.filter_congr fun v _ ↦ ?_
  simp only [mem_filter, mem_univ, true_and, ofFn_blockAppend]

/-- Lower bound by conditioning on a good set of prefixes, at the level of lists. -/
theorem eventProb_filter_ge_of_split {n a b : ℕ} (hn : n = a + b) (P : List Bool → Prop)
    [DecidablePred P] (G : Finset (BitString a)) (q : ℚ)
    (hP : ∀ u ∈ G, q ≤ eventProb (univ.filter fun v : BitString b ↦ P (List.ofFn u ++ List.ofFn v))) :
    q * eventProb G ≤ eventProb (univ.filter fun w : BitString n ↦ P (List.ofFn w)) := by
  classical
  subst hn
  refine eventProb_ge_of_slices _ G q fun u hu ↦ ?_
  refine le_trans (hP u hu) (le_of_eq ?_)
  congr 1
  refine Finset.filter_congr fun v _ ↦ ?_
  simp only [mem_filter, mem_univ, true_and, ofFn_blockAppend]

/-- Conditional upper bound at the level of lists: `Pr[P] ≤ Pr[Gᶜ] + max_{u ∈ G} Pr[P | u]`. -/
theorem eventProb_filter_le_of_good_split {n a b : ℕ} (hn : n = a + b) (P : List Bool → Prop)
    [DecidablePred P] (G : Finset (BitString a)) (q₁ q₂ : ℚ) (h₀ : 0 ≤ q₂)
    (h₁ : eventProb Gᶜ ≤ q₁)
    (h₂ : ∀ u ∈ G,
      eventProb (univ.filter fun v : BitString b ↦ P (List.ofFn u ++ List.ofFn v)) ≤ q₂) :
    eventProb (univ.filter fun w : BitString n ↦ P (List.ofFn w)) ≤ q₁ + q₂ := by
  classical
  subst hn
  refine eventProb_le_of_good_prefix _ G q₁ q₂ h₀ h₁ fun u hu ↦ ?_
  refine le_trans (le_of_eq ?_) (h₂ u hu)
  congr 1
  refine Finset.filter_congr fun v _ ↦ ?_
  simp only [mem_filter, mem_univ, true_and, ofFn_blockAppend]

/-! ## §2 `block` on a concatenation -/

/-- A window contained in the first summand. -/
theorem block_append_left (l₁ l₂ : List Bool) {len : ℕ} (h : len ≤ l₁.length) :
    block (l₁ ++ l₂) 0 len = l₁.take len := by
  simp only [block, List.drop_zero]
  exact List.take_append_of_le_length h

/-- A window starting exactly at the end of the first summand. -/
theorem block_append_right (l₁ l₂ : List Bool) {off : ℕ} (hoff : off = l₁.length) (len : ℕ) :
    block (l₁ ++ l₂) off len = l₂.take len := by
  simp only [block, List.drop_left' hoff.symm]

/-- A window starting at the end of `l₁` and contained in `l₂`. -/
theorem block_append_mid (l₁ l₂ l₃ : List Bool) {off len : ℕ} (hoff : off = l₁.length)
    (hlen : len ≤ l₂.length) : block (l₁ ++ (l₂ ++ l₃)) off len = l₂.take len := by
  rw [block_append_right _ _ hoff, List.take_append_of_le_length hlen]

/-- A window inside a prefix of the seed. -/
theorem block_take (l : List Bool) {off len n : ℕ} (h : off + len ≤ n) :
    block (l.take n) off len = block l off len := by
  simp only [block, List.drop_take, List.take_take]
  congr 1
  omega

namespace DegreeOracle

variable (Or : DegreeOracle) (C : PrimeConstruction)

/-! ## §3 The six segments of a trial -/

/-- **One trial, as a function of its six seed segments.** Identical to `trialData` except that
each `block` read is replaced by the corresponding segment; segments 1 and 2 are used only through
their prefixes of length `kBits m₀`, `hashBits m₀` and segment 6 only through its prefix of length
`σOr s`. -/
def trialOf (s : ℕ) (φ : CNF) (a₁ a₂ a₃ a₄ a₅ a₆ : List Bool) : Bool :=
  let m₀ := φ.maxVar + 1
  let ψn := isolateSeed φ (a₁.take (kBits m₀)) (a₂.take (hashBits m₀))
  match C.firstPackage (Nn s) tp (C.Lp s) a₃ with
  | none => false
  | some (ℓ, c) =>
    let p := 1 + c * ℓ.prod
    let ℓm := ℓ.take ψn.2
    let E := ℓm.prod
    match findOmega p E ℓm (ta s) (C.Bb s) a₄ with
    | none => false
    | some w =>
      let H := buildH p E ℓm w ψn.2 ψn.1 (C.Bb s) a₅
      decide (Or.O (pair (unaryN (cnt s)) (pair (Or.inst p (rawRterms p E) H)
        (a₆.take (Or.σOr C s)))) = [true])

/-- **The seed of a trial factors through its six segments.** -/
theorem trialData_eq_trialOf {s : ℕ} {φ : CNF} (hs : (CNF.encode φ).length = s)
    (a₁ a₂ a₃ a₄ a₅ a₆ : List Bool) (h₁ : a₁.length = KB s) (h₂ : a₂.length = HB s)
    (h₃ : a₃.length = tp * C.Lp s) (h₄ : a₄.length = ta s * C.Bb s)
    (h₅ : a₅.length = Tmax s * C.Bb s) :
    Or.trialData C s φ (a₁ ++ a₂ ++ a₃ ++ a₄ ++ a₅ ++ a₆) = Or.trialOf C s φ a₁ a₂ a₃ a₄ a₅ a₆ := by
  have hk := kBits_le_KB hs
  have hh := hashBits_le_HB hs
  have s1 : a₁ ++ a₂ ++ a₃ ++ a₄ ++ a₅ ++ a₆ = a₁ ++ (a₂ ++ a₃ ++ a₄ ++ a₅ ++ a₆) := by
    simp only [List.append_assoc]
  have s2 : a₁ ++ a₂ ++ a₃ ++ a₄ ++ a₅ ++ a₆ = a₁ ++ (a₂ ++ (a₃ ++ a₄ ++ a₅ ++ a₆)) := by
    simp only [List.append_assoc]
  have s3 : a₁ ++ a₂ ++ a₃ ++ a₄ ++ a₅ ++ a₆ = (a₁ ++ a₂) ++ (a₃ ++ (a₄ ++ a₅ ++ a₆)) := by
    simp only [List.append_assoc]
  have s4 : a₁ ++ a₂ ++ a₃ ++ a₄ ++ a₅ ++ a₆ = (a₁ ++ a₂ ++ a₃) ++ (a₄ ++ (a₅ ++ a₆)) := by
    simp only [List.append_assoc]
  have s5 : a₁ ++ a₂ ++ a₃ ++ a₄ ++ a₅ ++ a₆ = (a₁ ++ a₂ ++ a₃ ++ a₄) ++ (a₅ ++ a₆) := by
    simp only [List.append_assoc]
  have e1 : block (a₁ ++ a₂ ++ a₃ ++ a₄ ++ a₅ ++ a₆) 0 (kBits (φ.maxVar + 1)) =
      a₁.take (kBits (φ.maxVar + 1)) := by
    rw [s1]
    exact block_append_left a₁ (a₂ ++ a₃ ++ a₄ ++ a₅ ++ a₆) (by omega)
  have e2 : block (a₁ ++ a₂ ++ a₃ ++ a₄ ++ a₅ ++ a₆) (KB s) (hashBits (φ.maxVar + 1)) =
      a₂.take (hashBits (φ.maxVar + 1)) := by
    rw [s2]
    exact block_append_mid a₁ a₂ (a₃ ++ a₄ ++ a₅ ++ a₆) h₁.symm (by omega)
  have e3 : block (a₁ ++ a₂ ++ a₃ ++ a₄ ++ a₅ ++ a₆) (C.o2 s) (tp * C.Lp s) = a₃ := by
    rw [s3, block_append_mid (a₁ ++ a₂) a₃ (a₄ ++ a₅ ++ a₆)
      (by simp [PrimeConstruction.o2, h₁, h₂]) (by omega),
      List.take_of_length_le (by omega)]
  have e4 : block (a₁ ++ a₂ ++ a₃ ++ a₄ ++ a₅ ++ a₆) (C.o3 s) (ta s * C.Bb s) = a₄ := by
    rw [s4, block_append_mid (a₁ ++ a₂ ++ a₃) a₄ (a₅ ++ a₆)
      (by simp [PrimeConstruction.o3, PrimeConstruction.o2, h₁, h₂, h₃]; omega) (by omega),
      List.take_of_length_le (by omega)]
  have e5 : block (a₁ ++ a₂ ++ a₃ ++ a₄ ++ a₅ ++ a₆) (C.o4 s) (Tmax s * C.Bb s) = a₅ := by
    rw [s5, block_append_mid (a₁ ++ a₂ ++ a₃ ++ a₄) a₅ a₆
      (by simp [PrimeConstruction.o4, PrimeConstruction.o3, PrimeConstruction.o2,
        h₁, h₂, h₃, h₄]; omega) (by omega),
      List.take_of_length_le (by omega)]
  have e6 : block (a₁ ++ a₂ ++ a₃ ++ a₄ ++ a₅ ++ a₆) (C.o5 s) (Or.σOr C s) =
      a₆.take (Or.σOr C s) := by
    rw [block_append_right (a₁ ++ a₂ ++ a₃ ++ a₄ ++ a₅) a₆
      (by simp [PrimeConstruction.o5, PrimeConstruction.o4, PrimeConstruction.o3,
        PrimeConstruction.o2, h₁, h₂, h₃, h₄, h₅]; omega)]
  simp only [trialData, trialOf, e1, e2, e3, e4, e5, e6]
  rfl

/-- Right-associated variant of `trialData_eq_trialOf`; this is the shape produced by iterating
`eventProb_filter_le_of_split`. -/
theorem trialData_eq_trialOf' {s : ℕ} {φ : CNF} (hs : (CNF.encode φ).length = s)
    (a₁ a₂ a₃ a₄ a₅ a₆ : List Bool) (h₁ : a₁.length = KB s) (h₂ : a₂.length = HB s)
    (h₃ : a₃.length = tp * C.Lp s) (h₄ : a₄.length = ta s * C.Bb s)
    (h₅ : a₅.length = Tmax s * C.Bb s) :
    Or.trialData C s φ (a₁ ++ (a₂ ++ (a₃ ++ (a₄ ++ (a₅ ++ a₆))))) =
      Or.trialOf C s φ a₁ a₂ a₃ a₄ a₅ a₆ := by
  rw [← trialData_eq_trialOf Or C hs a₁ a₂ a₃ a₄ a₅ a₆ h₁ h₂ h₃ h₄ h₅]
  congr 1
  simp only [List.append_assoc]

/-- `trialData` on an arbitrary seed, written through its six windows. -/
theorem trialData_eq_trialOf_block {s : ℕ} {φ : CNF} (hs : (CNF.encode φ).length = s)
    (l : List Bool) :
    Or.trialData C s φ l = Or.trialOf C s φ (block l 0 (KB s)) (block l (KB s) (HB s))
      (block l (C.o2 s) (tp * C.Lp s)) (block l (C.o3 s) (ta s * C.Bb s))
      (block l (C.o4 s) (Tmax s * C.Bb s)) (block l (C.o5 s) (Or.σOr C s)) := by
  have hk := kBits_le_KB hs
  have hh := hashBits_le_HB hs
  have e1 : (block l 0 (KB s)).take (kBits (φ.maxVar + 1)) = block l 0 (kBits (φ.maxVar + 1)) := by
    simp only [block, List.drop_zero, List.take_take]
    congr 1
    omega
  have e2 : (block l (KB s) (HB s)).take (hashBits (φ.maxVar + 1)) =
      block l (KB s) (hashBits (φ.maxVar + 1)) := by
    simp only [block, List.take_take]
    congr 1
    omega
  have e6 : (block l (C.o5 s) (Or.σOr C s)).take (Or.σOr C s) = block l (C.o5 s) (Or.σOr C s) := by
    simp only [block, List.take_take, Nat.min_self]
  simp only [trialData, trialOf, e1, e2, e6]
  rfl

/-- The accepting seeds of one trial. -/
def trialAccept (Or : DegreeOracle) (C : PrimeConstruction) (s : ℕ) (φ : CNF) :
    Finset (BitString (Or.L C s)) :=
  univ.filter fun w ↦ Or.trialData C s φ (List.ofFn w) = true

/-- The length of a trial seed, split into its six segments. -/
theorem L_eq_segments (s : ℕ) : Or.L C s =
    KB s + (HB s + (tp * C.Lp s + (ta s * C.Bb s + (Tmax s * C.Bb s + Or.σOr C s)))) := by
  simp only [DegreeOracle.L, PrimeConstruction.o5, PrimeConstruction.o4, PrimeConstruction.o3,
    PrimeConstruction.o2]
  ring

/-- **Upper bound by stages.** It suffices to bound, uniformly in the first four segments, the
probability over the last two (coefficients and oracle seed). -/
theorem eventProb_trialAccept_le_of_stages {s : ℕ} {φ : CNF} (hs : (CNF.encode φ).length = s)
    (q : ℚ)
    (h : ∀ a₁ a₂ a₃ a₄ : List Bool, a₁.length = KB s → a₂.length = HB s →
        a₃.length = tp * C.Lp s → a₄.length = ta s * C.Bb s →
      eventProb (univ.filter fun v : BitString (Tmax s * C.Bb s + Or.σOr C s) ↦
        Or.trialOf C s φ a₁ a₂ a₃ a₄
          (List.ofFn (blockFst (Tmax s * C.Bb s) (Or.σOr C s) v))
          (List.ofFn (blockSnd (Tmax s * C.Bb s) (Or.σOr C s) v)) = true) ≤ q) :
    eventProb (Or.trialAccept C s φ) ≤ q := by
  unfold trialAccept
  refine eventProb_filter_le_of_split (L_eq_segments Or C s)
    (fun l ↦ Or.trialData C s φ l = true) q ?_
  intro a₁ h₁
  refine eventProb_filter_le_of_split rfl (fun l ↦ Or.trialData C s φ (a₁ ++ l) = true) q ?_
  intro a₂ h₂
  refine eventProb_filter_le_of_split rfl
    (fun l ↦ Or.trialData C s φ (a₁ ++ (a₂ ++ l)) = true) q ?_
  intro a₃ h₃
  refine eventProb_filter_le_of_split rfl
    (fun l ↦ Or.trialData C s φ (a₁ ++ (a₂ ++ (a₃ ++ l))) = true) q ?_
  intro a₄ h₄
  refine le_trans (le_of_eq ?_) (h a₁ a₂ a₃ a₄ h₁ h₂ h₃ h₄)
  congr 1
  refine Finset.filter_congr fun v _ ↦ ?_
  have hv : List.ofFn v = List.ofFn (blockFst (Tmax s * C.Bb s) (Or.σOr C s) v) ++
      List.ofFn (blockSnd (Tmax s * C.Bb s) (Or.σOr C s) v) := by
    rw [← ofFn_blockAppend, blockAppend_fst_snd]
  simp only [hv]
  rw [trialData_eq_trialOf' Or C hs a₁ a₂ a₃ a₄ _ _ h₁ h₂ h₃ h₄ (by simp)]

/-- **Lower bound by conditioning on segments 1-2.** -/
theorem eventProb_trialAccept_ge_of_prefix {s : ℕ} {φ : CNF} {b : ℕ}
    (hb : Or.L C s = KB s + HB s + b) (G : Finset (BitString (KB s + HB s))) (q : ℚ)
    (h : ∀ u ∈ G, q ≤ eventProb (univ.filter fun v : BitString b ↦
      Or.trialData C s φ (List.ofFn u ++ List.ofFn v) = true)) :
    q * eventProb G ≤ eventProb (Or.trialAccept C s φ) :=
  eventProb_filter_ge_of_split hb (fun l ↦ Or.trialData C s φ l = true) G q h

/-- The segment decomposition used by `eventProb_trialAccept_ge_of_prefix`. -/
theorem L_eq_prefix_segments (s : ℕ) : Or.L C s =
    KB s + HB s + (tp * C.Lp s + (ta s * C.Bb s + (Tmax s * C.Bb s + Or.σOr C s))) := by
  simp only [DegreeOracle.L, PrimeConstruction.o5, PrimeConstruction.o4, PrimeConstruction.o3,
    PrimeConstruction.o2]
  ring

end DegreeOracle

/-! ## §4 Structural facts shared by the two bound proofs -/

/-- A residue returned by `findOmega` is a residue. -/
theorem findOmega_lt_of_validPackage {N : ℕ} {ℓ : List ℕ} {c : ℕ} (hv : ValidPackage N ℓ c)
    {m t B : ℕ} {bits : List Bool} {w : ℕ}
    (h : findOmega (1 + c * ℓ.prod) (ℓ.take m).prod (ℓ.take m) t B bits = some w) :
    w < 1 + c * ℓ.prod :=
  (findOmega_some h hv.2.2.2.2.pos).1

/-- A residue returned by `findOmega` has exact order `E`. -/
theorem orderOf_findOmega {N : ℕ} {ℓ : List ℕ} {c : ℕ} (hv : ValidPackage N ℓ c)
    {m t B : ℕ} {bits : List Bool} {w : ℕ}
    (h : findOmega (1 + c * ℓ.prod) (ℓ.take m).prod (ℓ.take m) t B bits = some w) :
    orderOf ((w : ZMod (1 + c * ℓ.prod))) = (ℓ.take m).prod :=
  orderOf_of_orderTestNat hv m (findOmega_some h hv.2.2.2.2.pos).2

/-- **The `RootData` of a trial whose package and ω stages both succeeded.** -/
def stageData {N : ℕ} {ℓ : List ℕ} {c : ℕ} (hv : ValidPackage N ℓ c) (m : ℕ) {t B : ℕ}
    {bits : List Bool} {w : ℕ}
    (h : findOmega (1 + c * ℓ.prod) (ℓ.take m).prod (ℓ.take m) t B bits = some w) : RootData :=
  rootDataOf hv m (findOmega_lt_of_validPackage hv h) (orderOf_findOmega hv h)

@[simp] theorem stageData_p {N ℓ c} (hv : ValidPackage N ℓ c) (m) {t B bits w}
    (h : findOmega (1 + c * ℓ.prod) (ℓ.take m).prod (ℓ.take m) t B bits = some w) :
    (stageData hv m h).p = 1 + c * ℓ.prod := rfl

@[simp] theorem stageData_ℓ {N ℓ c} (hv : ValidPackage N ℓ c) (m) {t B bits w}
    (h : findOmega (1 + c * ℓ.prod) (ℓ.take m).prod (ℓ.take m) t B bits = some w) :
    (stageData hv m h).ℓ = ℓ.take m := rfl

@[simp] theorem stageData_E {N ℓ c} (hv : ValidPackage N ℓ c) (m) {t B bits w}
    (h : findOmega (1 + c * ℓ.prod) (ℓ.take m).prod (ℓ.take m) t B bits = some w) :
    (stageData hv m h).E = (ℓ.take m).prod := rfl

@[simp] theorem stageData_w {N ℓ c} (hv : ValidPackage N ℓ c) (m) {t B bits w}
    (h : findOmega (1 + c * ℓ.prod) (ℓ.take m).prod (ℓ.take m) t B bits = some w) :
    (stageData hv m h).w = w := rfl

theorem stageData_m {N ℓ c} (hv : ValidPackage N ℓ c) (m) (hm : m ≤ N) {t B bits w}
    (h : findOmega (1 + c * ℓ.prod) (ℓ.take m).prod (ℓ.take m) t B bits = some w) :
    (stageData hv m h).m = m :=
  rootDataOf_m hv m hm _ _

namespace DegreeOracle

variable (Or : DegreeOracle) (C : PrimeConstruction)

/-- **The oracle guarantee, transported to the reserved oracle segment.** The oracle only reads
the first `σ(cnt s + |z|)` bits of its randomness (`O_prefix`) and `|z| ≤ Zmax s`
(`length_inst_le`), so the reserved block of `σOr s = σ(cnt s + Zmax s)` bits carries the same
error bound. -/
theorem eventProb_oracle_correct {s : ℕ} (d : RootData) {ψ : CNF} (B : ℕ) (a₅ : List Bool)
    (hp : Nat.size d.p ≤ C.bitBound.eval (Nn s)) (hm : d.m ≤ Vmax s)
    (hψv : CNF.VarsLt ψ d.m) (hψb : BoundedClauses ψ) (hk : ψ.length ≤ Kmax s)
    (hcard : (solutions ψ d.m).card ≤ 1)
    (hZ : d.commonZeros [toPoly d.p (buildH d.p d.E d.ℓ d.w d.m ψ B a₅)] =
      d.commonZeros (d.constraintPolys ψ)) :
    1 - 1 / (2 : ℚ) ^ cnt s ≤ eventProb (univ.filter fun v : BitString (Or.σOr C s) ↦
      (Or.O (pair (unaryN (cnt s)) (pair (Or.inst d.p (rawRterms d.p d.E)
          (buildH d.p d.E d.ℓ d.w d.m ψ B a₅)) (List.ofFn v))) = [true] ↔
        0 < (monicGcd d.R (toPoly d.p (buildH d.p d.E d.ℓ d.w d.m ψ B a₅))).natDegree)) := by
  classical
  set us : List ℕ := coeffs d.p B (d.m + ψ.length) a₅ with hus
  have hHeq : buildH d.p d.E d.ℓ d.w d.m ψ B a₅ =
      normalize d.p (RootData.Hterms d.p us (d.constraintTerms ψ)) := buildH_eq d ψ B a₅
  have hZ' : d.commonZeros [toPoly d.p (RootData.Hterms d.p us (d.constraintTerms ψ))] =
      d.commonZeros (d.constraintPolys ψ) := by
    rw [← toPoly_buildH d ψ B a₅]
    exact hZ
  have hcor := Or.correct (cnt s) d ψ us hψv hψb hcard hZ'
  rw [← hHeq] at hcor
  set z : List Bool := Or.inst d.p (rawRterms d.p d.E) (buildH d.p d.E d.ℓ d.w d.m ψ B a₅) with hz
  set a : ℕ := Or.σ.eval (cnt s + z.length) with ha
  have hlen : z.length ≤ C.Zmax s := length_inst_le Or C d hp hm hψb hk B a₅
  have hle : a ≤ Or.σOr C s :=
    Complexity.polynomial_eval_mono_nat Or.σ (Nat.add_le_add_left hlen _)
  refine hcor.trans (le_of_eq ?_)
  refine (eventProb_filter_take_eq (T := Or.σOr C s) (a := a) hle
    (fun l ↦ (Or.O (pair (unaryN (cnt s)) (pair z l)) = [true] ↔
      0 < (monicGcd d.R (toPoly d.p (buildH d.p d.E d.ℓ d.w d.m ψ B a₅))).natDegree)) ?_).symm
  intro l
  rw [← Or.O_prefix (cnt s) z l]

/-! ### The isolation stage on the padded segments 1-2 -/

open scoped Classical in
/-- **Lemma 13/21 on the padded seed.** Segment 1 is `KB s ≥ kBits m₀` bits long and segment 2 is
`HB s ≥ hashBits m₀` bits long; only their prefixes are read, so the isolation succeeds with
probability at least `1/A(s)`. -/
theorem eventProb_isolateSeed_unique_padded {s : ℕ} {φ : CNF} (hs : (CNF.encode φ).length = s)
    (hφ : φ.Satisfiable) :
    (1 : ℚ) / A s ≤ eventProb (univ.filter fun w : BitString (KB s + HB s) ↦
      UniqueSat (isolateSeed φ ((List.ofFn w).take (kBits (φ.maxVar + 1)))
          (((List.ofFn w).drop (KB s)).take (hashBits (φ.maxVar + 1)))).1
        (isolateSeed φ ((List.ofFn w).take (kBits (φ.maxVar + 1)))
          (((List.ofFn w).drop (KB s)).take (hashBits (φ.maxVar + 1)))).2) := by
  classical
  have hk := kBits_le_KB hs
  have hh := hashBits_le_HB hs
  rw [eventProb_filter_two_prefix hk hh
    (fun x y ↦ UniqueSat (isolateSeed φ x y).1 (isolateSeed φ x y).2)]
  have hbase := eventProb_isolateSeed_unique_ge φ hφ
  simp only at hbase
  have heq : (univ.filter fun w : BitString (kBits (φ.maxVar + 1) + hashBits (φ.maxVar + 1)) ↦
      UniqueSat (isolateSeed φ ((List.ofFn w).take (kBits (φ.maxVar + 1)))
          ((List.ofFn w).drop (kBits (φ.maxVar + 1)))).1
        (isolateSeed φ ((List.ofFn w).take (kBits (φ.maxVar + 1)))
          ((List.ofFn w).drop (kBits (φ.maxVar + 1)))).2) =
      (univ.filter fun w : BitString (kBits (φ.maxVar + 1) + hashBits (φ.maxVar + 1)) ↦
        UniqueSat (isolateSeed φ (List.ofFn (blockFst _ _ w)) (List.ofFn (blockSnd _ _ w))).1
          (isolateSeed φ (List.ofFn (blockFst _ _ w)) (List.ofFn (blockSnd _ _ w))).2) := by
    refine Finset.filter_congr fun w _ ↦ ?_
    rw [ofFn_blockFst, ofFn_blockSnd]
  rw [heq]
  refine le_trans (one_div_le_one_div_of_le (by positivity) ?_) hbase
  have hm : φ.maxVar + 1 ≤ s + 1 := maxVar_succ_le hs
  have hm' : (φ.maxVar : ℚ) + 1 ≤ (s : ℚ) + 1 := by exact_mod_cast hm
  unfold A
  push_cast
  linarith

end DegreeOracle

end SparseGcd
