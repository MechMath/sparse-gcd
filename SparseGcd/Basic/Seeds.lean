import Complexitylib.Classes.EventProb
import Complexitylib.Classes.FiniteCounting
import Complexitylib.Circuits.BitString
import Mathlib.Tactic

/-!
# Seed calculus

Probability bookkeeping for random seeds split into consecutive blocks. Everything is finite:
`eventProb E = |E| / 2^T` (complexitylib). The two *slice* lemmas are the engine of the layered
error accounting of the paper's Theorem 18/Lemma 26 proof: an event on `a + b` bits whose
conditional probability given any prefix is `≤ q` has probability `≤ q`, and one whose conditional
probability given a prefix in `G` is `≥ q` has probability `≥ q · Pr[G]`.
-/

open Complexity Finset

namespace SparseGcd

/-- Prefix projection is restriction along the canonical inclusion. -/
theorem blockFst_apply (a b : ℕ) (w : BitString (a + b)) (i : Fin a) :
    blockFst a b w i = w (Fin.castAdd b i) := rfl

theorem blockAppend_castAdd (a b : ℕ) (u : BitString a) (v : BitString b) (i : Fin a) :
    blockAppend a b u v (Fin.castAdd b i) = u i := by
  have h := congrFun (blockFst_append a b u v) i
  rwa [blockFst_apply] at h

theorem blockAppend_natAdd (a b : ℕ) (u : BitString a) (v : BitString b) (i : Fin b) :
    blockAppend a b u v (Fin.natAdd a i) = v i := by
  have h := congrFun (blockSnd_append a b u v) i
  rwa [blockSnd_apply] at h

/-- The fiber of `E` over a prefix `u` is in bijection with the slice of `E` at `u`. -/
private theorem card_fiber_blockFst {a b : ℕ} (E : Finset (BitString (a + b))) (u : BitString a) :
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

private theorem card_eq_sum_slices {a b : ℕ} (E : Finset (BitString (a + b))) :
    E.card = ∑ u : BitString a, (univ.filter fun v : BitString b ↦ blockAppend a b u v ∈ E).card := by
  rw [Finset.card_eq_sum_card_fiberwise (f := blockFst a b) (t := univ)
    (fun _ _ ↦ mem_univ _)]
  exact Finset.sum_congr rfl fun u _ ↦ card_fiber_blockFst E u

/-- Upper slice bound. -/
theorem eventProb_le_of_slices {a b : ℕ} (E : Finset (BitString (a + b))) (q : ℚ)
    (h : ∀ u : BitString a,
      eventProb (univ.filter fun v : BitString b ↦ blockAppend a b u v ∈ E) ≤ q) :
    eventProb E ≤ q := by
  have hpos : (0 : ℚ) < 2 ^ b := by positivity
  have hcard : ∀ u : BitString a,
      ((univ.filter fun v : BitString b ↦ blockAppend a b u v ∈ E).card : ℚ) ≤ q * 2 ^ b := by
    intro u
    have hu := h u
    unfold eventProb at hu
    rwa [div_le_iff₀ hpos] at hu
  unfold eventProb
  rw [div_le_iff₀ (by positivity), card_eq_sum_slices E]
  push_cast
  calc ∑ u : BitString a, ((univ.filter fun v : BitString b ↦ blockAppend a b u v ∈ E).card : ℚ)
      ≤ ∑ _u : BitString a, q * 2 ^ b := Finset.sum_le_sum fun u _ ↦ hcard u
    _ = q * 2 ^ (a + b) := by
      rw [Finset.sum_const, card_univ, card_finArrowBool, pow_add]
      ring

/-- Lower slice bound. -/
theorem eventProb_ge_of_slices {a b : ℕ} (E : Finset (BitString (a + b))) (G : Finset (BitString a))
    (q : ℚ) (h : ∀ u ∈ G, q ≤ eventProb (univ.filter fun v : BitString b ↦ blockAppend a b u v ∈ E)) :
    q * eventProb G ≤ eventProb E := by
  have hpos : (0 : ℚ) < 2 ^ b := by positivity
  have hcard : ∀ u ∈ G,
      q * 2 ^ b ≤ ((univ.filter fun v : BitString b ↦ blockAppend a b u v ∈ E).card : ℚ) := by
    intro u hu
    have hu' := h u hu
    unfold eventProb at hu'
    rwa [le_div_iff₀ hpos] at hu'
  unfold eventProb
  rw [le_div_iff₀ (by positivity), card_eq_sum_slices E]
  have hrw : q * (G.card / 2 ^ a) * 2 ^ (a + b) = ∑ _u ∈ G, q * 2 ^ b := by
    rw [Finset.sum_const, nsmul_eq_mul, pow_add]
    field_simp
  rw [hrw]
  push_cast
  calc ∑ _u ∈ G, q * 2 ^ b
      ≤ ∑ u ∈ G, ((univ.filter fun v : BitString b ↦ blockAppend a b u v ∈ E).card : ℚ) :=
        Finset.sum_le_sum hcard
    _ ≤ ∑ u : BitString a, ((univ.filter fun v : BitString b ↦ blockAppend a b u v ∈ E).card : ℚ) :=
        Finset.sum_le_sum_of_subset_of_nonneg (subset_univ G) fun _ _ _ ↦ by positivity

/-- An event depending only on the prefix. -/
theorem eventProb_filter_blockFst {a b : ℕ} (G : Finset (BitString a)) :
    eventProb (univ.filter fun w : BitString (a + b) ↦ blockFst a b w ∈ G) = eventProb G := by
  have h := eventProb_block (fun u : BitString a ↦ u ∈ G) (fun _ : BitString b ↦ True)
  simpa [Finset.filter_univ_mem] using h

/-- An event depending only on the suffix. -/
theorem eventProb_filter_blockSnd {a b : ℕ} (G : Finset (BitString b)) :
    eventProb (univ.filter fun w : BitString (a + b) ↦ blockSnd a b w ∈ G) = eventProb G := by
  have h := eventProb_block (fun _ : BitString a ↦ True) (fun v : BitString b ↦ v ∈ G)
  simpa [Finset.filter_univ_mem] using h

theorem eventProb_filter_not {T : ℕ} (P : BitString T → Prop) [DecidablePred P] :
    eventProb (univ.filter fun w ↦ ¬ P w) = 1 - eventProb (univ.filter P) := by
  rw [← eventProb_compl, Finset.compl_filter]

/-- Independence over `k` blocks: all blocks avoid `E` with probability `(1 - Pr E)^k`. -/
theorem eventProb_blockEventCount_eq_zero (k T : ℕ) (E : Finset (BitString T)) :
    eventProb (univ.filter fun w : BitString (k * T) ↦ blockEventCount E w = 0) =
      (1 - eventProb E) ^ k := by
  unfold eventProb
  rw [card_blockEventCount_eq, Nat.choose_zero_right, pow_zero, Nat.sub_zero, one_mul, one_mul,
    Nat.cast_pow, Nat.cast_sub (card_le_pow E), Nat.cast_pow, Nat.cast_ofNat,
    one_sub_div (by positivity), div_pow, ← pow_mul, mul_comm T k]

/-- Exact probability that some block lies in `E`. -/
theorem eventProb_blockEventCount_pos_eq (k T : ℕ) (E : Finset (BitString T)) :
    eventProb (univ.filter fun w : BitString (k * T) ↦ 0 < blockEventCount E w) =
      1 - (1 - eventProb E) ^ k := by
  rw [← eventProb_blockEventCount_eq_zero, ← eventProb_filter_not]
  congr 1
  exact Finset.filter_congr fun w _ ↦ Nat.pos_iff_ne_zero

/-- Union bound over `k` blocks: some block lies in `E`. -/
theorem eventProb_blockEventCount_pos_le (k T : ℕ) (E : Finset (BitString T)) :
    eventProb (univ.filter fun w : BitString (k * T) ↦ 0 < blockEventCount E w) ≤
      k * eventProb E := by
  rw [eventProb_blockEventCount_pos_eq]
  have hp1 := eventProb_le_one E
  have hp0 := eventProb_nonneg E
  have hb : 1 - k * eventProb E ≤ (1 - eventProb E) ^ k := by
    have := one_add_mul_le_pow (a := -eventProb E) (by linarith) k
    simpa [sub_eq_add_neg] using this
  linarith

theorem eventProb_blockEventCount_pos_ge (k T : ℕ) (E : Finset (BitString T)) :
    1 - (1 - eventProb E) ^ k ≤
      eventProb (univ.filter fun w : BitString (k * T) ↦ 0 < blockEventCount E w) :=
  (eventProb_blockEventCount_pos_eq k T E).ge

/-! ### Lists of bits -/

theorem ofFn_blockAppend {a b : ℕ} (u : BitString a) (v : BitString b) :
    List.ofFn (blockAppend a b u v) = List.ofFn u ++ List.ofFn v := by
  rw [List.ofFn_add]
  congr 1
  · exact congrArg List.ofFn (funext fun i ↦ blockAppend_castAdd a b u v i)
  · exact congrArg List.ofFn (funext fun i ↦ blockAppend_natAdd a b u v i)

theorem ofFn_blockFst {a b : ℕ} (w : BitString (a + b)) :
    List.ofFn (blockFst a b w) = (List.ofFn w).take a := by
  rw [List.ofFn_add, List.take_left' (by simp)]
  rfl

theorem ofFn_blockSnd {a b : ℕ} (w : BitString (a + b)) :
    List.ofFn (blockSnd a b w) = (List.ofFn w).drop a := by
  rw [List.ofFn_add, List.drop_left' (by simp)]
  rfl

/-- The `i`-th block of a `k * T`-bit seed as a list. -/
theorem ofFn_blocksEquiv {k T : ℕ} (w : BitString (k * T)) (i : Fin k) :
    List.ofFn (blocksEquiv k T w i) = ((List.ofFn w).drop (i.val * T)).take T := by
  have hle : (i.val + 1) * T ≤ k * T := Nat.mul_le_mul_right T i.isLt
  rw [Nat.succ_mul] at hle
  apply List.ext_getElem
  · simp
    omega
  · intro j h1 h2
    simp only [List.getElem_ofFn, List.getElem_take, List.getElem_drop, blocksEquiv_apply]
    congr 1
    ext
    simp only [finProdFinEquiv_apply_val]
    ring

/-- Event monotonicity under an implication of list-level predicates. -/
theorem eventProb_filter_mono {T : ℕ} {P Q : BitString T → Prop} [DecidablePred P] [DecidablePred Q]
    (h : ∀ w, P w → Q w) : eventProb (univ.filter P) ≤ eventProb (univ.filter Q) := by
  apply eventProb_mono
  intro w hw
  simp only [mem_filter, mem_univ, true_and] at hw ⊢
  exact h w hw

/-- Probability of a conjunction is at most the probability of either conjunct. -/
theorem eventProb_filter_and_le_left {T : ℕ} (P Q : BitString T → Prop) [DecidablePred P]
    [DecidablePred Q] :
    eventProb (univ.filter fun w ↦ P w ∧ Q w) ≤ eventProb (univ.filter P) :=
  eventProb_filter_mono fun _ h ↦ h.1

/-- `Pr[P] ≤ Pr[Q] + Pr[P ∧ ¬Q]`. -/
theorem eventProb_filter_le_add {T : ℕ} (P Q : BitString T → Prop) [DecidablePred P]
    [DecidablePred Q] :
    eventProb (univ.filter P) ≤ eventProb (univ.filter Q) +
      eventProb (univ.filter fun w ↦ P w ∧ ¬ Q w) := by
  refine le_trans (eventProb_mono ?_) (eventProb_union_le _ _)
  intro w hw
  simp only [mem_filter, mem_univ, true_and, mem_union] at hw ⊢
  by_cases hq : Q w
  · exact Or.inl hq
  · exact Or.inr ⟨hw, hq⟩

/-- `Pr[P ∧ Q] ≥ Pr[P] - Pr[¬Q]`. -/
theorem eventProb_filter_and_ge {T : ℕ} (P Q : BitString T → Prop) [DecidablePred P]
    [DecidablePred Q] :
    eventProb (univ.filter P) - eventProb (univ.filter fun w ↦ ¬ Q w) ≤
      eventProb (univ.filter fun w ↦ P w ∧ Q w) := by
  have h1 := eventProb_filter_le_add P (fun w ↦ P w ∧ Q w)
  have h2 : eventProb (univ.filter fun w ↦ P w ∧ ¬ (P w ∧ Q w)) ≤
      eventProb (univ.filter fun w ↦ ¬ Q w) :=
    eventProb_filter_mono fun _ hw hq ↦ hw.2 ⟨hw.1, hq⟩
  linarith

end SparseGcd
