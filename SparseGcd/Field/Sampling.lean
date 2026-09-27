import SparseGcd.Basic.Seeds
import SparseGcd.Basic.Bernoulli
import SparseDivComplexity.Encoding

/-!
# Sampling residues from fair bits

A uniform `n`-bit string read as an LSB-first numeral `a < 2^n` and reduced modulo `p` is
*nearly* uniform on `{0, …, p-1}`: every residue has probability within `2^{-n}` of `1/p`.
This replaces the paper's "sample `u ∈ 𝔽_p` uniformly": the bias is carried explicitly through
every probability bound (with `2^n ≥ 2p` the bias is at most `1/(2p)`).
-/

open Complexity Finset

namespace SparseGcd

/-- The numeral of a bit vector (LSB first), as in `SparseDiv.decNat`. -/
def bitsVal {n : ℕ} (v : BitString n) : ℕ := SparseDiv.decNat (List.ofFn v)

theorem bitsVal_lt {n : ℕ} (v : BitString n) : bitsVal v < 2 ^ n := by
  simpa [bitsVal] using SparseDiv.decNat_lt_two_pow_length (List.ofFn v)

theorem bitsVal_injective {n : ℕ} : Function.Injective (bitsVal (n := n)) := by
  intro v w h
  exact List.ofFn_injective (Nat.fromBitsLE_inj_of_length_eq (by simp) h)

/-- `bitsVal` is a bijection `BitString n ≃ Fin (2^n)`. -/
theorem bitsVal_bijective (n : ℕ) :
    Function.Bijective (fun v : BitString n ↦ (⟨bitsVal v, bitsVal_lt v⟩ : Fin (2 ^ n))) := by
  rw [Fintype.bijective_iff_injective_and_card]
  refine ⟨fun v w h ↦ bitsVal_injective (by simpa using h), ?_⟩
  simp

theorem exists_bitsVal_eq {n x : ℕ} (hx : x < 2 ^ n) : ∃ v : BitString n, bitsVal v = x := by
  obtain ⟨v, hv⟩ := (bitsVal_bijective n).2 ⟨x, hx⟩
  exact ⟨v, by simpa using congrArg Fin.val hv⟩

/-- Every numeral below `2^n` is hit by exactly one bit vector. -/
theorem card_bitsVal_eq {n x : ℕ} (hx : x < 2 ^ n) :
    (univ.filter fun v : BitString n ↦ bitsVal v = x).card = 1 := by
  obtain ⟨v, rfl⟩ := exists_bitsVal_eq hx
  rw [card_eq_one]
  refine ⟨v, ?_⟩
  ext w
  simp only [mem_filter, mem_univ, true_and, mem_singleton]
  exact ⟨fun h ↦ bitsVal_injective h, fun h ↦ h ▸ rfl⟩

theorem card_bitsVal_eq_of_ge {n x : ℕ} (hx : 2 ^ n ≤ x) :
    (univ.filter fun v : BitString n ↦ bitsVal v = x).card = 0 := by
  rw [card_eq_zero, filter_eq_empty_iff]
  intro v _ h
  exact absurd (h ▸ bitsVal_lt v) (not_lt.mpr hx)

/-- Counting bit vectors by a property of their numeral is counting numerals below `2^n`. -/
theorem card_filter_bitsVal (n : ℕ) (P : ℕ → Prop) [DecidablePred P] :
    (univ.filter fun v : BitString n ↦ P (bitsVal v)).card = ((range (2 ^ n)).filter P).card := by
  refine card_bij (fun v _ ↦ bitsVal v) ?_ ?_ ?_
  · intro v hv
    simp only [mem_filter, mem_univ, true_and, mem_range] at hv ⊢
    exact ⟨bitsVal_lt v, hv⟩
  · intro v _ w _ h
    exact bitsVal_injective h
  · intro x hx
    simp only [mem_filter, mem_range] at hx
    obtain ⟨v, rfl⟩ := exists_bitsVal_eq hx.1
    exact ⟨v, by simpa using hx.2, rfl⟩

/-- At most `N / p + 1` numerals below `N` have residue `r` modulo `p`. -/
theorem card_range_filter_mod_le (N p r : ℕ) :
    ((range N).filter fun x ↦ x % p = r).card ≤ N / p + 1 := by
  calc ((range N).filter fun x ↦ x % p = r).card ≤ (range (N / p + 1)).card := by
        refine card_le_card_of_injOn (· / p) ?_ ?_
        · intro x hx
          simp only [mem_coe, mem_filter, mem_range] at hx ⊢
          exact Nat.lt_succ_of_le (Nat.div_le_div_right hx.1.le)
        · intro x hx y hy hxy
          simp only [mem_coe, mem_filter, mem_range] at hx hy
          simp only at hxy
          calc x = p * (x / p) + x % p := (Nat.div_add_mod x p).symm
            _ = p * (y / p) + y % p := by rw [hxy, hx.2, hy.2]
            _ = y := Nat.div_add_mod y p
    _ = N / p + 1 := card_range _

/-- At least `N / p` numerals below `N` have residue `r < p` modulo `p`. -/
theorem card_range_filter_mod_ge (N p r : ℕ) (hr : r < p) :
    N / p ≤ ((range N).filter fun x ↦ x % p = r).card := by
  calc N / p = (range (N / p)).card := (card_range _).symm
    _ ≤ ((range N).filter fun x ↦ x % p = r).card := by
        refine card_le_card_of_injOn (fun j ↦ j * p + r) ?_ ?_
        · intro j hj
          simp only [mem_coe, mem_filter, mem_range] at hj ⊢
          refine ⟨?_, ?_⟩
          · have h1 : (j + 1) * p ≤ N / p * p := Nat.mul_le_mul_right p hj
            have h2 : N / p * p ≤ N := Nat.div_mul_le_self N p
            rw [add_mul, one_mul] at h1
            omega
          · rw [Nat.mul_add_mod', Nat.mod_eq_of_lt hr]
        · intro j _ k _ hjk
          simp only at hjk
          exact Nat.eq_of_mul_eq_mul_right (by omega) (Nat.add_right_cancel hjk)

/-- Number of `n`-bit numerals with residue `r` modulo `p`: between `2^n/p - 1` and `2^n/p + 1`. -/
theorem card_bitsVal_mod_mul_le (n p r : ℕ) (_hp : 0 < p) :
    (univ.filter fun v : BitString n ↦ bitsVal v % p = r).card * p ≤ 2 ^ n + p := by
  rw [card_filter_bitsVal n (fun x ↦ x % p = r)]
  have h1 := card_range_filter_mod_le (2 ^ n) p r
  have h2 : 2 ^ n / p * p ≤ 2 ^ n := Nat.div_mul_le_self _ p
  calc _ ≤ (2 ^ n / p + 1) * p := Nat.mul_le_mul_right p h1
    _ = 2 ^ n / p * p + p := by ring
    _ ≤ 2 ^ n + p := by omega

theorem two_pow_le_card_bitsVal_mod_mul_add (n p r : ℕ) (hr : r < p) :
    2 ^ n ≤ (univ.filter fun v : BitString n ↦ bitsVal v % p = r).card * p + p := by
  rw [card_filter_bitsVal n (fun x ↦ x % p = r)]
  have h1 := card_range_filter_mod_ge (2 ^ n) p r hr
  have h2 : 2 ^ n < p * (2 ^ n / p + 1) := Nat.lt_mul_div_succ _ (by omega)
  calc 2 ^ n ≤ p * (2 ^ n / p + 1) := h2.le
    _ = 2 ^ n / p * p + p := by ring
    _ ≤ _ := Nat.add_le_add_right (Nat.mul_le_mul_right p h1) p

/-- **Bias bound (upper).** -/
theorem eventProb_bitsVal_mod_le (n p r : ℕ) (hp : 0 < p) :
    eventProb (univ.filter fun v : BitString n ↦ bitsVal v % p = r) ≤ 1 / p + 1 / 2 ^ n := by
  have hp' : (0 : ℚ) < p := by exact_mod_cast hp
  have h : ((univ.filter fun v : BitString n ↦ bitsVal v % p = r).card : ℚ) * p ≤ 2 ^ n + p := by
    exact_mod_cast card_bitsVal_mod_mul_le n p r hp
  unfold eventProb
  rw [div_add_div _ _ hp'.ne' (by positivity), div_le_div_iff₀ (by positivity) (by positivity)]
  have := mul_le_mul_of_nonneg_right h (by positivity : (0 : ℚ) ≤ 2 ^ n)
  linarith

/-- **Bias bound (lower).** -/
theorem eventProb_bitsVal_mod_ge (n p r : ℕ) (hr : r < p) :
    1 / p - 1 / 2 ^ n ≤ eventProb (univ.filter fun v : BitString n ↦ bitsVal v % p = r) := by
  have hp' : (0 : ℚ) < p := by exact_mod_cast (show 0 < p by omega)
  have h : (2 : ℚ) ^ n ≤ ((univ.filter fun v : BitString n ↦ bitsVal v % p = r).card : ℚ) * p + p := by
    exact_mod_cast two_pow_le_card_bitsVal_mod_mul_add n p r hr
  unfold eventProb
  rw [div_sub_div _ _ hp'.ne' (by positivity), div_le_div_iff₀ (by positivity) (by positivity)]
  have := mul_le_mul_of_nonneg_right h (by positivity : (0 : ℚ) ≤ 2 ^ n)
  linarith

/-- Conditioning on the residue: the probability of hitting `S` is the sum over `r ∈ S`. -/
theorem eventProb_bitsVal_mod_mem_eq_sum (n p : ℕ) (S : Finset ℕ) :
    eventProb (univ.filter fun v : BitString n ↦ bitsVal v % p ∈ S) =
      ∑ r ∈ S, eventProb (univ.filter fun v : BitString n ↦ bitsVal v % p = r) := by
  rw [eventProb_eq_sum_fiberwise _ S (fun v ↦ bitsVal v % p) (by intro v hv; simpa using hv)]
  refine sum_congr rfl fun r hr ↦ ?_
  congr 1
  ext v
  simp only [mem_filter, mem_univ, true_and]
  exact ⟨fun h ↦ h.2, fun h ↦ ⟨h ▸ hr, h⟩⟩

/-- Hitting a set of residues. -/
theorem eventProb_bitsVal_mod_mem_ge (n p : ℕ) (S : Finset ℕ) (hS : ∀ r ∈ S, r < p) :
    S.card * (1 / p - 1 / 2 ^ n) ≤ eventProb (univ.filter fun v : BitString n ↦ bitsVal v % p ∈ S) := by
  rw [eventProb_bitsVal_mod_mem_eq_sum, ← nsmul_eq_mul, ← sum_const]
  exact sum_le_sum fun r hr ↦ eventProb_bitsVal_mod_ge n p r (hS r hr)

theorem eventProb_bitsVal_mod_mem_le (n p : ℕ) (hp : 0 < p) (S : Finset ℕ) :
    eventProb (univ.filter fun v : BitString n ↦ bitsVal v % p ∈ S) ≤ S.card * (1 / p + 1 / 2 ^ n) := by
  rw [eventProb_bitsVal_mod_mem_eq_sum, ← nsmul_eq_mul, ← sum_const]
  exact sum_le_sum fun r _ ↦ eventProb_bitsVal_mod_le n p r hp

end SparseGcd
