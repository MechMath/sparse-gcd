import SparseGcd.Field.Package
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.GroupTheory.OrderOfElement
import Mathlib.GroupTheory.SpecificGroups.Cyclic.Basic
import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots

/-!
# Elements of exact order `E` in `𝔽_p^*` (Lemma 15 / Lemma 22, ω part)

`ω = a^{(p-1)/E}` has `ω^E = 1`; the order test `ω^{E/ℓ_i} ≠ 1` for every prime `ℓ_i ∣ E`
(with `E` squarefree with prime factors exactly the `ℓ_i`) is equivalent to `orderOf ω = E`.
Over a uniform `a ∈ 𝔽_p^*` the test succeeds with probability `φ(E)/E ≥ 1/(m+1)`.
-/

open Finset

namespace SparseGcd

/-- The executable order test: `ω^E = 1` and `ω^{E/q} ≠ 1` for every listed prime `q`. -/
def OrderTest {p : ℕ} (E : ℕ) (ℓ : List ℕ) (ω : ZMod p) : Prop :=
  ω ^ E = 1 ∧ ∀ q ∈ ℓ, ω ^ (E / q) ≠ 1

instance {p : ℕ} (E : ℕ) (ℓ : List ℕ) (ω : ZMod p) : Decidable (OrderTest E ℓ ω) := by
  unfold OrderTest; infer_instance

set_option linter.unusedVariables false in
/-- The order test characterises exact order `E = ∏ ℓ`. (`hnodup` is not needed for this
equivalence; it is kept for a uniform interface.) -/
theorem orderOf_eq_iff_orderTest {p : ℕ} {ℓ : List ℕ} (hprime : ∀ q ∈ ℓ, q.Prime)
    (hnodup : ℓ.Nodup) (ω : ZMod p) : orderOf ω = ℓ.prod ↔ OrderTest ℓ.prod ℓ ω := by
  have hpos : 0 < ℓ.prod := prod_pos_of_prime hprime
  constructor
  · intro h
    refine ⟨h ▸ pow_orderOf_eq_one ω, fun q hq hcontra ↦ ?_⟩
    have hq1 := (hprime q hq).one_lt
    have hdvd : orderOf ω ∣ ℓ.prod / q := orderOf_dvd_iff_pow_eq_one.mpr hcontra
    have hlt : ℓ.prod / q < ℓ.prod := Nat.div_lt_self hpos hq1
    have hqpos : 0 < ℓ.prod / q :=
      Nat.div_pos (Nat.le_of_dvd hpos (mem_dvd_prod hq)) (hprime q hq).pos
    have := Nat.le_of_dvd hqpos hdvd
    omega
  · rintro ⟨h1, h2⟩
    exact orderOf_eq_of_pow_and_pow_div_prime hpos h1 fun q hq hdvd ↦
      h2 q ((prime_dvd_prod_iff_mem hprime hq).mp hdvd)

/-- Raising an element of order `E` to `E/q` (with `q ∣ E`) gives an element of order `q`. -/
theorem orderOf_pow_div {G : Type*} [Monoid G] {ω : G} {E q : ℕ} (hω : orderOf ω = E)
    (hq : q ∣ E) (hE : 0 < E) : orderOf (ω ^ (E / q)) = q := by
  subst hω
  exact orderOf_pow_orderOf_div hE.ne' hq

/-- `ω^a = ω^b ↔ a ≡ b (mod E)` for an element of order `E`. -/
theorem pow_eq_pow_iff_mod {G : Type*} [Monoid G] {ω : G} {E : ℕ} (hω : orderOf ω = E)
    (hE : 0 < E) (a b : ℕ) : ω ^ a = ω ^ b ↔ a % E = b % E := by
  subst hω
  exact (orderOf_pos_iff.mp hE).pow_inj_mod

/-- The candidates `a ∈ 𝔽_p` whose power `a^{(p-1)/E}` has exact order `E`. -/
noncomputable def goodBases (p E : ℕ) [NeZero p] : Finset (ZMod p) :=
  univ.filter fun a ↦ orderOf (a ^ ((p - 1) / E)) = E

/-- `orderOf 0 = 0` in a nontrivial monoid with zero. -/
private theorem orderOf_zero_eq_zero {M : Type*} [MonoidWithZero M] [Nontrivial M] :
    orderOf (0 : M) = 0 :=
  orderOf_eq_zero_iff'.mpr fun n hn ↦ by rw [zero_pow hn.ne']; exact zero_ne_one

/-- The number of `i < E·d` coprime to `E` is `d·φ(E)`: `d` blocks of length `E`. -/
private theorem card_range_mul_filter_coprime (E d : ℕ) :
    ((range (E * d)).filter (Nat.Coprime E)).card = d * Nat.totient E := by
  rw [← Nat.count_eq_card_filter_range]
  induction d with
  | zero => simp
  | succ d ih =>
    rw [Nat.mul_succ, Nat.count_add, ih, Nat.succ_mul]
    congr 1
    simp only [Nat.coprime_mul_left_add_right]
    rw [Nat.count_eq_card_filter_range]
    rfl

/-- In a cyclic group of order `E·d`, exactly `d·φ(E)` elements `u` satisfy `orderOf (u^d) = E`. -/
private theorem card_filter_orderOf_pow_eq {G : Type*} [Group G] [Fintype G] [DecidableEq G]
    [IsCyclic G] {E d : ℕ} (hE : 0 < E) (hcard : Fintype.card G = E * d) :
    (univ.filter fun u : G ↦ orderOf (u ^ d) = E).card = d * Nat.totient E := by
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := G)
  have hog : orderOf g = E * d := by
    rw [orderOf_eq_card_of_forall_mem_zpowers hg, Nat.card_eq_fintype_card, hcard]
  have hd : 0 < d := by
    rcases Nat.eq_zero_or_pos d with h | h
    · rw [h, mul_zero] at hcard; exact absurd hcard Fintype.card_ne_zero
    · exact h
  have himg : (range (E * d)).image (fun i ↦ g ^ i) = univ := by
    rw [← hog]; exact IsCyclic.image_range_orderOf hg
  rw [← himg, filter_image, card_image_of_injOn, ← card_range_mul_filter_coprime]
  · congr 1
    ext i
    simp only [mem_filter, mem_range, and_congr_right_iff]
    intro _
    rw [← pow_mul, orderOf_pow, hog, Nat.gcd_mul_right, Nat.mul_div_mul_right _ _ hd,
      Nat.div_eq_self, Nat.coprime_iff_gcd_eq_one]
    omega
  · intro i hi j hj hij
    exact pow_injOn_Iio_orderOf (by simpa [hog] using (mem_filter.mp (mem_coe.mp hi)).1)
      (by simpa [hog] using (mem_filter.mp (mem_coe.mp hj)).1) hij

/-- **Density of good bases.** For `p` prime and `E ∣ p - 1`, exactly `φ(E)·(p-1)/E` elements of
`𝔽_p` are good bases (`0` is never good). -/
theorem card_goodBases_mul {p E : ℕ} [Fact p.Prime] (hE : E ∣ p - 1) (hE0 : 0 < E) :
    (goodBases p E).card * E = Nat.totient E * (p - 1) := by
  set d := (p - 1) / E with hd
  have hpd : p - 1 = E * d := (Nat.mul_div_cancel_left' hE).symm
  have hp1 : 0 < p - 1 := Nat.sub_pos_of_lt (Fact.out : p.Prime).one_lt
  have hd0 : 0 < d := Nat.pos_of_ne_zero fun h ↦ by rw [h, mul_zero] at hpd; omega
  have hcardU : Fintype.card (ZMod p)ˣ = E * d := by rw [ZMod.card_units p, hpd]
  have key : goodBases p E =
      (univ.filter fun u : (ZMod p)ˣ ↦ orderOf (u ^ d) = E).map ⟨Units.val, Units.val_injective⟩ := by
    ext a
    simp only [goodBases, mem_filter, mem_univ, true_and, mem_map, Function.Embedding.coeFn_mk]
    constructor
    · intro ha
      have ha0 : a ≠ 0 := by
        rintro rfl
        rw [zero_pow hd0.ne', orderOf_zero_eq_zero] at ha
        exact hE0.ne ha
      refine ⟨Units.mk0 a ha0, ?_, Units.val_mk0 ha0⟩
      rw [← orderOf_units, Units.val_pow_eq_pow_val, Units.val_mk0]
      exact ha
    · rintro ⟨u, hu, rfl⟩
      rwa [← Units.val_pow_eq_pow_val, orderOf_units]
  rw [key, card_map, card_filter_orderOf_pow_eq hE0 hcardU, hpd]
  ring

theorem card_goodBases_ge {p : ℕ} [Fact p.Prime] {ℓ : List ℕ} (hprime : ∀ q ∈ ℓ, q.Prime)
    (hnodup : ℓ.Nodup) (hE : ℓ.prod ∣ p - 1) :
    ((p : ℚ) - 1) / (ℓ.length + 1) ≤ (goodBases p ℓ.prod).card := by
  have hE0 := prod_pos_of_prime hprime
  have h := card_goodBases_mul hE hE0
  have ht := totient_div_ge hprime hnodup
  have hp1 : 1 ≤ p := (Fact.out : p.Prime).one_le
  have hq : ((goodBases p ℓ.prod).card : ℚ) * ℓ.prod = Nat.totient ℓ.prod * ((p : ℚ) - 1) := by
    have := congrArg (Nat.cast (R := ℚ)) h
    rwa [Nat.cast_mul, Nat.cast_mul, Nat.cast_sub hp1, Nat.cast_one] at this
  have hEq : (0 : ℚ) < ℓ.prod := by exact_mod_cast hE0
  have hp1' : (0 : ℚ) ≤ (p : ℚ) - 1 := by
    have : (1 : ℚ) ≤ p := by exact_mod_cast hp1
    linarith
  calc ((p : ℚ) - 1) / (ℓ.length + 1) = (1 / (ℓ.length + 1)) * ((p : ℚ) - 1) := by ring
    _ ≤ (Nat.totient ℓ.prod : ℚ) / ℓ.prod * ((p : ℚ) - 1) :=
      mul_le_mul_of_nonneg_right ht hp1'
    _ = (goodBases p ℓ.prod).card := by
      rw [div_mul_eq_mul_div, ← hq, mul_div_assoc, div_self hEq.ne', mul_one]

/-- `E = 1`: every nonzero `a` is a good base (`ω = 1`, `orderOf 1 = 1`). -/
theorem goodBases_one {p : ℕ} [Fact p.Prime] : goodBases p 1 = univ.filter (· ≠ 0) := by
  ext a
  simp only [goodBases, Nat.div_one, mem_filter, mem_univ, true_and]
  constructor
  · rintro h rfl
    have hp1 : 0 < p - 1 := Nat.sub_pos_of_lt (Fact.out : p.Prime).one_lt
    rw [zero_pow hp1.ne', orderOf_zero_eq_zero] at h
    exact zero_ne_one h
  · intro ha
    rw [ZMod.pow_card_sub_one_eq_one ha, orderOf_one]

end SparseGcd
