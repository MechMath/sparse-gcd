import SparseGcd.Basic.Bernoulli
import Mathlib.NumberTheory.LucasPrimality
import Mathlib.Data.Nat.Totient
import Mathlib.Tactic

/-!
# The prime-field data package (Lemma 15 / Lemma 22, data part)

A `PrimePackage` is the *output* of the BCR/AIRR construction (Lemma 14): distinct primes
`ℓ_0, …, ℓ_{N-1}`, an integer `c ≥ 1` and the prime `p = 1 + c ∏ ℓ_j`. Only the first `m` primes
are Boolean primes; the remaining `N - m` are dummy primes which only enlarge `p`. We prove the
purely arithmetic consequences: `E := ∏_{i<m} ℓ_i` divides `p - 1`, `E / p ≤ 2^{-(N-m)}`,
`bitLength E ≤ bitLength p`, and `E` is squarefree with the listed prime factors.
-/

namespace SparseGcd

structure PrimePackage where
  /-- The distinct primes `ℓ_0, …, ℓ_{N-1}` (Boolean primes first, dummy primes last). -/
  ℓ : List ℕ
  /-- The cofactor `c` (the paper has `c ≥ 11`; only `c ≥ 1` is used). -/
  c : ℕ
  hprime : ∀ q ∈ ℓ, q.Prime
  hnodup : ℓ.Nodup
  hc : 1 ≤ c
  hp : (1 + c * ℓ.prod).Prime

namespace PrimePackage

variable (P : PrimePackage)

/-- The field characteristic `p = 1 + c ∏ ℓ_j`. -/
def p : ℕ := 1 + P.c * P.ℓ.prod

/-- The number of primes `N`. -/
def N : ℕ := P.ℓ.length

/-- The Boolean primes: the first `m` primes. -/
def boolPrimes (m : ℕ) : List ℕ := P.ℓ.take m

/-- `E = ∏_{i<m} ℓ_i`. -/
def E (m : ℕ) : ℕ := (P.ℓ.take m).prod

/-- The dummy product `∏_{j ≥ m} ℓ_j`. -/
def Pdum (m : ℕ) : ℕ := (P.ℓ.drop m).prod

theorem p_prime : P.p.Prime := P.hp

theorem two_le_p : 2 ≤ P.p := P.p_prime.two_le

theorem E_mul_Pdum (m : ℕ) : P.E m * P.Pdum m = P.ℓ.prod :=
  List.prod_take_mul_prod_drop _ _

theorem E_pos (m : ℕ) : 0 < P.E m :=
  List.prod_pos fun q hq ↦ (P.hprime q (List.mem_of_mem_take hq)).pos

theorem Pdum_pos (m : ℕ) : 0 < P.Pdum m :=
  List.prod_pos fun q hq ↦ (P.hprime q (List.mem_of_mem_drop hq)).pos

theorem E_dvd_p_sub_one (m : ℕ) : P.E m ∣ P.p - 1 := by
  show P.E m ∣ 1 + P.c * P.ℓ.prod - 1
  rw [Nat.add_sub_cancel_left]
  exact (Dvd.intro _ (P.E_mul_Pdum m)).mul_left _

theorem E_lt_p (m : ℕ) : P.E m < P.p := by
  have h1 : P.E m ≤ P.E m * P.Pdum m := Nat.le_mul_of_pos_right _ (P.Pdum_pos m)
  have h2 : P.ℓ.prod ≤ P.c * P.ℓ.prod := Nat.le_mul_of_pos_left _ P.hc
  rw [P.E_mul_Pdum] at h1
  show P.E m < 1 + P.c * P.ℓ.prod
  omega

theorem two_pow_le_Pdum {m : ℕ} (hm : m ≤ P.N) : 2 ^ (P.N - m) ≤ P.Pdum m := by
  have := List.pow_length_le_prod (P.ℓ.drop m) 2
    fun x hx ↦ (P.hprime x (List.mem_of_mem_drop hx)).two_le
  rwa [List.length_drop] at this

/-- `E / p ≤ 2^{-(N-m)}`: the dummy primes push `p` far above `E`. -/
theorem E_div_p_le {m : ℕ} (hm : m ≤ P.N) : (P.E m : ℚ) / P.p ≤ 1 / 2 ^ (P.N - m) := by
  have hN : P.E m * 2 ^ (P.N - m) ≤ P.p := by
    calc P.E m * 2 ^ (P.N - m) ≤ P.E m * P.Pdum m := Nat.mul_le_mul_left _ (P.two_pow_le_Pdum hm)
      _ = P.ℓ.prod := P.E_mul_Pdum m
      _ ≤ P.c * P.ℓ.prod := Nat.le_mul_of_pos_left _ P.hc
      _ ≤ P.p := Nat.le_add_left _ _
  have hp : (0 : ℚ) < P.p := by exact_mod_cast P.p_prime.pos
  rw [div_le_div_iff₀ hp (by positivity), one_mul]
  exact_mod_cast hN

theorem size_E_le_size_p (m : ℕ) : Nat.size (P.E m) ≤ Nat.size P.p :=
  Nat.size_le_size (P.E_lt_p m).le

theorem boolPrimes_prime (m : ℕ) : ∀ q ∈ P.boolPrimes m, q.Prime :=
  fun q hq ↦ P.hprime q (List.mem_of_mem_take hq)

theorem boolPrimes_nodup (m : ℕ) : (P.boolPrimes m).Nodup :=
  (List.take_sublist m P.ℓ).nodup P.hnodup

theorem boolPrimes_length {m : ℕ} (hm : m ≤ P.N) : (P.boolPrimes m).length = m := by
  show (P.ℓ.take m).length = m
  rw [List.length_take]
  exact Nat.min_eq_left hm

theorem E_eq_prod_boolPrimes (m : ℕ) : P.E m = (P.boolPrimes m).prod := rfl

/-- `p - 1 = c · E · Pdum`. -/
theorem p_sub_one_eq (m : ℕ) : P.p - 1 = P.c * (P.E m * P.Pdum m) := by
  rw [P.E_mul_Pdum]
  exact Nat.add_sub_cancel_left ..

end PrimePackage

/-! ### Products of distinct primes -/

/-- Every prime dividing a product of primes from the list is in the list. -/
theorem prime_dvd_prod_iff_mem {ℓ : List ℕ} (hprime : ∀ q ∈ ℓ, q.Prime) {q : ℕ} (hq : q.Prime) :
    q ∣ ℓ.prod ↔ q ∈ ℓ := by
  induction ℓ with
  | nil => simp [Nat.dvd_one, hq.ne_one]
  | cons a l ih =>
    rw [List.prod_cons, hq.dvd_mul, List.mem_cons,
      Nat.prime_dvd_prime_iff_eq hq (hprime a List.mem_cons_self),
      ih fun x hx ↦ hprime x (List.mem_cons_of_mem _ hx)]

/-- The head of a list of distinct primes is coprime to the product of the tail. -/
theorem coprime_head_prod_tail {a : ℕ} {l : List ℕ} (hprime : ∀ q ∈ a :: l, q.Prime)
    (hnodup : (a :: l).Nodup) : a.Coprime l.prod :=
  Nat.coprime_list_prod_right_iff.mpr fun n hn ↦
    (Nat.coprime_primes (hprime a List.mem_cons_self) (hprime n (List.mem_cons_of_mem _ hn))).mpr
      fun h ↦ (List.nodup_cons.mp hnodup).1 (h ▸ hn)

theorem squarefree_prod_of_nodup {ℓ : List ℕ} (hprime : ∀ q ∈ ℓ, q.Prime) (hnodup : ℓ.Nodup) :
    Squarefree ℓ.prod := by
  induction ℓ with
  | nil => exact squarefree_one
  | cons a l ih =>
    rw [List.prod_cons, Nat.squarefree_mul (coprime_head_prod_tail hprime hnodup)]
    exact ⟨(Nat.prime_iff.mp (hprime a List.mem_cons_self)).squarefree,
      ih (fun x hx ↦ hprime x (List.mem_cons_of_mem _ hx)) (List.nodup_cons.mp hnodup).2⟩

theorem prod_pos_of_prime {ℓ : List ℕ} (hprime : ∀ q ∈ ℓ, q.Prime) : 0 < ℓ.prod :=
  List.prod_pos fun q hq ↦ (hprime q hq).pos

theorem mem_dvd_prod {ℓ : List ℕ} {q : ℕ} (hq : q ∈ ℓ) : q ∣ ℓ.prod :=
  List.dvd_prod hq

/-- Pairwise coprimality of distinct primes. -/
theorem pairwise_coprime_of_nodup {ℓ : List ℕ} (hprime : ∀ q ∈ ℓ, q.Prime) (hnodup : ℓ.Nodup) :
    ℓ.Pairwise Nat.Coprime :=
  hnodup.imp_of_mem fun ha hb hne ↦ (Nat.coprime_primes (hprime _ ha) (hprime _ hb)).mpr hne

/-- `φ(∏ ℓ_i) / ∏ ℓ_i = ∏ (1 - 1/ℓ_i)`. -/
theorem totient_prod_of_nodup {ℓ : List ℕ} (hprime : ∀ q ∈ ℓ, q.Prime) (hnodup : ℓ.Nodup) :
    (Nat.totient ℓ.prod : ℚ) / ℓ.prod = (ℓ.map fun q : ℕ ↦ (1 : ℚ) - 1 / q).prod := by
  induction ℓ with
  | nil => simp
  | cons a l ih =>
    have ha := hprime a List.mem_cons_self
    have hl : ∀ q ∈ l, q.Prime := fun x hx ↦ hprime x (List.mem_cons_of_mem _ hx)
    rw [List.map_cons, List.prod_cons, List.prod_cons,
      Nat.totient_mul (coprime_head_prod_tail hprime hnodup), Nat.totient_prime ha,
      ← ih hl (List.nodup_cons.mp hnodup).2, Nat.cast_mul, Nat.cast_mul,
      Nat.cast_sub ha.one_le, Nat.cast_one]
    have ha0 : (a : ℚ) ≠ 0 := by exact_mod_cast ha.ne_zero
    have hP0 : (l.prod : ℚ) ≠ 0 := by exact_mod_cast (prod_pos_of_prime hl).ne'
    field_simp

/-- The Finset version of the telescoping bound, for any finite set of naturals `≥ 2`:
induction on the maximum, which is at least `card + 2` since the set sits inside `[2, max)`. -/
theorem prod_one_sub_inv_ge_finset (s : Finset ℕ) (h2 : ∀ x ∈ s, 2 ≤ x) :
    (1 : ℚ) / (s.card + 1) ≤ ∏ x ∈ s, ((1 : ℚ) - 1 / x) := by
  induction s using Finset.induction_on_max with
  | empty => simp
  | insert a s hlt ih =>
    have has : a ∉ s := fun h ↦ lt_irrefl a (hlt a h)
    have h2s : ∀ x ∈ s, 2 ≤ x := fun x hx ↦ h2 x (Finset.mem_insert_of_mem hx)
    have hcard : s.card + 2 ≤ a := by
      have hsub : s ⊆ Finset.Ico 2 a := fun x hx ↦ Finset.mem_Ico.mpr ⟨h2s x hx, hlt x hx⟩
      have := Finset.card_le_card hsub
      rw [Nat.card_Ico] at this
      have ha2 : 2 ≤ a := h2 a (Finset.mem_insert_self a s)
      omega
    rw [Finset.prod_insert has, Finset.card_insert_of_notMem has]
    have ih' := ih h2s
    have hc : (s.card : ℚ) + 2 ≤ a := by exact_mod_cast hcard
    have hpos : (0 : ℚ) < s.card + 1 := by positivity
    have ha : (0 : ℚ) < a := by linarith
    have hfac : (0 : ℚ) ≤ 1 - 1 / a := by
      rw [sub_nonneg, div_le_one ha]; linarith
    calc (1 : ℚ) / (↑(s.card + 1) + 1) ≤ (1 - 1 / a) * (1 / (s.card + 1)) := by
          push_cast
          rw [show (1 - 1 / (a : ℚ)) * (1 / (s.card + 1)) = (a - 1) / (a * (s.card + 1)) by
            field_simp]
          rw [div_le_div_iff₀ (by positivity) (by positivity)]
          nlinarith
      _ ≤ (1 - 1 / a) * ∏ x ∈ s, ((1 : ℚ) - 1 / x) := mul_le_mul_of_nonneg_left ih' hfac

/-- **Telescoping density bound.** For `m` distinct primes, `∏ (1 - 1/ℓ_i) ≥ 1/(m+1)`: after sorting,
the `i`-th smallest prime is at least `i + 2` (0-indexed), so the product is at least
`∏_{i<m} (i+1)/(i+2) = 1/(m+1)`. -/
theorem prod_one_sub_inv_ge {ℓ : List ℕ} (hprime : ∀ q ∈ ℓ, q.Prime) (hnodup : ℓ.Nodup) :
    (1 : ℚ) / (ℓ.length + 1) ≤ (ℓ.map fun q : ℕ ↦ (1 : ℚ) - 1 / q).prod := by
  rw [← List.prod_toFinset _ hnodup, ← List.toFinset_card_of_nodup hnodup]
  have h2 : ∀ x ∈ ℓ.toFinset, 2 ≤ x := fun x hx ↦ (hprime x (List.mem_toFinset.mp hx)).two_le
  exact prod_one_sub_inv_ge_finset ℓ.toFinset h2

theorem totient_div_ge {ℓ : List ℕ} (hprime : ∀ q ∈ ℓ, q.Prime) (hnodup : ℓ.Nodup) :
    (1 : ℚ) / (ℓ.length + 1) ≤ (Nat.totient ℓ.prod : ℚ) / ℓ.prod := by
  rw [totient_prod_of_nodup hprime hnodup]
  exact prod_one_sub_inv_ge hprime hnodup

end SparseGcd
