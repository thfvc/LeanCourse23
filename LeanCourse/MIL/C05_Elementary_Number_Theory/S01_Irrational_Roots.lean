import LeanCourse.Common
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Data.Nat.Prime
import Std.Data.Nat.Gcd

#print Nat.Coprime

example (m n : Nat) (h : m.Coprime n) : m.gcd n = 1 :=
  h

example (m n : Nat) (h : m.Coprime n) : m.gcd n = 1 := by
  rw [Nat.Coprime] at h
  exact h

example : Nat.Coprime 12 7 := by norm_num

example : Nat.gcd 12 8 = 4 := by norm_num

#check Nat.prime_def_lt

example (p : ℕ) (prime_p : Nat.Prime p) : 2 ≤ p ∧ ∀ m : ℕ, m < p → m ∣ p → m = 1 := by
  rwa [Nat.prime_def_lt] at prime_p

#check Nat.Prime.eq_one_or_self_of_dvd

example (p : ℕ) (prime_p : Nat.Prime p) : ∀ m : ℕ, m ∣ p → m = 1 ∨ m = p :=
  prime_p.eq_one_or_self_of_dvd

example : Nat.Prime 17 := by norm_num

-- commonly used
example : Nat.Prime 2 :=
  Nat.prime_two

example : Nat.Prime 3 :=
  Nat.prime_three

#check Nat.Prime.dvd_mul
#check Nat.Prime.dvd_mul Nat.prime_two
#check Nat.prime_two.dvd_mul

theorem even_of_even_sqr {m : ℕ} (h : 2 ∣ m ^ 2) : 2 ∣ m := by
  rw [pow_two, Nat.prime_two.dvd_mul] at h
  cases h <;> assumption

example {m : ℕ} (h : 2 ∣ m ^ 2) : 2 ∣ m :=
  Nat.Prime.dvd_of_dvd_pow Nat.prime_two h

example (a b c : Nat) (h : a * b = a * c) (h' : a ≠ 0) : b = c :=
  -- apply? suggests the following:
  (mul_right_inj' h').mp h

example {m n : ℕ} (coprime_mn : m.Coprime n) : m ^ 2 ≠ 2 * n ^ 2 := by
  intro sqr_eq
  have two_div_m : 2 ∣ m := by
    apply even_of_even_sqr
    use n ^ 2
  obtain ⟨k, meq⟩ := dvd_iff_exists_eq_mul_left.mp two_div_m
  have : 2 * (2 * k ^ 2) = 2 * n ^ 2 := by
    rw [← sqr_eq, meq]
    ring
  have : 2 * k ^ 2 = n ^ 2 := by
    apply (mul_right_inj' (Nat.succ_ne_zero 1)).mp
    exact this
  have two_div_n : 2 ∣ n := by
    apply even_of_even_sqr
    use k ^ 2
    symm
    exact this
  have : 2 ∣ m.gcd n := by
    exact Nat.dvd_gcd two_div_m two_div_n
  have : 2 ∣ 1 := by
    rwa [← coprime_mn]
  norm_num at this

lemma prime_div_of_prime_div_square {p m : ℕ} (hp : Nat.Prime p) (hmp : p ∣ m ^ 2) : p ∣ m:= by
  rw [pow_two, hp.dvd_mul] at hmp
  cases hmp <;> assumption

example {m n p : ℕ} (coprime_mn : m.Coprime n) (prime_p : p.Prime) : m ^ 2 ≠ p * n ^ 2 := by
  intro sqr_eq
  have p_div_m : p ∣ m := by
    apply prime_div_of_prime_div_square prime_p
    use n ^ 2
  obtain ⟨k, meq⟩ := dvd_iff_exists_eq_mul_left.mp p_div_m
  have : p * (p * k ^ 2) = p * n ^ 2 := by
    rw [← sqr_eq, meq]
    ring
  have : p * k ^ 2 = n ^ 2 := by
    apply (mul_right_inj' (Nat.Prime.ne_zero prime_p)).mp
    exact this
  have p_div_n : p ∣ n := by
    apply prime_div_of_prime_div_square prime_p
    use k ^ 2
    symm
    exact this
  have : p ∣ m.gcd n := by
    exact Nat.dvd_gcd p_div_m p_div_n
  have : p ∣ 1 := by
    rwa [← coprime_mn]
  apply Nat.Prime.ne_one prime_p
  exact Nat.dvd_one.mp this

#check Nat.factors
#check Nat.prime_of_mem_factors
#check Nat.prod_factors
#check Nat.factors_unique

theorem factorization_mul' {m n : ℕ} (mnez : m ≠ 0) (nnez : n ≠ 0) (p : ℕ) :
    (m * n).factorization p = m.factorization p + n.factorization p := by
  rw [Nat.factorization_mul mnez nnez]
  rfl

theorem factorization_pow' (n k p : ℕ) :
    (n ^ k).factorization p = k * n.factorization p := by
  rw [Nat.factorization_pow]
  rfl

theorem Nat.Prime.factorization' {p : ℕ} (prime_p : p.Prime) :
    p.factorization p = 1 := by
  rw [prime_p.factorization]
  simp

example {m n p : ℕ} (nnz : n ≠ 0) (prime_p : p.Prime) : m ^ 2 ≠ p * n ^ 2 := by
  intro sqr_eq
  have nsqr_nez : n ^ 2 ≠ 0 := by simpa
  have eq1 : Nat.factorization (m ^ 2) p = 2 * m.factorization p := by
    simp
  have eq2 : (p * n ^ 2).factorization p = 2 * n.factorization p + 1 := by
    rwa [← prime_p.factorization', ← factorization_pow', ← factorization_mul', mul_comm]
    exact prime_p.ne_zero
  have : 2 * m.factorization p % 2 = (2 * n.factorization p + 1) % 2 := by
    rw [← eq1, sqr_eq, eq2]
  rw [add_comm, Nat.add_mul_mod_self_left, Nat.mul_mod_right] at this
  norm_num at this

example {m n k r : ℕ} (nnz : n ≠ 0) (pow_eq : m ^ k = r * n ^ k) {p : ℕ} (prime_p : p.Prime) :
    k ∣ r.factorization p := by
  rcases r with _ | r
  · simp
  have npow_nz : n ^ k ≠ 0 := fun npowz ↦ nnz (pow_eq_zero npowz)
  have eq1 : (m ^ k).factorization p = k * m.factorization p := by
    sorry
  have eq2 : (r.succ * n ^ k).factorization p =
      k * n.factorization p + r.succ.factorization p := by
    sorry
  have : r.succ.factorization p = k * m.factorization p - k * n.factorization p := by
    rw [← eq1, pow_eq, eq2, add_comm, Nat.add_sub_cancel]
  rw [this]
  sorry

#check multiplicity
