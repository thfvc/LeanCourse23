import LeanCourse.Common
set_option linter.unusedVariables false
open Real Function
local macro_rules | `($x ^ $y) => `(HPow.hPow $x $y)

/-
* From Mathematics in Lean https://leanprover-community.github.io/mathematics_in_lean
  Read chapter 5, all sections (mostly section 2)
  Read chapter 6, all sections (mostly sections 1 and 2).

* Do the exercises corresponding to these sections in the `LeanCourse/MIL` folder.
  Feel free to skip exercises if you are confident that you can do them.

* You can use any lemmas or tactics from mathlib.

* Hand in the solutions to the exercises below. Deadline: 10.11.2023.

* When you hand in your solution, make sure that the file compiles!
  If you didn't manage to complete a particular exercise, make sure that the proof still compiles,
  by replacing the proof (or part of the proof) by `sorry`.
-/


open Nat Finset BigOperators in
lemma exercise4_1 (n : ℕ) :
    (∑ i in range (n + 1), i ^ 3 : ℚ) = (∑ i in range (n + 1), i : ℚ) ^ 2 := by

    have (k : ℕ) : 2 * ∑ x in range (k + 1), (x : ℚ) = ((k : ℚ) + 1) * ↑k := by
      induction k
      case zero => simp
      case succ l ih =>
        rw [sum_range_succ, mul_add, ih]
        push_cast
        ring
    induction n
    case zero =>
      simp
    case succ k ih =>
      rw [sum_range_succ, ih]
      symm
      rw [sum_range_succ, add_sq, add_assoc]
      rw [add_left_cancel_iff]
      rw [sq, pow_three]
      push_cast
      rw [←add_mul, ←mul_assoc]
      rw [mul_eq_mul_right_iff]
      left
      rw [mul_add_one]
      rw [add_right_cancel_iff]
      exact this k






open Set in
/-
Suppose `(A i)_i` is a sequence of sets indexed by a well-ordered type
(this is an order where every nonempty set has a minimum element).
We now define a new sequence by `C n = A n \ (⋃ i < n, A i)`.
In this exercise, we show that the new sequence is pairwise disjoint but has the same union as the
original sequence.
-/
lemma exercise4_2 {ι α : Type*} [LinearOrder ι] [wf : WellFoundedLT ι] (A C : ι → Set α)
  (hC : ∀ i, C i = A i \ ⋃ j < i, A j) : Pairwise (Disjoint on C) ∧ ⋃ i, C i = ⋃ i, A i := by
  have h := wf.wf.has_min
  have c_sub_a (i : ι) : C i ⊆ A i := by
    intro X hx
    rw [hC] at hx
    exact mem_of_mem_diff hx
  constructor
  · intro i j hij
    apply disjoint_iff_inter_eq_empty.mpr
    rw [eq_empty_iff_forall_not_mem]
    intro x hx
    simp at hx

    let s := {i : ι | x ∈ A i}
    have sne : s.Nonempty := by
      use i
      simp
      apply c_sub_a i
      exact hx.1
    obtain ⟨k, hk⟩ := h s sne
    apply hij

    simp at hk

    have kei : k = i := by
      apply le_antisymm
      · exact hk.2 i (c_sub_a i hx.1)
      · rw [← not_lt]
        intro hneg
        have : x ∈ ⋃ j < i, A j := by
          simp
          use k
          exact ⟨hneg, hk.1⟩
        have : x ∉ C i := by
          rw [hC]
          exact not_mem_diff_of_mem this
        exact this hx.1
    have kej : k = j := by
      apply le_antisymm
      · exact  hk.2 j (c_sub_a j hx.2)
      · rw [← not_lt]
        intro hneg
        have : x ∈ ⋃ l < j, A l := by
          simp
          use k
          exact ⟨hneg, hk.1⟩
        have : x ∉ C j := by
          rw [hC]
          exact not_mem_diff_of_mem this
        exact this hx.2
    rw [← kei, ← kej]
  · ext x
    constructor
    · intro hx
      obtain ⟨s, hs⟩ := hx
      obtain ⟨i, hi⟩ := hs.1
      simp at hi
      simp
      use i
      rw [← hi] at hs
      apply c_sub_a
      exact hs.2
    · intro hx
      obtain ⟨s, hs⟩ := hx
      obtain ⟨j, hj⟩ := hs.1
      simp at hj
      let t := {i : ι | x ∈ A i}
      have tne : t.Nonempty := by
        use j
        simp
        rw [hj]
        exact hs.2
      obtain ⟨i, ih⟩ := h t tne
      simp
      use i
      rw [hC, mem_diff]
      constructor
      · exact ih.1
      · intro hneg
        simp at hneg
        obtain ⟨k, hk⟩ := hneg
        have : k ∈ t := by
          simp
          exact hk.2
        exact ih.2 k hk.2 $ hk.1

/-- Let's prove that the positive reals form a group under multiplication.
Note: in this exercise `rw` and `simp` will not be that helpful, since the definition is hidden
behind notation. But you can use apply to use the lemmas about real numbers.

Note: any field mentioning `div`, `npow` or `zpow` are fields that you don't have to give when
defining a group. These are operations defined in terms of the group structure. -/

def PosReal : Type := {x : ℝ // 0 < x}

@[ext] lemma PosReal.ext (x y : PosReal) (h : x.1 = y.1) : x = y := Subtype.ext h


def mul' (a b : PosReal) : PosReal :=
  ⟨(a.1 * b.1), Real.mul_pos a.2 b.2⟩

lemma mul'_assoc (a b c : PosReal) : mul' (mul' a b) c = mul' a (mul' b c) := by
  have : (mul' (mul' a b) c).1 = (mul' a (mul' b c)).1 := by
    calc (mul' (mul' a b) c).1
      _ = (mul' a b).1 * c.1 := by rfl
      _ = a.1 * b.1 * c.1 := by rfl
      _ = a.1 * (b.1 * c.1) := by exact mul_assoc a.1 b.1 c.1
      _ = a.1 * (mul' b c).1 := by rfl
      _ = (mul' a (mul' b c)).1 := by rfl
  exact PosReal.ext (mul' (mul' a b) c) (mul' a (mul' b c)) this

def one' : PosReal := ⟨(1 : ℝ), one_pos⟩

lemma one'_mul' (a : PosReal) : mul' one' a = a := by
  have : (mul' one' a).1 = a.1 := by
    calc (mul' one' a).1
      _ = one'.1 * a.1 := by rfl
      _ = 1 * a.1 := by rfl
      _ = a.1 := by exact one_mul a.1
  exact PosReal.ext (mul' one' a) a this

lemma mul'_one' (a : PosReal) : mul' a one' = a := by
  have : (mul' a one').1 = a.1 := by
    calc (mul' a one').1
      _ = a.1 * one'.1 := by rfl
      _ = a.1 * 1 := by rfl
      _ = a.1 := by exact mul_one a.1
  exact PosReal.ext (mul' a one') a this

noncomputable def inv' (a : PosReal) : PosReal := --unsure why I need noncomputable is here
  ⟨(a.1)⁻¹, inv_pos.mpr a.2⟩

lemma mul'_left_inv' (a : PosReal) : mul' (inv' a) a = one' := by
  have anez : a.1 ≠ 0 := by
    linarith [a.2]
  have : (mul' (inv' a) a).1 = one'.1 := by
    calc (mul' (inv' a) a).1
      _ = (inv' a).1 * a.1 := by rfl
      _ = (a.1)⁻¹ * a.1 := by rfl
      _ = 1 := by refine inv_mul_cancel anez
      _ = one'.1 := by rfl
  exact PosReal.ext (mul' (inv' a) a) one' this

lemma exercise4_3 : Group PosReal where
  mul := mul'
  mul_assoc := mul'_assoc
  one := one'
  one_mul := one'_mul'
  mul_one := mul'_one'
  inv := inv'
  mul_left_inv := mul'_left_inv'


/- Next, we'll prove that if `2 ^ n - 1` is prime, then `n` is prime.
The first exercise is a preparation, and I've given you a skeleton of the proof for the
second exercise. Note how we do some computations in the integers, since the subtraction on `ℕ`
is less well-behaved.
(The converse is not true, because `89 ∣ 2 ^ 11 - 1`) -/


open Nat in
lemma exercise4_4 (n : ℕ) :
    ¬ Nat.Prime n ↔ n = 0 ∨ n = 1 ∨ ∃ a b : ℕ, 2 ≤ a ∧ 2 ≤ b ∧ n = a * b := by
    constructor
    · intro hn
      by_contra h
      push_neg at h
      apply hn
      rw [@prime_def_lt']
      constructor
      · refine (two_le_iff n).mpr ?mp.left.a
        exact ⟨h.1, h.2.1⟩
      · intro m hm hmn
        intro hm'
        obtain ⟨k, hk⟩ := hm'
        have h' := h.2.2
        specialize h' m k hm
        have hk' : 2 ≤ k := by
          apply (two_le_iff k).mpr
          constructor
          · intro h0
            apply h.1
            rw [hk, h0]
            rfl
          · intro h1
            apply Nat.ne_of_lt hmn
            rw [hk, h1]
            simp
        apply h' hk'
        exact hk
    · intro hn
      obtain hn0 | hn1 | hn2 := hn
      · rw [hn0]
        exact Nat.not_prime_zero
      · rw [hn1]
        exact Nat.not_prime_one
      · intro hn'
        obtain ⟨a, b, ha, hb, hab⟩ := hn2
        rw [prime_def_lt] at hn'
        have bneo : b ≠ 1 := by exact Nat.ne_of_gt hb
        have bltn : b < n := by
          rw [hab]
          calc a * b
            _ ≥ 2 * b := by exact Nat.mul_le_mul_right b ha
            _ = b + b := by rw [two_mul]
            _ > 0 + b := by linarith
            _ = b     := by rw [zero_add]
        have bdivn : b ∣ n := by
          use a
          rw [mul_comm]
          exact hab
        exact bneo $ hn'.2 b bltn bdivn -- I like this last line, but I can see that it might not be elegant code








lemma exercise4_5 (n : ℕ) (hn : Nat.Prime (2 ^ n - 1)) : Nat.Prime n := by
  by_contra h2n
  rw [exercise4_4] at h2n
  obtain rfl|rfl|⟨a, b, ha, hb, rfl⟩ := h2n
  · apply Nat.not_prime_zero
    exact hn
  · apply Nat.not_prime_one
    exact hn
  have h : (2 : ℤ) ^ a - 1 ∣ (2 : ℤ) ^ (a * b) - 1
  · rw [← Int.modEq_zero_iff_dvd]
    have bne0 : b ≠ 0 := by exact Nat.not_eq_zero_of_lt hb
    calc (2 : ℤ) ^ (a * b) - 1
        ≡ ((2 : ℤ) ^ a) ^ b - 1 [ZMOD (2 : ℤ) ^ a - 1] := by rw [pow_mul]
      --_ ≡ ((2 : ℤ) ^ a - 1 + 1) ^ b - 1 [ZMOD (2 : ℤ) ^ a - 1] := by rw [Int.sub_add_cancel]
      --_ ≡ ∑ i in range b, (choose i b) * ((2 : ℤ) ^ a - 1) ^ i * 1 ^ (b - i) [ZMOD (2 : ℤ) ^ a - 1] := by rw?
      _ ≡ (1 : ℤ) ^ b - 1 [ZMOD (2 : ℤ) ^ a - 1] := by gcongr; apply Int.modEq_sub
      --_ ≡ (1 : ℤ) ^ b - 1 [ZMOD (2 : ℤ) ^ a - 1] := by rw [Int.zero_add]
      _ ≡ (1 : ℤ) - 1 [ZMOD (2 : ℤ) ^ a - 1] := by rw [one_pow]
      _ ≡ 0 [ZMOD (2 : ℤ) ^ a - 1] := by rfl
  have h2 : 2 ^ 2 ≤ 2 ^ a := by
    refine pow_le_pow' ?ha ha
    linarith
  have h3 : 1 ≤ 2 ^ a := by
    exact Nat.one_le_two_pow a
  have h3' : 1 < 2 ^ a := by
    calc 1
      _ < 4 := by norm_num
      _ = 2 ^ 2 := by rw [Nat.pow_two]
      _ ≤ 2 ^ a := by exact h2
  have h4 : 2 ^ a - 1 ≠ 1 := by zify; simp [h3]; linarith
  have h5 : 2 ^ a - 1 < 2 ^ (a * b) - 1 := by
    apply tsub_lt_tsub_right_of_le h3
    rw [Nat.pow_mul]
    calc 2 ^ a
      _ = (2 ^ a) * 1        := by rw [mul_one]
      _ < (2 ^ a) * (2 ^ a)  := by exact Nat.mul_lt_mul_of_pos_left h3' h3
      _ = (2 ^ a) ^ 2        := by rw [Nat.pow_two]
      _ ≤ (2 ^ a) ^ b        := by exact (Nat.pow_le_iff_le_right h3').mpr hb
  have h6' : 2 ^ 0 ≤ 2 ^ (a * b) := by
    /-
    rw [Nat.pow_zero]
    exact Nat.one_le_two_pow (a * b) -- this works, but doesnt feel in the spirit of this proof, considering that this is just a precursor for h6
    -/
    apply pow_le_pow one_le_two
    calc 0
      _ ≤ 4 := by exact Nat.zero_le 4
      _ = 2 * 2 := by exact rfl
      _ ≤ 2 * b := by exact Nat.mul_le_mul_left 2 hb
      _ ≤ a * b := by exact Nat.mul_le_mul_right b ha
  have h6 : 1 ≤ 2 ^ (a * b) := h6'
  have h' : 2 ^ a - 1 ∣ 2 ^ (a * b) - 1
  · norm_cast at h
  rw [Nat.prime_def_lt] at hn
  exact h4 $ hn.2 (2 ^ a - 1) h5 h'


/- Here is another exercise about numbers. Make sure you find a simple proof on paper first.
-/

-- just a remark: I cant do number theory, it's hard

lemma exercise4_6 (a b : ℕ) (ha : 0 < a) (hb : 0 < b) :
    ¬ IsSquare (a ^ 2 + b) ∨ ¬ IsSquare (b ^ 2 + a) := by
    by_contra h
    push_neg at h
    obtain ⟨n, hn⟩ := h.1
    obtain ⟨m, hm⟩ := h.2

    rw [sq] at hn
    rw [sq] at hm

    have anz : a ≠ 0 := Nat.pos_iff_ne_zero.mp ha

    have mgtz : m > 0 := by
      have mnez : m ≠ 0 := by
        intro h
        rw [h] at hm
        simp at hm
        exact anz hm.2
      exact Nat.pos_iff_ne_zero.mpr mnez

    have that : a = m * m - b * b := (tsub_eq_of_eq_add_rev (id hm.symm)).symm

    have msubbge1 : 1 ≤ m - b := by
      apply Nat.one_le_iff_ne_zero.mpr
      intro h
      apply anz
      rw [that, Nat.mul_self_sub_mul_self_eq, h, Nat.mul_zero]

    have blta : b < a := by
      calc
        b < m + b := by exact Nat.lt_add_of_pos_left mgtz
        _ ≤ (m + b) * (m - b) := by exact Nat.le_mul_of_pos_right msubbge1
        _ = m * m - b * b := by rw [Nat.mul_self_sub_mul_self_eq]
        _ = a := by rw [that]

    have bnz : b ≠ 0 := Nat.pos_iff_ne_zero.mp hb

    have ngtz : n > 0 := by
      have nnez : n ≠ 0 := by
        intro h
        rw [h] at hn
        simp at hn
        exact bnz hn.2
      exact Nat.pos_iff_ne_zero.mpr nnez

    have that : b = n * n - a * a := (tsub_eq_of_eq_add_rev (id hn.symm)).symm

    have nsubage1 : 1 ≤ n - a := by
      apply Nat.one_le_iff_ne_zero.mpr
      intro h
      apply bnz
      rw [that, Nat.mul_self_sub_mul_self_eq, h, Nat.mul_zero]

    have altb : a < b := by
      calc
        a < n + a := by exact Nat.lt_add_of_pos_left ngtz
        _ ≤ (n + a) * (n - a) := by exact Nat.le_mul_of_pos_right nsubage1
        _ = n * n - a * a := by rw [Nat.mul_self_sub_mul_self_eq]
        _ = b := by rw [that]

    have : ¬ a < b := by exact Nat.lt_asymm blta
    exact this altb
