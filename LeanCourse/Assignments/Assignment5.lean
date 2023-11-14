import LeanCourse.Common
import Mathlib.Analysis.Complex.Polynomial
import Mathlib.Data.Nat.Choose.Dvd
import Mathlib.FieldTheory.Minpoly.Basic
set_option linter.unusedVariables false
noncomputable section
open Real Function BigOperators
local macro_rules | `($x ^ $y) => `(HPow.hPow $x $y)

/-
* From Mathematics in Lean https://leanprover-community.github.io/mathematics_in_lean
  Read chapters 7 and 8, all sections.

* Do the exercises corresponding to these sections in the `LeanCourse/MIL` folder.
  Feel free to skip exercises if you are confident that you can do them.
  There are solutions in the solution folder in case you get stuck.

* Hand in the solutions to the exercises below. Deadline: 17.11.2023.

* When you hand in your solution, make sure that the file compiles!
  If you didn't manage to complete a particular exercise, make sure that the proof still compiles,
  by replacing the proof (or part of the proof) by `sorry`.
-/


section LinearMap

variable {R M₁ M₂ N : Type*} [CommRing R] [AddCommGroup M₁] [AddCommGroup M₂] [AddCommGroup N]
  [Module R M₁] [Module R M₂] [Module R N]

/- Define the coproduct of two linear maps that send (x, y) ↦ f x + g y. -/

def exercise5_1 (f : M₁ →ₗ[R] N) (g : M₂ →ₗ[R] N) : M₁ × M₂ →ₗ[R] N where
  toFun x := f x.1 + g x.2
  map_add' := by
    intro x y
    simp
    exact add_add_add_comm (f.toFun x.1) (f.toFun y.1) (g.toFun x.2) (g.toFun y.2)
  map_smul' := by
    simp


example (f : M₁ →ₗ[R] N) (g : M₂ →ₗ[R] N) (x : M₁) (y : M₂) :
  exercise5_1 f g (x, y) = f x + g y := rfl -- should be rfl


end LinearMap

section Ring
variable {R : Type*} [CommRing R]


/- Let's define ourselves what it means to be a unit in a ring and then
  prove that the units of a ring form a group.
  Hint: I recommend that you first prove that the product of two units is again a unit,
  and that you define the inverse of a unit separately using `Exists.choose`.
  Hint 2: to prove associativity, use something like `intros; ext; apply mul_assoc`
  (`rw` doesn't work well because of the casts) -/

#check Exists.choose
#check Exists.choose_spec
def IsAUnit (x : R) : Prop := ∃ y, y * x = 1


lemma unit_of_prod_unit (a b : {x : R // IsAUnit x}) : IsAUnit (a.1 * b.1) := by
  obtain ⟨a_inv, ha⟩ := a.2
  obtain ⟨b_inv, hb⟩ := b.2
  use b_inv * a_inv
  rw [mul_assoc, ← mul_assoc a_inv, ha, one_mul, hb]

def mul (x y : {x : R // IsAUnit x}) : {x : R // IsAUnit x} := ⟨x * y, unit_of_prod_unit x y⟩

lemma one_unit : IsAUnit (1 : R) := by
  use 1
  exact one_mul 1

def one : {x : R // IsAUnit x} := ⟨1, one_unit⟩

lemma one_mul' : ∀ a : {x : R // IsAUnit x}, mul one a = a := by
  intro a
  ext
  calc (mul one a).1
    _ = 1 * a.1 := by rfl
    _             = a.1     := by exact one_mul a.1

lemma mul_one' : ∀ a : {x : R // IsAUnit x}, mul a one = a := by
  intro a
  ext
  rw [← mul_one a.1]
  rfl



def inv (x : {x : R // IsAUnit x}) : {x : R // IsAUnit x} :=
  ⟨Exists.choose x.2, by
    use x.1
    rw [mul_comm, Exists.choose_spec x.2]
  ⟩

lemma mul_left_inv' : ∀  a : {x : R // IsAUnit x}, mul (inv a) a = one := by
  intro a
  ext
  calc (mul (inv a) a).1
    _ = (Exists.choose a.2) * a.1 := by rfl
    _ = 1                         := by rw [Exists.choose_spec a.2]

instance exercise5_2 : Group {x : R // IsAUnit x} where
  mul x y := mul x y
  mul_assoc := by
    intros
    ext
    apply mul_assoc
  one := one
  one_mul := one_mul'
  mul_one := mul_one'
  inv := inv
  mul_left_inv := mul_left_inv'

-- you have the correct group structure if this is true by `rfl`
example (x y : {x : R // IsAUnit x}) : (↑(x * y) : R) = ↑x * ↑y := by rfl

end Ring



/- The Frobenius morphism in a field of characteristic p is the map `x ↦ x ^ p`.
Let's prove that the Frobenius morphism is additive, without using that
fact from the library. -/
#check CharP.cast_eq_zero_iff
#check Finset.sum_congr
variable (p : ℕ) [hp : Fact p.Prime] (K : Type*) [Field K] [CharP K p] in
open Nat Finset in
lemma exercise5_3 (x y : K) : (x + y) ^ p = x ^ p + y ^ p := by
  rw [add_pow]
  have h2 : p.Prime := hp.out
  have h3 : 0 < p := h2.pos
  have h4 : range p = insert 0 (Ioo 0 p)
  · ext (_|_) <;> simp [h3]
  have h5 : ∀ i ∈ Ioo 0 p, p ∣ Nat.choose p i := by
    intro i hi
    simp at hi
    refine Prime.dvd_choose_self h2 ?hk hi.2
    · symm
      exact Nat.ne_of_lt hi.1
  have h' : ∀ i ∈  Ioo 0 p, x ^ i * y ^ (p - i) * Nat.choose p i = x ^ i * y ^ (p - i) * 0 := by
    intro i hi
    have : (Nat.choose p i : K) = 0 := by
      rw [CharP.cast_eq_zero_iff K p]
      exact h5 i hi
    rw [this]
  have h6 : ∑ i in Ioo 0 p, x ^ i * y ^ (p - i) * Nat.choose p i = 0 :=
    calc
      _ = ∑ i in Ioo 0 p, x ^ i * y ^ (p - i) * 0 := by rw [Finset.sum_congr rfl h']
      _ = ∑ i in Ioo 0 p, 0                       := by ring
      _ = 0 := by exact sum_const_zero

  calc ∑ m in range (p + 1), x ^ m * y ^ (p - m) * Nat.choose p m
    _ = (∑ m in range p, x ^ m * y ^ (p - m) * Nat.choose p m) + x ^ p * y ^ (p - p) * Nat.choose p p := by rw [sum_range_succ]
    _ = (∑ m in range p, x ^ m * y ^ (p - m) * Nat.choose p m) + x ^ p * y ^ 0 * Nat.choose p p := by rw [tsub_self]
    _ = (∑ m in range p, x ^ m * y ^ (p - m) * Nat.choose p m) + x ^ p * 1 * Nat.choose p p := by rw [_root_.pow_zero]
    _ = (∑ m in range p, x ^ m * y ^ (p - m) * Nat.choose p m) + x ^ p * Nat.choose p p := by rw [mul_one]
    _ = (∑ m in range p, x ^ m * y ^ (p - m) * Nat.choose p m) + x ^ p * (1 : ℕ) := by rw [Nat.choose_self]
    _ = (∑ m in range p, x ^ m * y ^ (p - m) * Nat.choose p m) + x ^ p * 1 := by simp
    _ = (∑ m in range p, x ^ m * y ^ (p - m) * Nat.choose p m) + x ^ p := by rw [mul_one]
    _ = (∑ m in insert 0 (Ioo 0 p), x ^ m * y ^ (p-m) * Nat.choose p m) + x ^ p := by rw [h4]
    _ = x ^ 0 * y ^ (p - 0) * Nat.choose p 0 + ∑ m in Ioo 0 p, x ^ m * y ^ (p - m) * Nat.choose p m + x ^ p := by rw [Finset.sum_insert left_not_mem_Ioo]
    _ = x ^ 0 * y ^ (p - 0) * Nat.choose p 0 + 0 + x ^ p := by rw [h6]
    _ = 1 * y ^ p * Nat.choose p 0 + x ^ p := by simp
    _ = y ^ p * Nat.choose p 0 + x ^ p := by simp
    _ = y ^ p * (1 : ℕ) + x ^ p := by rw [Nat.choose_zero_right p]
    _ = y ^ p + x ^ p := by simp
    _ = x ^ p + y ^ p := by rw [add_comm]

/- Let's prove that if `M →ₗ[R] M` forms a module over `R`, then `R` must be a commutative ring.
  To prove this we have to additionally assume that `M` contains at least two elements, and
`smul_eq_zero : r • x = 0 ↔ r = 0 ∨ x = 0` (this is given by the `NoZeroSMulDivisors` class).
-/
#check exists_ne
#check exists_pair_ne

lemma exercise5_4 {R M M' : Type*} [Ring R] [AddCommGroup M] [Module R M] [Nontrivial M]
    [NoZeroSMulDivisors R M] [Module R (M →ₗ[R] M)]
    (h : ∀ (r : R) (f : M →ₗ[R] M) (x : M), (r • f) x = r • f x)
    (r s : R) : r * s = s * r := by
  have ignore (f : M →ₗ[R] M) (h : f ≠ 0) : ∃ m : M, f m ≠ 0 := by
    by_contra hyp
    push_neg at hyp
    apply h
    ext x
    rw [hyp]
    simp



  have (f : M →ₗ[R] M) (r : R) (h' : r • f = 0): r = 0 ∨ f = 0 := by
    by_contra hyp
    push_neg at hyp
    obtain ⟨m, hm⟩ := ignore f hyp.2
    have m_ne_z : m ≠ 0 := by
      by_contra tt
      apply hm
      rw [tt]
      exact LinearMap.map_zero f
    have rfmez : r • (f m) = 0 := by
      rw [← h, h']
      rfl
    have rezofmez : r = 0 ∨ f m = 0 := by
      exact smul_eq_zero.mp rfmez
    obtain hr | hfm := rezofmez
    · exact hyp.1 hr
    · exact hm hfm
  let ι : (M →ₗ[R] M) := LinearMap.id
  obtain ⟨m, hm⟩ := exists_ne (0 : M)
  have fnez : ι ≠ 0 := by
    intro hι
    apply hm
    calc m
      _ = ι.toFun m := by rfl
      _ = (0 : M →ₗ[R] M).toFun m := by rw [hι]
      _ = (0 : M) := by rfl
  sorry
