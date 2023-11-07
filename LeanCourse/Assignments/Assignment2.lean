import LeanCourse.Common
set_option linter.unusedVariables false
open Nat

/-

* From Mathematics in Lean https://leanprover-community.github.io/mathematics_in_lean
  Read chapter 2, sections 3, 4 and 5
  Read chapter 3, sections 1, 2, 4, 5.

* Do the exercises corresponding to these sections in the `LeanCourse/MIL` folder.
  There are solutions in the solution folder in case you get stuck.

* Hand in the solutions to the exercises below. Deadline: 27.10.2023.

* When you hand in your solution, make sure that the file compiles!
  If you didn't manage to complete a particular exercise, make sure that the proof still compiles,
  by replacing the proof (or part of the proof) by `sorry`.
-/

lemma exercise2_1 {α : Type*} {p q : α → Prop} :
    (∃ x, p x ∨ q x) ↔ (∃ x, p x) ∨ (∃ x, q x) := by
  constructor
  · intro h1
    rcases h1 with ⟨a, ha⟩
    rcases ha with ha' | ha''
    · left
      use a
    right
    use a
  intro h1
  rcases h1 with h1' | h1''
  · rcases h1' with ⟨a, ha⟩
    use a
    left
    exact ha
  rcases h1'' with ⟨a, ha⟩
  use a
  right
  exact ha

section Surjectivity

/- Lean's mathematical library knows what a surjective function is, but let's define it here
ourselves and prove some things about it. -/
def SurjectiveFunction (f : ℝ → ℝ) : Prop :=
  ∀ (y : ℝ), ∃ (x : ℝ), f x = y

variable {f g : ℝ → ℝ} {x : ℝ}

/- `rfl` or `simp` can compute the following.
  `simp` is a very useful tactic that can simplify many expressions. -/
example : (g ∘ f) x = g (f x) := by simp

lemma exercise2_2 (h : SurjectiveFunction (g ∘ f)) : SurjectiveFunction g := by
  intro z
  rcases h z with ⟨x, hx⟩
  use f x
  exact hx

/- Hint: you are allowed to use the previous exercise in this exercise! -/
lemma exercise2_3 (hf : SurjectiveFunction f) :
    SurjectiveFunction (g ∘ f) ↔ SurjectiveFunction g := by
  constructor
  · exact exercise2_2
  intro hg z
  rcases hg z with ⟨y, hy⟩
  rcases hf y with ⟨x, hx⟩
  use x
  simp
  rw [hx, hy]

/- Composing a surjective function by a linear function to the left and the right will still result
in a surjective function. The `ring` tactic will be very useful here! -/
lemma exercise2_4 (hf : SurjectiveFunction f) :
    SurjectiveFunction (fun x ↦ 2 * f (3 * (x + 4)) + 1) := by
  intro y
  rcases hf (y/2 - 1/2) with ⟨x', hx'⟩
  use x'/3 - 4
  -- have h1 : (fun x => 2 * f (3 * (x + 4)) + 1) ((x' - 1) / 3 - 4) = 2 * f (3 * (((x'- 1)/3 - 4) + 4) + 1)  := by
  -- have h2 : 2 * f (3 * (((x'- 1)/3 - 4) + 4) + 1) = y := by
  ring
  rw [hx']
  ring

end Surjectivity





section Growth

/- Given two sequences of natural numbers `s` and `t`. We say that `s` eventually grows faster than
  `t` if for all `k : ℕ`, `s_n` will be at least as large as `k * t_n` for large enough `n`. -/
def EventuallyGrowsFaster (s t : ℕ → ℕ) : Prop :=
  ∀ k : ℕ, ∃ N : ℕ, ∀ n ≥ N, k * t n ≤ s n

variable {s t : ℕ → ℕ} {k : ℕ}

/- Hint: `simp` can help you simplify expressions like the following.
  Furthermore, `gcongr` will be helpful! -/
example : (fun n ↦ n * s n) k = k * s k := by simp

lemma exercise2_5 : EventuallyGrowsFaster (fun n ↦ n * s n) s := by
  intro k
  use k
  intro n hn
  simp
  apply mul_le_mul
  · exact hn
  · exact le_refl s n
  · exact Nat.zero_le (s n)
  exact Nat.zero_le n

/- For the following exercise, it will be useful to know that you can write `max a b`
  to take the maximum of `a` and `b`, and that this lemma holds  -/
lemma useful_fact (a b c : ℕ) : c ≥ max a b ↔ c ≥ a ∧ c ≥ b := by simp

lemma exercise2_6 {s₁ s₂ t₁ t₂ : ℕ → ℕ}
    (h₁ : EventuallyGrowsFaster s₁ t₁) (h₂ : EventuallyGrowsFaster s₂ t₂) :
    EventuallyGrowsFaster (s₁ + s₂) (t₁ + t₂) := by
  intro k
  rcases h₁ k with ⟨N₁, hn₁⟩
  rcases h₂ k with ⟨N₂, hn₂⟩
  use max N₁ N₂
  intro n hn
  simp
  rw [mul_add]
  apply Nat.add_le_add
  · exact hn₁ n ((useful_fact N₁ N₂ n).mp hn).left
  exact hn₂ n ((useful_fact N₁ N₂ n).mp hn).right


/- Optional hard exercise 1:
Find a function that is nowhere zero and grows faster than itself when shifted by one. -/
lemma exercise2_7 : ∃ (s : ℕ → ℕ), EventuallyGrowsFaster (fun n ↦ s (n+1)) s ∧ ∀ n, s n ≠ 0 := by
  use (fun n => n^n)
  constructor
  · intro k
    use k
    intro n hn
    simp
    have h : n ≤ n + 1 := by linarith
    calc
      k * n ^ n ≤ n * n ^ n := by apply mul_le_mul hn (le_refl (n^n)) (Nat.zero_le (n^n)) (Nat.zero_le n)
                                        -- I prefer this to proving k ≤ n somewhere else
      _         = n^(n + 1) := by ring
      _          ≤ (n + 1)^(n + 1) := by apply Nat.pow_le_pow_of_le_left h
  · intro n
    by_cases n = 0 -- this is ugly, I would prefer to do this "case distinction" by induction, but didnt get it to work
    · calc
        n^n = 0^0 := by rw [h]
        _   = 1   := by ring
      exact one_ne_zero
    · have h6 : n^n ≥ 1 := by
        calc
          n^n ≥ n^0 := by apply Nat.pow_le_pow_of_le_right (Nat.pos_of_ne_zero h) (Nat.zero_le n)
          _   = 1   := by rw [@pow_eq_one_iff_modEq]
      intro
      linarith


/- Optional hard exercise 2:
Show that a function that satisfies the conditions of the last
exercise, then it must necessarily tend to infinity.
The following fact will be useful. Also, the first step of the proof is already given. -/


--expanded the exact?s for aesthetics
lemma useful_fact2 {n m : ℕ} (hn : n ≥ m + 1) : ∃ k ≥ m, k + 1 = n := by
  use n - 1
  constructor
  · exact le_pred_of_lt hn
  · have : 1 ≤ n := by exact one_le_of_lt hn
    exact Nat.sub_add_cancel this

lemma exercise2_8 (hs : EventuallyGrowsFaster (fun n ↦ s (n+1)) s) (h2s : ∀ n, s n ≠ 0) :
  ∀ k : ℕ, ∃ N : ℕ, ∀ n ≥ N, s n ≥ k := by
  have h3s : ∀ n, 1 ≤ s n := by
    intro n
    exact one_le_iff_ne_zero.mpr (h2s n)
  intro k
  obtain ⟨N, hN⟩ := hs k
  use N + 1
  intro n hn

  obtain ⟨l, hl⟩ := useful_fact2 hn
  specialize hN l hl.left
  calc
    s n = s (l + 1)                 := by rw [hl.right]
    _   = (fun n => s (n + 1)) l    := by simp
    _   ≥ k * (s l)                 := by apply hN
    _   ≥ k * 1                     := by exact Nat.mul_le_mul_left k (h3s l)
    _   = k                         := by ring




end Growth
