import LeanCourse.Common
import LeanCourse.MIL.C03_Logic.solutions.Solutions_S06_Sequences_and_Convergence
set_option linter.unusedVariables false
open Nat Real Function Set

/-
* From Mathematics in Lean https://leanprover-community.github.io/mathematics_in_lean
  Read chapter 3, sections 3 and 6
  Read chapter 4, all sections.

* Do the exercises corresponding to these sections in the `LeanCourse/MIL` folder.
  Feel free to skip exercises if you are confident that you can do them.
  There are solutions in the solution folder in case you get stuck.

* Hand in the solutions to the exercises below. Deadline: 3.11.2023.

* When you hand in your solution, make sure that the file compiles!
  If you didn't manage to complete a particular exercise, make sure that the proof still compiles,
  by replacing the proof (or part of the proof) by `sorry`.
-/


/- Prove the law of excluded middle without using `by_cases` or lemmas from the library.
You will need to use `by_contra` in the proof. -/
lemma exercise3_1 (p : Prop) : p ∨ ¬ p := by
  by_contra h
  have hp : ¬p := by
    by_contra h'
    apply h
    left
    exact h'
  apply h
  right
  exact hp








/- ## Converging sequences

In the next few exercises, you prove more lemmas about converging sequences. -/

/-- From the lecture, the sequence `u` of real numbers converges to `l`. -/
def SequentialLimit (u : ℕ → ℝ) (l : ℝ) : Prop :=
  ∀ ε > 0, ∃ N, ∀ n ≥ N, |u n - l| < ε

/- Let's prove that reindexing a convergent sequence
by a reindexing function that tends to infinity
produces a sequence that converges to the same value. -/
lemma exercise3_2 {s : ℕ → ℝ} {r : ℕ → ℕ} {a : ℝ}
    (hs : SequentialLimit s a) (hr : ∀ m : ℕ, ∃ N : ℕ, ∀ n ≥ N, r n ≥ m) :
    SequentialLimit (s ∘ r) a := by
    intro ε hε
    specialize hs ε hε
    obtain ⟨m, hm⟩ := hs
    specialize hr m
    obtain ⟨N, hN⟩ := hr
    use N
    intro n hn
    specialize hN n hn
    specialize hm (r n) hN
    simp
    exact hm


/- Let's prove the squeeze theorem for sequences.
You will want to use the lemma in the library that states
`|a| < b ↔ -b < a ∧ a < b`. -/
lemma exercise3_3 {s₁ s₂ s₃ : ℕ → ℝ} {a : ℝ}
    (hs₁ : SequentialLimit s₁ a) (hs₃ : SequentialLimit s₃ a)
    (hs₁s₂ : ∀ n, s₁ n ≤ s₂ n) (hs₂s₃ : ∀ n, s₂ n ≤ s₃ n) :
    SequentialLimit s₂ a := by
    intro ε hε
    have hε' : ε/2 > 0 := by linarith
    specialize hs₁ ε hε
    specialize hs₃ ε hε
    obtain ⟨N₁, hN₁⟩ := hs₁
    obtain ⟨N₃, hN₃⟩ := hs₃
    let N := max N₁ N₃
    use N
    intro n hn
    have this : n ≥ N₁ := by exact le_of_max_le_left hn
    specialize hN₁ n this
    have that : n ≥ N₃ := by exact le_of_max_le_right hn
    specialize hN₃ n that
    apply abs_lt.mpr
    constructor
    · specialize hs₁s₂ n
      calc
        -ε < s₁ n - a := by exact neg_lt_of_abs_lt hN₁
        _  ≤ s₂ n - a := by linarith
    · specialize hs₂s₃ n
      calc
        s₂ n - a ≤ s₃ n - a := by exact sub_le_sub_right hs₂s₃ a
        _        < ε        := by exact lt_of_abs_lt hN₃



/- Let's prove that the sequence `n ↦ 1 / (n+1)` converges to `0`.
  It will be useful to know that if `x : ℝ` then `⌈x⌉₊ : ℕ` is `x` rounded up
  (in fact, it's rounded up to 0 if `x ≤ 0`). You will need some lemmas from the library, and `simp`
  will be useful to simplify.
  In the goal you will see `↑n`. This is the number `n : ℕ` interpreted as a real number `↑n : ℝ`.
  To type this number yourself, you have to write `(n : ℝ)`.
-/
#check ⌈π⌉₊
#check fun n : ℕ ↦ (n : ℝ)


--TODO: clean up this mess
lemma exercise3_4 : SequentialLimit (fun n ↦ 1 / (n+1)) 0 := by
  intro ε hε
  let N := ⌈1/ε⌉₊
  have hN: (N : ℝ) ≥ 1/ε := by exact le_ceil (1 / ε)
  use N
  intro n hn
  simp
  --have : ((n : ℝ) + 1)⁻¹ >   0 := by exact inv_pos_of_nat
  have that : ((n : ℝ) + 1)⁻¹ ≥ 0 := by
    apply le_of_lt
    exact inv_pos_of_nat
  rw [abs_eq_self.mpr that]
  have this : (n : ℝ) + 1 > 0 := by exact cast_add_one_pos n
  rw [inv_lt this hε]

  have : (n : ℝ) ≥ N := by exact cast_le.mpr hn

  calc
    (n : ℝ) + 1 = n + 1 := by simp
    _           ≥ N + 1:= by linarith
    _           ≥ 1/ε + 1:= by linarith
    _           > 1/ε := by linarith
    _           = ε⁻¹ := by simp



/- Use the previous exercises to prove that `n ↦ sin n / (n + 1)` converges to 0.
  I will prove for you that `n ↦ -1 / (n + 1)` also converges to `0`. -/

theorem convergesTo_mul_const {s : ℕ → ℝ} {a : ℝ} (c : ℝ) (hs : SequentialLimit s a) :
    SequentialLimit (fun n ↦ c * s n) (c * a) := by
  intro ε hε
  obtain ⟨N, hN⟩ := hs (ε / max |c| 1) (by positivity)
  use N
  intro n hn
  specialize hN n hn
  simp
  calc |c * s n - c * a|
      = |c * (s n - a)| := by ring
    _ = |c| * |s n - a| := by exact abs_mul c (s n - a)
    _ ≤ max |c| 1 * |s n - a| := by gcongr; exact le_max_left |c| 1
    _ < max |c| 1 * (ε / max |c| 1) := by gcongr
    _ = ε := by refine mul_div_cancel' ε ?hb; positivity

lemma use_me : SequentialLimit (fun n ↦ (-1) / (n+1)) 0 := by
  have : SequentialLimit (fun n ↦ (-1) * (1 / (n+1))) (-1 * 0) :=
    convergesTo_mul_const (-1) exercise3_4
  simp at this
  simp [neg_div, this]

lemma exercise3_5 : SequentialLimit (fun n ↦ sin n / (n+1)) 0 := by
  let s₁ := (fun n ↦ 1 / (n+1))
  let s₃ := (fun n ↦ (-1) / (n+1))
  apply (exercise3_3 use_me exercise3_4)
  · intro n
    have hn: (n : ℝ) + 1 > 0 := by exact cast_add_one_pos n
    apply (div_le_div_right hn).mpr ?hs₁s₂.a
    exact neg_one_le_sin ↑n
  · intro n
    have hn: (n : ℝ) + 1 > 0 := by exact cast_add_one_pos n
    apply (div_le_div_right hn).mpr ?hs₂s₃.a
    exact sin_le_one ↑n


/- Now let's prove that if a convergent sequence is nondecreasing, then it must stay below the
limit. -/
def NondecreasingSequence (u : ℕ → ℝ) : Prop :=
  ∀ n m, n ≤ m → u n ≤ u m

lemma exercise3_6 (u : ℕ → ℝ) (l : ℝ) (h1 : SequentialLimit u l) (h2 : NondecreasingSequence u) :
    ∀ n, u n ≤ l := by
    by_contra h
    push_neg at h
    obtain ⟨n, hn⟩ := h
    let ε := u n - l
    have hε : ε > 0 := by exact sub_pos.mpr hn
    specialize h1 ε hε
    obtain ⟨N, hN⟩ := h1
    let N' := max N n
    specialize hN N' (Nat.le_max_left N n)
    have hN' : u n ≤ u N' := by
      apply h2
      exact Nat.le_max_right N n
    have hN'' : u N' - l > 0 := by linarith
    have      : |u N' - l| ≥ ε := by
      calc
        |u N' - l| = u N' - l       := by exact abs_of_pos hN''
        _          ≥ u n  - l       := by exact sub_le_sub_right hN' l
    --    _          = ε              := by rfl
    --have : ¬|u N' - l| < ε := by exact not_lt.mpr this
    exact not_lt.mpr this hN





/- ## Sets

In the next few exercises, you prove more lemmas about converging sequences. -/


lemma exercise3_7 {α β : Type*} (f : α → β) (s : Set α) (t : Set β) :
    f '' s ∩ t = f '' (s ∩ f ⁻¹' t) := by
    ext y
    constructor
    · intro hy
      obtain ⟨x, hx₁⟩ := hy.1
      have hx₂ : x ∈ f ⁻¹' t := by
        simp
        rw [hx₁.2]
        exact hy.2
      use x
      exact ⟨⟨hx₁.1, hx₂⟩, hx₁.2⟩
    · intro hy
      obtain ⟨x, hx⟩ := hy
      constructor
      · use x
        exact ⟨hx.1.1, hx.2⟩
      · rw [←hx.2]
        exact hx.1.2


lemma exercise3_8 :
    (fun x : ℝ ↦ x ^ 2) ⁻¹' {y | y ≥ 4} = { x : ℝ | x ≤ -2 } ∪ { x : ℝ | x ≥ 2 } := by
    have h2   : (0 : ℝ) ≤ 2 := by linarith
    have h2'  : (2 : ℝ) ≤ 2 := by linarith  -- some very important and complicated lemmas
    have h2'' : (0 : ℝ) < 2 := by linarith
    ext x
    simp
    rw [← le_abs']
    rw [← sq_abs x]
    constructor
    · intro hx
      by_contra hx'
      apply not_lt_of_le hx
      let hx'' := lt_of_not_le hx'
      by_cases hor : |x| = 0
      · calc
          |x| ^ 2 = 0 ^ 2 := by rw [hor]
          _       = 0     := by ring
          _       < 4     := by linarith
      · have hor' : 0 < |x| := by
          apply lt_of_le_of_ne' ?_ hor
          exact abs_nonneg x
        calc
          |x| ^ 2 = |x| * |x|            := by rw [sq]
          _       <   2 * |x|            := by refine mul_lt_mul_of_pos_right hx'' hor'
          _       <   2 * 2              := by refine mul_lt_mul_of_pos_of_nonneg h2' hx'' h2'' h2
          _       =     4                := by ring
    · intro hx
      calc
        4 = 2 * 2     := by ring
        _ ≤ 2 * |x|   := by apply OrderedSemiring.mul_le_mul_of_nonneg_left 2 |x| 2 hx h2
        _ ≤ |x| * |x| := by refine mul_le_mul_of_nonneg_right hx (abs_nonneg x)
        _ = |x| ^ 2   := by rw [sq]





/- As mentioned in exercise 2, `α × β` is the cartesian product of the types `α` and `β`.
Elements of the cartesian product are denoted `(a, b)`, and the projections are `.1` and `.2`.
As an example, here are two ways to state when two elements of the cartesian product are equal. -/

variable {α β γ : Type*}
example (a a' : α) (b b' : β) : (a, b) = (a', b') ↔ a = a' ∧ b = b' := Prod.ext_iff
example (x y : α × β) : x = y ↔ x.1 = y.1 ∧ x.2 = y.2 := Prod.ext_iff

/- Hard exercise: Let's prove that if `f : α → γ` and `g : β → γ` are injective function whose
  ranges partition `γ`, then `Set α × Set β` is in bijective correspondence to `Set γ`.

  To help you along the way, some ways to reformulate the hypothesis are given,
  which might be more useful than the stated hypotheses.
  Remember: you can use `simp [hyp]` to simplify using hypothesis `hyp`. -/
lemma exercise3_9 {f : α → γ} {g : β → γ} (hf : Injective f) (hg : Injective g)
    (h1 : range f ∩ range g = ∅) (h2 : range f ∪ range g = univ) :
    ∃ (L : Set α × Set β → Set γ) (R : Set γ → Set α × Set β), L ∘ R = id ∧ R ∘ L = id := by
  have h1' : ∀ x y, f x ≠ g y
  · intro x y h
    apply h1.subset
    exact ⟨⟨x, h⟩, ⟨y, rfl⟩⟩
  have h1'' : ∀ y x, g y ≠ f x
  · intro x y
    symm
    apply h1'
  have h2' : ∀ x, x ∈ range f ∪ range g := eq_univ_iff_forall.1 h2
  have hf' : ∀ x x', f x = f x' ↔ x = x' := fun x x' ↦ hf.eq_iff
  let L : Set α × Set β → Set γ :=
    fun (s, t) ↦ f '' s ∪ g '' t
  let R : Set γ → Set α × Set β :=
    fun s ↦ (f ⁻¹' s, g ⁻¹' s)
  use L, R
  constructor
  · ext s a
    simp
    constructor
    · intro ha
      simp at ha
      obtain ha' | ha'' := ha
      · obtain ⟨x, hx⟩ := ha'
        rw [hx.2] at hx
        exact hx.1
      · obtain ⟨x, hx⟩ := ha''
        rw [hx.2] at hx
        exact hx.1
    · intro ha
      obtain ha' | ha'' := h2' a
      · left
        obtain ⟨x, hx⟩ := ha'
        use x
        rw [hx]
        exact ⟨ha, rfl⟩
      · right
        obtain ⟨x, hx⟩ := ha''
        use x
        rw [hx]
        exact ⟨ha, rfl⟩
  · ext ⟨s, t⟩ a
    simp
    constructor
    · intro ha
      obtain ha' | ha'' := ha
      · obtain ⟨b, hb⟩ := ha'
        have hab : a = b := by
          apply hf
          rw [hb.2]
        rw [hab]
        exact hb.1
      · obtain ⟨b, hb⟩ := ha''
        by_contra
        apply h1'' b a
        exact hb.2
    · intro ha
      left
      use a
    · constructor
      · simp
        intro ha
        obtain ha' | ha'' := ha
        · obtain ⟨b, hb⟩ := ha'
          by_contra
          apply h1' b a
          exact hb.2
        · obtain ⟨b, hb⟩ := ha''
          have hab : a = b := by
            apply hg
            rw [hb.2]
          rw [hab]
          exact hb.1
      · simp
        intro ha
        right
        use a
