import Mathlib.SetTheory.Cardinal.Basic

open Cardinal

def abcd    {X : Type*} (ν : Cardinal) (A : Set X) : Set (Set X) := {Y | # Y = ν ∧ Y ⊆ A} --TODO: rename this

def abcd_le {X : Type*} (ν : Cardinal) (A : Set X) : Set (Set X) := {Y | # Y ≤ ν ∧ Y ⊆ A}

def abcd_lt {X : Type*} (ν : Cardinal) (A : Set X) : Set (Set X) := {Y | # Y < ν ∧ Y ⊆ A}

@[simp] lemma abcd_monotone {X : Type*} {ν : Cardinal} {A B: Set X} (hA : A ⊆ B) : abcd ν A ⊆ abcd ν B := by
  intro Y hY
  constructor
  · exact hY.1
  · calc
      Y ⊆ A  := hY.2
      A ⊆ B := hA

@[simp] lemma abcd_monotone' {X : Type*} {ν : Cardinal} {B C Y: Set X} (hB : Y ⊆ B) (hY : Y ∈ abcd ν C) :
  Y ∈ abcd ν B := ⟨hY.1, hB⟩

#print abcd

#check Fin 2

def coloring {X : Type*} (n : ℕ) (μ : Type*) (A : Set X) := (abcd n A) → μ

#print coloring

example {X : Type*} (A A' : Set X) : A ∩ A' ⊆ A := by exact Set.inter_subset_left A A'

def homogeneous_of_color {X μ : Type*} {n : ℕ} {A : Set X}  (c : coloring n μ A) (H : Set X) (i : μ): Prop :=
  ∀ Y : abcd n A, Y.1 ⊆ H →  c Y  = i

def homogeneous {X μ : Type*} {n : ℕ} {A : Set X} (c : coloring n μ A) (H : Set X): Prop :=
  ∃ i : μ, homogeneous_of_color c H i

def arrows {X : Type*} (κ : Cardinal) (n : ℕ) (A : Set X) (μ : Type*): Prop :=
  ∀ (c : coloring n μ A), ∃ H : Set X, (H ⊆ A) ∧ # H = κ ∧ homogeneous c H
/-
lemma nice_iso_left {X X' : Type u1} {μ : Type*} (κ : Cardinal) (n : ℕ) (A : Set X) (A' : Set X') (f : X → X') (hf : f.Bijective)
  (h : arrows κ n A μ) : arrows κ n A' μ := by sorry
-/


lemma monotone_left {X μ: Type*} {n : ℕ} {A A' : Set X} {κ : Cardinal} (hA : A ⊆ A') :
    arrows κ n A μ → arrows κ n A' μ := by
  intro h c'

  let c (Y : abcd n A) := c' ⟨Y.1, abcd_monotone hA Y.2⟩


  obtain ⟨H, hH⟩ := h c

  use H

  constructor
  · calc
      H ⊆ A  := hH.1
      A ⊆ A' := hA
  · constructor
    · exact hH.2.1
    · obtain ⟨i, hi⟩ := hH.2.2
      use i
      intro Y hY
      calc c' Y
        _ = c ⟨Y.1, abcd_monotone hH.1 $ abcd_monotone' hY Y.2⟩ := by rfl
        _ = i := by exact hi ⟨Y.1, abcd_monotone hH.1 $ abcd_monotone' hY Y.2⟩ hY

lemma monotone_card {X μ : Type*} {n : ℕ} {A : Set X} {κ κ' : Cardinal} (hκ : κ' ≤ κ) :
  arrows κ n A μ → arrows κ' n A μ := by
  intro h c

  obtain ⟨H, hH⟩ := h c

  have : ∃ H' : Set X, H' ⊆ H ∧ # H' = κ' := by
    rw [← hH.2.1] at hκ
    let H'' := Exists.choose $ le_mk_iff_exists_set.mp hκ
    have hH'' := Exists.choose_spec $ le_mk_iff_exists_set.mp hκ
    let H' : Set X := Subtype.val '' H''--{x : X | ∃ y : H, y ∈ H'' ∧ x = y.1}--Subtype.val '' H''
    use H'
    constructor
    · intro x hx
      obtain ⟨y, hy⟩ := hx
      rw [← hy.2]
      exact y.2
    · rw [mk_image_eq Subtype.coe_injective]
      exact hH''

  obtain ⟨H', hH'⟩ := this
  use H'

  have hH'A : H' ⊆ A := by calc
      H' ⊆ H := hH'.1
      _  ⊆ A := hH.1

  constructor
  · exact hH'A
  · constructor
    · exact hH'.2
    · obtain ⟨i, hi⟩ := hH.2.2
      use i
      intro Y hY

      have : Y.1 ⊆ H := by
        calc
          Y.1 ⊆ H' := hY
          _   ⊆ H  := hH'.1

      exact hi Y this


-- lemma lemma_1_2 (A A' : Type u1) (κ κ' : Cardinal) (n : ℕ) (μ μ' : Type u2) (hA : # A ≤ # A') (hκ : κ' ≤ κ) (hμ : # μ' ≤ # μ) :
--     arrows A κ n μ → arrows A' κ' n μ' := by
--   intro h c
--   have : ∃ f : A → A', Function.Injective f := by sorry --this should follow from hA, but I cant find out how rn
--   obtain ⟨f, hf⟩ := this
--   have : ∃ g : μ' → μ, Function.Injective g := by sorry --see above, but with hμ
--   obtain ⟨g, hg⟩ := this

--   let F : abcd A n → abcd A' n := fun x ↦ ⟨f '' x, by
--     sorry⟩

--   have hF : F.Injective := by sorry

--   let c' (a : abcd A n) := g $ c $ F a
--   obtain ⟨H, hH⟩ := h c'

--   let H' := f '' H

--   use H'
--   constructor
--   · sorry
--   · sorry

/-
lemma lemma_1_3 (A : Type*) (κ : Cardinal) (n n' : ℕ) (μ: Type*) (hn : n' ≤ n) :
    arrows A κ n μ → arrows A κ n' μ := by
  intro h c'
  sorry
-/


lemma fuckinghellthisshouldbeeasy (x : Fin 2) (h : x ≠ 0) : x = 1 := by
  apply Fin.fin_two_eq_of_eq_zero_iff
  simp [h]

lemma nonempty_of_card_pos {A : Type*} (h : 1 ≤ # A) : Nonempty A := by
  have ⟨f, _⟩ := (Cardinal.le_def _ _).mp h

  use f 0


lemma todo2 {X : Type*} {A : Set X} (hA : # A = 1) : ∃ x : X, A = {x} := by
  have one_le_card : 1 ≤ # A := by exact Eq.le hA.symm
  have card_le_one : # A ≤ 1 := by exact Eq.le hA

  obtain ⟨x, hx⟩ := nonempty_of_card_pos one_le_card
  use x

  apply Set.Subsingleton.eq_singleton_of_mem
  · apply mk_le_one_iff_set_subsingleton.mp card_le_one
  · exact hx

lemma rathole_principle : arrows ℵ₀ 0 (Set.univ : Set ℕ) (Fin 2) := by
  intro c
  use Set.univ
  simp
  have : ∅ ∈ abcd 0 (Set.univ : Set ℕ):= by
    constructor
    · exact mk_emptyCollection ℕ
    · simp
  let i := c ⟨∅, this⟩
  use i
  intro Y _
  have : Y = ⟨(∅ : Set ℕ), this⟩ := by
    have hY := Y.2.1
    ext1
    exact mk_emptyCollection_iff.mp hY

  rw [this]


lemma pigeonhole_principle : arrows ℵ₀ 1 (Set.univ : Set ℕ) (Fin 2) := by
  intro c
  by_contra hyp
  push_neg at hyp

  have singleton_abcd (n : ℕ) : {n} ∈ abcd 1 (Set.univ : Set ℕ) := by exact ⟨mk_singleton n, Set.singleton_subset_iff.mpr trivial⟩

  let H (i : Fin 2) := {n : ℕ | c ⟨{n}, singleton_abcd n⟩ = i}

  have Hhom (i : Fin 2): homogeneous c $ H i := by
    use i
    intro Y hY
    --have : ∃ n : ℕ, {n} = Y.1 :=  --should follow from being singleton
    obtain ⟨n, hn⟩ := todo2 Y.2.1
    have : n ∈ H i := by
      rw [← @Set.singleton_subset_iff, ← hn]
      exact hY

    calc c Y
      _ = c ⟨{n}, singleton_abcd n⟩ := by rw [← Subtype.coe_eq_of_eq_mk hn]
      _ = i := this

  have that :  (Set.univ : Set ℕ) = H 0 ∪ H 1 := by
    ext n
    constructor
    · intro
      by_cases hyp : c ⟨{n}, singleton_abcd n⟩ = 0
      · left
        exact hyp
      · right
        exact fuckinghellthisshouldbeeasy (c ⟨{n}, singleton_abcd n⟩) hyp
    · intro
      exact trivial

  have Hfin (i : Fin 2) : # (H i) < ℵ₀ := by
    by_contra hH₀
    push_neg at hH₀

    have : # (H i) = ℵ₀ := by
      have : # (H i) ≤ ℵ₀ := by exact mk_le_aleph0
      exact le_antisymm  this hH₀

    exact hyp (H i) (Set.subset_univ (H i)) this (Hhom i)

  have : # ℕ < ℵ₀ := by
    calc # ℕ
      _ = # (Set.univ : Set ℕ) := by exact mk_univ.symm
      _ = # (H 0 ∪ H 1 : Set ℕ)  := by rw [that]
      _ ≤ # (H 0)  + # (H 1) := by exact mk_union_le (H 0) (H 1)
      _ < ℵ₀ := by exact add_lt_aleph0 (Hfin 0) (Hfin 1)

  exact LT.lt.ne this mk_nat

example (A : Set ℕ) : A ⊆ Set.univ := by exact Set.subset_univ A
/-
lemma ramsey_two (n : ℕ) : arrows ℵ₀ n (Set.univ : Set ℕ) (Fin 2) := by
  induction n
  case zero => exact rathole_principle
  case succ n hn =>
    intro c

    --have ih' (A : Set ℕ) : arrows ℵ₀ n A (Fin 2) := sorry -- monotone_left (Set.subset_univ A) hn

    have ih' (a : ℕ) (A : Set ℕ) : arrows ℵ₀ n (A \ {a}) (Fin 2) := by sorry

    let c' (a : ℕ) (A : Set ℕ) (Y : abcd n (A \ {a})) := c ⟨insert a Y.1, by
      constructor
      · have : a ∉ Y.1 := by
          intro hyp
          have := Y.2.2 hyp
          simp at this
        rw [Cardinal.mk_insert this, Y.2.1]
        norm_cast

      · exact Set.subset_univ (Set.insert a Y.1)
      ⟩

    let min' (A : Set ℕ) (hA : #A = ℵ₀) : ∃ a ∈ A, ∀ b ∈ A, a ≤ b := by
      sorry

    --let select (A : Set ℕ) (hA : # A = ℵ₀) : ∃ (B : Set ℕ)

    let rec seq : ∀ k : ℕ, ∃ (A : Set ℕ) /-(i : Fin 2)-/, # A = ℵ₀
      | 0    => ⟨(Set.univ : Set ℕ), by simp⟩
      | k + 1    => ⟨Exists.choose (ih' (Exists.choose $ min' (seq k).choose (seq k).choose_spec) (c' )), sorry⟩

    sorry
-/
