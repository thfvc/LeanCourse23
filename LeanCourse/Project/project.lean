import Mathlib.SetTheory.Cardinal.Basic

open Cardinal

def abcd    (X : Type*) (ν : Cardinal) : Set (Set X) := {Y | # Y = ν} --TODO: rename this

def abcd_le (X : Type*) (ν : Cardinal) : Set (Set X) := {Y | # Y ≤ ν}

def abcd_lt (X : Type*) (ν : Cardinal) : Set (Set X) := {Y | # Y < ν}

#print abcd

#check Fin 2

def coloring (X : Type*) (n : ℕ)  (μ : Type*) := (abcd X n) → μ

#print coloring

def homogenous_of_color {X μ : Type*} {n : ℕ}  (c : coloring X n μ) (H : Set X) (i : μ): Prop :=
  ∀ (A : Set X) (_ : A ⊆ H) (h2 : (# A = n)), c ⟨A, h2⟩  = i

def homogenous {X μ : Type*} {n : ℕ}  (c : coloring X n μ) (H : Set X) : Prop :=
  ∃ i : μ, homogenous_of_color c H i

def arrows (A : Type*) (κ : Cardinal) (n : ℕ) (μ : Type*): Prop :=
  ∀ (c : coloring A n μ), ∃ H : Set A , # H = κ ∧ homogenous c H

universe u1

universe u2

lemma lemma_1_2 (A A' : Type u1) (κ κ' : Cardinal) (n : ℕ) (μ μ' : Type u2) (hA : # A ≤ # A') (hκ : κ' ≤ κ) (hμ : # μ' ≤ # μ) :
    arrows A κ n μ → arrows A' κ' n μ' := by
  intro h c
  have : ∃ f : A → A', Function.Injective f := by sorry --this should follow from hA, but I cant find out how rn
  obtain ⟨f, hf⟩ := this
  have : ∃ g : μ' → μ, Function.Injective g := by sorry --see above, but with hμ
  obtain ⟨g, hg⟩ := this

  let F : abcd A n → abcd A' n := fun x ↦ ⟨f '' x, by
    sorry⟩

  have hF : F.Injective := by sorry

  let c' (a : abcd A n) := g $ c $ F a
  obtain ⟨H, hH⟩ := h c'

  let H' := f '' H

  use H'
  constructor
  · sorry
  · sorry

lemma lemma_1_3 (A : Type*) (κ : Cardinal) (n n' : ℕ) (μ: Type*) (hn : n' ≤ n) :
    arrows A κ n μ → arrows A κ n' μ := by
  intro h c'
  sorry
