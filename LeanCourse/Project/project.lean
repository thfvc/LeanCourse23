import Mathlib.SetTheory.Cardinal.Basic

open Cardinal
open Set

def abcd    (X : Type*) (ν : Cardinal) : Set (Set X) := {Y | # Y = ν} --TODO: rename this

/-
def abcd_le {X : Type*} (ν : Cardinal) (A : Set X) : Set (Set X) := {Y | # Y ≤ ν ∧ Y ⊆ A}

def abcd_lt {X : Type*} (ν : Cardinal) (A : Set X) : Set (Set X) := {Y | # Y < ν ∧ Y ⊆ A}
-/


lemma abcd_monotone {A' : Type*} {n : ℕ} {A : Set A'} (Y : abcd A n) : Subtype.val '' Y.1 ∈ abcd A' n := by
  have : # (Subtype.val '' Y.1) = # Y := mk_image_eq Subtype.coe_injective
  rw [Y.2] at this
  exact this

/-
@[simp] lemma abcd_monotone' {X : Type*} {ν : Cardinal} {B C Y: Set X} (hB : Y ⊆ B) (hY : Y ∈ abcd ν C) :
  Y ∈ abcd ν B := ⟨hY.1, hB⟩

-/
#print abcd

#check Fin 2

def coloring (X : Type*) (n : ℕ) (μ : Type*) := (abcd X n) → μ

#print coloring

example {X : Type*} (A A' : Set X) : A ∩ A' ⊆ A := by exact Set.inter_subset_left A A'

def homogeneous_of_color {X μ : Type*} {n : ℕ} (c : coloring X n μ) (H : Set X) (i : μ)  : Prop :=
  ∀ Y : abcd X n, Y.1 ⊆ H →  c Y  = i

def homogeneous {A B : Type*} {n : ℕ} (c : coloring A n B) (H : Set A) : Prop :=
  ∃ i : B, homogeneous_of_color c H i

def arrows_type (A : Type*) (κ : Cardinal) (n : ℕ) (B : Type*) : Prop :=
  ∀ (c : coloring A n B), ∃ H : Set A, # H = κ ∧ homogeneous c H

def arrows_card (lambda κ : Cardinal) (n : ℕ) (μ : Cardinal) : Prop :=
  ∀ (A B : Type*), # A = lambda → # B = μ → arrows_type A κ n B
/-
lemma nice_iso_left {X X' : Type u1} {μ : Type*} (κ : Cardinal) (n : ℕ) (A : Set X) (A' : Set X') (f : X → X') (hf : f.Bijective)
  (h : arrows κ n A μ) : arrows κ n A' μ := by sorry
-/


lemma monotone_left (lambda lambda' κ : Cardinal) (n : ℕ) (μ : Cardinal) (hlambda : lambda ≤ lambda') :
    arrows_card lambda κ n μ → arrows_card lambda' κ n μ := by
  intro h A' B hA' hB c'

  rw [← hA', le_mk_iff_exists_set] at hlambda

  obtain ⟨A, hA⟩ := hlambda

  let c (Y : abcd A n) : B := c' ⟨Subtype.val '' Y.1, abcd_monotone Y⟩

  obtain ⟨H, hH⟩ := h A B hA hB c

  let H' : Set A' := Subtype.val '' H

  use H'

  constructor
  · rw [← hH.1]
    exact mk_image_eq Subtype.coe_injective
  · obtain ⟨i, hi⟩ := hH.2
    use i
    intro Y' hY'
    let Y : Set A := Subtype.val ⁻¹' Y'
    have hY₁ : Y ∈ abcd A n := by
      rw [← Y'.2]
      apply mk_preimage_of_injective_of_subset_range
      · exact Subtype.coe_injective
      · intro y hy
        specialize hY' hy
        exact mem_range_of_mem_image Subtype.val H hY'
    have hY₂ : Y ⊆ H := by
      intro y hy
      obtain ⟨x, hx⟩ := hY' hy
      have : x = y := by
        ext
        exact hx.2
      rw [← this]
      exact hx.1
    have hY₃ : Y'.1 = Subtype.val '' Y := by
      ext y'
      constructor
      · intro hy'
        obtain ⟨y, hy⟩ := hY' hy'
        use y
        simp
        constructor
        · rw [hy.2]
          exact hy'
        · exact hy.2
      · intro hy'
        obtain ⟨y, hy⟩ := hy'
        rw [← hy.2]
        exact hy.1
    have hY'₂ : Subtype.val '' Y ∈ abcd A' n := by
      rw [← hY₃]
      exact Y'.2
    let Y'' : abcd A' n := ⟨Subtype.val '' Y, hY'₂⟩

    have : Y' = Y'' := by
      ext1
      exact hY₃

    rw [this]

    calc c' Y''
      _ = c ⟨Y, hY₁⟩ := by rfl
      _ = i := by exact hi { val := Y, property := hY₁ } hY₂



#check Cardinal.le_mk_iff_exists_subset

lemma monotone_card (lambda κ κ' : Cardinal) (n : ℕ) (μ : Cardinal) (hκ : κ' ≤ κ) :
    arrows_card lambda κ n μ → arrows_card lambda κ' n μ := by
  intro h A B hA hB

  specialize h A B hA hB

  intro c

  obtain ⟨H, hH⟩ := h c

  rw [← hH.1] at hκ
  obtain ⟨H', hH'⟩ := le_mk_iff_exists_subset.mp hκ
  use H'


  constructor
  · exact hH'.2
  · obtain ⟨i, hi⟩ := hH.2
    use i
    intro Y hY
    have : Y.1 ⊆ H := by
      calc Y.1
        _ ⊆ H' := hY
        _ ⊆ H  := hH'.1
    exact hi Y this

lemma monotone_right (lambda κ : Cardinal) (n : ℕ) (μ μ' : Cardinal) (hμ : μ' ≤ μ) :
    arrows_card lambda κ n μ → arrows_card lambda κ n μ' := by
  intro h A B' hA hB' c

  have : ∃ (B : Type u_2), # B = μ := CanLift.prf μ trivial

  obtain ⟨B, hB⟩ := this

  have : Nonempty (B' ↪ B) := by
    rw [← le_def, hB, hB']
    exact hμ

  obtain ⟨f, hf⟩ := this

  obtain ⟨H, hH⟩ := h A B hA hB (f ∘ c)

  use H

  constructor
  · exact hH.1
  · obtain ⟨i, hi⟩ := hH.2
    sorry -- TODO: figure out what to do if lambda = 0

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


lemma fin2_one_of_ne_two (x : Fin 2) (h : x ≠ 0) : x = 1 := by
  apply Fin.fin_two_eq_of_eq_zero_iff
  simp [h]

lemma nonempty_of_card_pos {A : Type*} (h : 1 ≤ # A) : Nonempty A := by
  apply mk_ne_zero_iff.mp
  exact one_le_iff_ne_zero.mp h


lemma singleton_of_card_one {X : Type*} {A : Set X} (hA : # A = 1) : ∃ x : X, A = {x} := by
  have one_le_card : 1 ≤ # A := by exact Eq.le hA.symm
  have card_le_one : # A ≤ 1 := by exact Eq.le hA

  obtain ⟨x, hx⟩ := nonempty_of_card_pos one_le_card
  use x

  apply Set.Subsingleton.eq_singleton_of_mem
  · apply mk_le_one_iff_set_subsingleton.mp card_le_one
  · exact hx

lemma rathole_principle : arrows_card ℵ₀ ℵ₀ 0 2 := by
  intro A B hA _ c
  use Set.univ
  simp
  constructor
  · exact hA
  · have : ∅ ∈ abcd A 0 := by exact mk_emptyCollection A
    let i := c ⟨∅, this⟩
    use i
    intro Y _

    have : Y = ⟨∅, this⟩ := by
      ext1
      rw [← mk_emptyCollection_iff]
      exact Y.2
    rw [this]

example (A : Set ℕ) : A ⊆ (univ : Set ℕ) := by exact subset_univ A

lemma pigeonhole_principle : arrows_card ℵ₀ ℵ₀ 1 2 := by
  intro A B hA hB

  intro c
  by_contra hyp
  push_neg at hyp

  have singleton_abcd (x : A) : {x} ∈ abcd A 1  := by
    rw [abcd]
    simp

  let H (i : B) := {x : A | c ⟨{x}, singleton_abcd x⟩ = i}

  have Hhom (i : B): homogeneous c $ H i := by
    use i
    intro Y hY
    obtain ⟨n, hn⟩ := singleton_of_card_one Y.2
    have : n ∈ H i := by
      rw [← @Set.singleton_subset_iff, ← hn]
      exact hY

    calc c Y
      _ = c ⟨{n}, singleton_abcd n⟩ := by rw [← Subtype.coe_eq_of_eq_mk hn]
      _ = i := this

  obtain ⟨x, y, hxy⟩ := mk_eq_two_iff.mp hB

  have that :  (Set.univ : Set A) = H x ∪ H y  := by
    ext a
    constructor
    · intro _
      simp
      have : c ⟨{a}, singleton_abcd a⟩ ∈ ({x, y} : Set B) := by
        rw [hxy.2]
        trivial
      exact this
    · intro _
      trivial

  have Hfin (i : B) : # (H i) < ℵ₀ := by
    by_contra hH₀
    push_neg at hH₀

    have : # (H i) = ℵ₀ := by
      have : # (H i) ≤ ℵ₀ := by
        rw [← hA]
        exact mk_set_le $ H i

      exact le_antisymm  this hH₀

    exact hyp (H i) this $ Hhom i

  have : # A < ℵ₀ := by
    calc # A
      _ = # (Set.univ : Set A) := by exact mk_univ.symm
      _ = # (H x ∪ H y : Set A)  := by rw [that]
      _ ≤ # (H x)  + # (H y) := by exact mk_union_le (H x) (H y)
      _ < ℵ₀ := by exact add_lt_aleph0 (Hfin x) (Hfin y)

  exact LT.lt.ne this hA

lemma ramsey_two (n : ℕ) : arrows_card ℵ₀ ℵ₀ n 2 := by


  induction n
  case zero => exact rathole_principle
  case succ n hn =>
    rw [Nat.succ_eq_add_one]
    intro A B hA hB c

    --have ih' (A : Set ℕ) : arrows ℵ₀ n A (Fin 2) := sorry -- monotone_left (Set.subset_univ A) hn

    have ih' (a : A) (A₀ : Set A) (h : # A₀ = ℵ₀) : arrows_type (A₀ \ {a} : Set A) ℵ₀ n B := by
      apply hn
      · sorry --TODO
      · exact hB

    let c' (a : A) (A₀ : Set A) (Y : abcd (A₀ \ {a} : Set A) n ) := c ⟨insert a Y.1, by
      have : a ∉ (Y.1 : Set A) := by
        intro hyp
        have :  (Y.1 : Set A) ⊆ (A₀ \ {a}) := coe_subset
        have that : a ∉ (A₀ \ {a}) :=  not_mem_diff_of_mem rfl
        exact that $ this hyp

      have : # (insert a (Y.1 : Set A) : Set A) = n + 1 := by
        have CoeM : #(Y.1 : Set A) = # Y := by sorry -- TODO, maybe this should be done outside bc it sounds highly usable

        rw [mk_insert]
        · rw [CoeM, Y.2]
        · exact this

      norm_cast at this
      ⟩

    let min (A₀ : Set A) (hA : # A₀ = ℵ₀) : {a : A // a ∈ A₀ ∧ ∀ b ∈ A₀, a = b} := sorry--a ≤ b} := by sorry

    --let select (A : Set ℕ) (hA : # A = ℵ₀) : ∃ (B : Set ℕ),
    let next' (A₀ : Set A) (hA₀ : # A₀ = ℵ₀) := (Exists.choose $ ih' (min A₀ hA₀) A₀ hA₀ (c' (min A₀ hA₀) A₀))

    let next (A₀ : Set A) (hA₀ : # A₀ = ℵ₀) : Set A := Subtype.val '' next' A₀ hA₀

    let next_inf' (A₀ : Set A) (hA₀ : # A₀ = ℵ₀) : # (next' A₀ hA₀) = ℵ₀ := (Exists.choose_spec $ ih' (min A₀ hA₀) A₀ hA₀ (c' (min A₀ hA₀) A₀)).1

    let next_inf (A₀ : Set A) (hA₀ : # A₀ = ℵ₀) : # (next A₀ hA₀) = ℵ₀ := by
      rw [← next_inf' A₀ hA₀]
      --simp
      apply mk_image_eq
      exact Subtype.coe_injective


    let rec seq : (k : ℕ) → {A₀ : Set A // # A₀ = ℵ₀}
      | 0 => ⟨(Set.univ : Set A), by
          rw [@mk_univ]
          exact hA⟩
      | k + 1 => ⟨next (seq k) (seq k).2, next_inf (seq k) (seq k).2⟩

    let a (k : ℕ) : A := min (seq k) (seq k).2

    let R := Set.range a

    --have {Y : Set ℕ} (hY : Y ∈  abcd (Nat.succ n) A) (k : ℕ) (h : ∀ c ∈ Y, a k ≤ c) : c $ abcd_monotone (subset_univ A) hY = 0

    --have {Y : abcd A n} {k : ℕ} (hY : Y.1 ⊆ R) (ha₁ : a ∈ Y.1) (ha₂ : ∀ b ∈ Y.1, a ≤ b) :
    sorry
