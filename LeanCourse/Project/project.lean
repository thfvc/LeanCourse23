import Mathlib.SetTheory.Cardinal.Basic
import Mathlib.SetTheory.Cardinal.Ordinal
import Mathlib.SetTheory.Cardinal.Cofinality
import Mathlib.SetTheory.Cardinal.Finite

open Ordinal
open Cardinal
open Set

--set_option pp.universes true

--def abcd (X : Type*) (n : ℕ) : Set (Finset X) := {Y | Y.card = n} --TODO: rename this

--def abcd    (X : Type*) (ν : Cardinal) : Set (Set X) := {Y | Nat.card Y = ν} --TODO: rename this
def abcd (X : Type*) (ν : Cardinal) : Set (Set X) := {Y | # Y = ν}
/-
def abcd_le {X : Type*} (ν : Cardinal) (A : Set X) : Set (Set X) := {Y | # Y ≤ ν ∧ Y ⊆ A}

def abcd_lt {X : Type*} (ν : Cardinal) (A : Set X) : Set (Set X) := {Y | # Y < ν ∧ Y ⊆ A}
-/


lemma abcd_monotone {A' : Type*} {n : ℕ} {A : Set A'} (Y : abcd A n) : Subtype.val '' Y.1 ∈ abcd A' n := by
  have : # (Subtype.val '' Y.1) = # Y := mk_image_eq Subtype.coe_injective
  rw [Y.2] at this
  exact this

lemma abcd_inj {A A' : Type*} {n : ℕ} {f : A → A'} (hf: f.Injective) {Y : abcd A n} : f '' Y.1 ∈ abcd A' n := by
  have : lift.{u_1, u_2} # (f '' Y.1) = lift.{u_2, u_1} # Y := mk_image_eq_lift f Y.1 hf
  rw [Y.2] at this
  simp at this
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
  (h : arrows κ n A μ) : arrows κ n A' μ := by s0rry
-/

-- universe u

-- example {A B : Type u} (h : # A = #B) : Nonempty (A ≃ B) := by exact Cardinal.eq.mp
#check Function.RightInverse
#check Cardinal.eq


lemma arrows_type_bij.{u} {A A' : Type u} {κ : Cardinal} {n : ℕ} {B B' : Type*} (f : Equiv A A') (g : Equiv B B') :
    arrows_type A κ n B → arrows_type A' κ n B' := by
  intro h c



  let f' (Y : abcd A n) : abcd A' n := ⟨f.toFun '' Y, by
    apply abcd_inj
    exact f.left_inv.injective --Function.LeftInverse.injective f.
    ⟩

  obtain ⟨H, hH⟩ := h (g.invFun ∘ c ∘ f')



  let H' := f '' H
  use H'
  constructor
  · rw [← hH.1]
    apply mk_image_eq
    exact Function.LeftInverse.injective f.left_inv
  · obtain ⟨i, hi⟩ := hH.2
    use g.toFun i
    intro Y' hY'

    let Y : abcd A n := ⟨f.invFun '' Y', by
      apply abcd_inj
      exact Function.LeftInverse.injective f.right_inv⟩
    have hY₁ : Y.1 ⊆ H := by
      intro y hy
      obtain ⟨y', hy'⟩ := hy
      specialize hY' hy'.1
      obtain ⟨x, hx⟩ := hY'
      rw [← hx.2] at hy'
      simp at hy'
      rw [hy'.2] at hx

      exact hx.1

    have hY₂ : f' Y = Y' := by
      ext y'
      constructor
      · intro hy'
        obtain ⟨y, hy⟩ := hy'
        obtain ⟨x, hx⟩ := hy.1
        rw [← hy.2, ← hx.2]
        simp
        exact hx.1
      · intro hy'
        simp
        exact hy'

    have : g.invFun (c Y') = g.invFun (g.toFun i) := by
      calc g.invFun (c Y')
        _ = g.invFun (c (f' Y)) := by rw [hY₂]
        _ = (g.invFun ∘ c ∘ f') Y := by simp
        _ = i := by rw [← hi Y hY₁]
        _ = g.invFun (g.toFun i) := by simp

    simp at this
    rw [← this]
    simp
--this lemma could be useful: If we have two types which are in an arrows relation, that relation can be extended to all types
--of the same cardinality
lemma arrows_card_of_arrows_type {A : Type*} {κ : Cardinal} {n : ℕ} {B : Type*} (h: arrows_type A κ n B) :
    arrows_card (# A) κ n (# B) := by
  intro A' B' hA' hB'

  obtain ⟨f⟩ := Cardinal.eq.mp hA'.symm
  obtain ⟨g⟩ := Cardinal.eq.mp hB'.symm

  exact arrows_type_bij f g h


lemma arrows_card_iff_arrows_type {A : Type*} {κ : Cardinal} {n : ℕ} {B : Type*} :
    arrows_type A κ n B ↔ arrows_card (# A) κ n (# B) := by
  constructor
  · intro h
    exact arrows_card_of_arrows_type h
  · intro h
    exact h A B rfl rfl




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
    have hY'₂ : Subtype.val '' Y ∈ abcd A' n := abcd_monotone ⟨Y, hY₁⟩
    let Y'' : abcd A' n := ⟨Subtype.val '' Y, hY'₂⟩

    have : Y' = Y'' := by
      ext1
      exact hY₃

    rw [this]

    calc c' Y''
      _ = c ⟨Y, hY₁⟩ := by rfl
      _ = i := by exact hi { val := Y, property := hY₁ } hY₂


#check Equiv.ulift
#check Cardinal.le_mk_iff_exists_subset

lemma monotone_card (lambda κ κ' : Cardinal) (n : ℕ) (μ : Cardinal) (hκ : κ' ≤ κ):
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

lemma monotone_right_nontrivial {lambda κ : Cardinal} {n : ℕ} (μ μ' : Cardinal) (hnκ : n ≤ κ) (hμ : μ' ≤ μ) (hμ' : μ' ≠ 0):
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

    have : Nonempty B' := by
      rw [← mk_ne_zero_iff, hB']
      exact hμ'

    let F := f.invFun

    use F i
    intro Y hY
    apply hf

    have : ∃ i' : B', f i' = i := by -- this needs something like κ ≥ n I think
      rw [← hH.1] at hnκ
      obtain ⟨Y, hY⟩ := le_mk_iff_exists_subset.mp hnκ
      let i' := c ⟨Y, hY.2⟩
      use i'
      apply hi
      exact hY.1


    calc f (c Y)
      _ = (f ∘ c) Y := rfl
      _ = i := hi Y hY
      _ = f (F i) := (f.invFun_eq this).symm

lemma arrows_of_right_empty {lambda κ : Cardinal} {n : ℕ} (nleqlambda : n ≤ lambda) :
    arrows_card lambda κ n 0 := by
  intro A B hA hB c

  have this : Nonempty (abcd A n) := by
    rw [← hA] at nleqlambda
    obtain ⟨Y, hY⟩ := le_mk_iff_exists_set.mp nleqlambda
    simp
    use Y
    exact hY

  rw [← not_isEmpty_iff] at this
  rw [mk_eq_zero_iff] at hB

  have that : IsEmpty (abcd A n) := by exact c.isEmpty

  contradiction

lemma arrows_of_n_leq_kappa {lambda κ : Cardinal} {n : ℕ} {μ : Cardinal} (nleqlambda : n ≤ lambda) (κltn : κ < n) :
    arrows_card lambda κ n μ := by
  by_cases μ = 0
  · rw [h]
    exact arrows_of_right_empty nleqlambda
  · intro A B hA hB c
    have κleqcardA : κ ≤ # A := by
      rw [hA]
      apply le_of_lt

      calc κ
        _ < n := κltn
        _ ≤ lambda := nleqlambda

    obtain ⟨H, hH⟩ := le_mk_iff_exists_set.mp κleqcardA
    use H
    constructor
    · exact hH
    · have B_not_empty : Nonempty B := by
        rw [← mk_ne_zero_iff, hB]
        exact h
      obtain ⟨i⟩ := B_not_empty
      use i
      intro Y hY --such a Y cannot exist:

      have cardYeqn  : # Y.1 = n := by exact Y.2
      have cardYneqn : # Y.1 ≠ n := by
        apply ne_of_lt

        calc # Y.1
          _ ≤ # H := mk_le_mk_of_subset hY
          _ = κ := hH
          _ < n := κltn
      contradiction

#check lift_umax_eq

-- lemma arrows_card_lift'.{u}
--     {A : Type*}
--     {κ : Cardinal} {n : ℕ} {B : Type*} (h : arrows_type A κ n B) :
--     arrows_type (ULift.{u} A) (lift.{u} κ) n B := by
--   intro c'

--   let f (a : A) : ULift.{u} A := { down := a}

--   have f_inj : f.Injective := by exact ULift.up_injective

--   let c (Y : abcd A n) : B := (c' ⟨f '' Y, abcd_inj f_inj⟩)

--   obtain ⟨H, hH⟩ := h c

--   let H' := f '' H

--   use H'

--   constructor
--   · have : lift.{u} # H' = lift.{max u1 u3, u} # H := by
--       apply mk_image_eq_lift
--       · exact f_inj
--     have that : lift.{u1, max u1 u3} # H' = # H' := by
--       exact Cardinal.lift_id'.{u1, u3} #H'
--     rw [← that]
--     rw [this]
--     rw [hH.1]
--     simp
--     rw [Cardinal.lift_umax'.{u1, u3}]
--   · obtain ⟨i, hi⟩ := hH.2
--     use { down := i}
--     intro Y' hY'
--     let Y := f ⁻¹' Y'
--     have hY₁ : Y ⊆ H := by
--       intro a ha
--       exact (Function.Injective.mem_set_image f_inj).mp (hY' ha)
--     have hY₂ : # Y = n := by
--       sorry
--     specialize hi ⟨Y, hY₂⟩ hY₁
--     have hY'' : Y' = ⟨f '' Y, sorry⟩ := by sorry
--     rw [hY'']
--     rw [← hi]




lemma arrows_card_lift.{u1, u2, u3, u4} {lambda κ : Cardinal.{u1}} {n : ℕ} {μ : Cardinal.{u2}} (h : arrows_card lambda κ n μ) :
    arrows_card (lift.{u3, u1} lambda) (lift.{u3, u1} κ) n (lift.{u4, u2} μ) := by
  let A := Quotient.out lambda
  let B := Quotient.out μ

  have cardA : # A = lambda := mk_out lambda
  have cardB : # B = μ := mk_out μ

  let A' := ULift.{u3, u1} A
  let B' := ULift.{u4, u2} B

  let lambda' := # A'
  let μ' := # B'

  have hlambda' : Cardinal.lift.{u3, u1} lambda = lambda' := by simp
  have hμ' : Cardinal.lift.{u4, u2} μ = μ' := by simp

  rw [hlambda', hμ']

  apply arrows_card_of_arrows_type
  intro c'

  let f (a : A) : A' := {down := a}

  have hf: f.Bijective := by exact ULift.up_bijective

  have f_inj : f.Injective := by exact ULift.up_injective

  let c (Y : abcd A n) : B := (c' ⟨f '' Y, abcd_inj f_inj⟩).down

  obtain ⟨H, hH⟩ := h A B cardA cardB c

  let H' := f '' H

  use H'

  constructor
  · have : lift.{u1, max u1 u3} # H' = lift.{max u1 u3, u1} # H := by
      apply mk_image_eq_lift
      · exact f_inj
    have that : lift.{u1, max u1 u3} # H' = # H' := by
      exact Cardinal.lift_id'.{u1, u3} #H'
    rw [← that]
    rw [this]
    rw [hH.1]
    rw [Cardinal.lift_umax'.{u1, u3}]
  · obtain ⟨i, hi⟩ := hH.2
    use { down := i}
    intro Y' hY'
    let Y := f ⁻¹' Y'
    have hY₁ : Y ⊆ H := by
      intro a ha
      exact (Function.Injective.mem_set_image f_inj).mp (hY' ha)
    have hY₂ : # Y = n := by
      have : lift.{max u1 u3} # Y = n := by

        rw [Cardinal.mk_preimage_of_injective_of_subset_range_lift]
        simp
        exact Y'.2
        exact f_inj
        exact SurjOn.subset_range hY'
      exact lift_eq_nat_iff.mp this




    specialize hi ⟨Y, hY₂⟩ hY₁
    have hY'' : Y'.1 = f '' Y := by exact (preimage_eq_iff_eq_image hf).mp rfl
    have hY''' : # (f '' Y) = n := by
      rw [← hY'']
      exact Y'.2
    have hY'''' : Y' = ⟨f '' Y, hY'''⟩ := by
      exact SetCoe.ext hY''
    rw [hY'''']
    rw [← hi]



lemma arrows_card_lift_left.{u1, u2} {lambda κ : Cardinal.{u1}} {n : ℕ} {μ : Cardinal} (h : arrows_card lambda κ n μ) :
    arrows_card (lift.{u2} lambda) (lift.{u2} κ) n μ := by
  rw [← lift_id μ]
  exact arrows_card_lift h
-- lemma monotone_right (lambda κ : Cardinal) (n : ℕ) {μ μ' : Cardinal} (hμ' : μ' ≤ μ) :
--     arrows_card lambda κ n μ → arrows_card lambda κ n μ' := sorry

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

noncomputable def min (X : Set ℕ) : ℕ := sInf X

--lemma test (A : Set ℕ) (B : Set ℕ) (hA : # A = ℵ₀) (hB : # B < ℵ₀) : # A \ B = ℵ₀ := sorry


-- WIP
lemma ramsey_two.{u1, u2} (n : ℕ) : arrows_card (ℵ₀ : Cardinal.{u1}) (ℵ₀ : Cardinal.{u1}) n (2 : Cardinal.{u2}):= by
  rw [← lift_aleph0.{0, u1}]
  rw [← lift_two.{u2, 0}]
  --rw [← Cardinal.lift_id.{0} (2 : Cardinal.{u2})]
  apply arrows_card_lift
  induction n
  case zero => exact rathole_principle
  case succ n hn =>
    nth_rw 1 [← mk_nat]
    rw [← show ((2 : ℕ) : Cardinal) = 2 from rfl, ← mk_fin 2]
    apply arrows_card_of_arrows_type
  --   rw [Nat.succ_eq_add_one]
    intro c

    --have ih' (A : Set ℕ) : arrows ℵ₀ n A (Fin 2) := sorry -- monotone_left (Set.subset_univ A) hn
    have ih' (a : ℕ) (A : Set ℕ) (h : # A = ℵ₀) : arrows_type (A \ {b | b ≤ a} : Set ℕ) ℵ₀ n (Fin 2) := by
      apply hn
      · apply le_antisymm
        · exact mk_le_aleph0
        · by_contra neg
          simp at neg
          have thingy : {b | b ∈ A ∧ b ≤ a}.Finite := by
            apply (finite_le_nat a).subset
            simp

          --simp at thingy
          have that : A.Finite := by
            have : A = {x | x ∈ A ∧ a < x} ∪ {b | b ∈ A ∧ b ≤ a} := by
              ext x
              constructor
              · intro hx
                simp [hx]
                exact Nat.lt_or_ge a x
              · intro hx
                simp at hx
                obtain left | right := hx
                · exact left.left
                · exact right.left
            rw [this]
            exact Set.Finite.union neg thingy
          apply that.not_infinite
          exact infinite_coe_iff.mp $ infinite_iff.mpr $ Eq.le (id h.symm)


      · exact mk_fin 2

    let f (a : ℕ) (A : Set ℕ) (Y : abcd (A \ {a} : Set ℕ) n) : abcd ℕ (Nat.succ n) := ⟨insert a (Subtype.val '' Y.1), by
      -- have cardY : # Y.1 = n := Y.2
      -- simp_rw [cardY]
      have : # (insert a (Subtype.val '' Y.1) : Set ℕ) = n + 1 := by
        have : # (Subtype.val '' Y.1) = n := by
          have := Y.2
          simp_rw [Y.2.symm]
          exact mk_image_eq Subtype.coe_injective
        simp_rw [← this]
        apply mk_insert
        intro ha
        obtain ⟨b, hb⟩ := ha
        apply ((mem_diff b.1).mp b.2).2
        simp_rw [← hb.2]
        simp
      rw [← Nat.add_one]
      push_cast
      exact this⟩

    let c' (a : ℕ) (A : Set ℕ) (Y : abcd (A \ {a} : Set ℕ) n ) := c $ f a A Y

    let min (A : Set ℕ) (hA : # A = ℵ₀) : {a : ℕ // a ∈ A ∧ ∀ b ∈ A, a ≤ b} := sorry--a ≤ b} := by sorry, need to apply well-ordering theorem (or rephrase this proof just for ℕ and Fin 2, and then do this with the ordering on ℕ)

  --   --let select (A : Set ℕ) (hA : # A = ℵ₀) : ∃ (B : Set ℕ),
    let h_next (A : Set ℕ) (hA : # A = ℵ₀) := ih' (min A hA) A hA (c' (min A hA) A)

    --let next (A : Set N) (hA : # A = ℵ₀) : Set N := Subtype.val '' next' A hA

    let next (A : Set ℕ) (hA : # A = ℵ₀) := Subtype.val '' (h_next A hA).choose

    have h'_next (A : Set ℕ) (hA : # A = ℵ₀) : next A hA ⊆ A := by
      intro a ha

    have next_inf (A : Set ℕ) (hA : # A = ℵ₀) : # (next A hA) = ℵ₀ := by --(Exists.choose_spec $ ih' (min A₀ hA₀) A₀ hA₀ (c' (min A₀ hA₀) A₀)).1
      rw [← (h_next A hA).choose_spec.1]
      apply mk_image_eq Subtype.coe_injective

  --   let next_inf (A₀ : Set A) (hA₀ : # A₀ = ℵ₀) : # (next A₀ hA₀) = ℵ₀ := by
  --     rw [← next_inf' A₀ hA₀]
  --     apply mk_image_eq
  --     exact Subtype.coe_injective


    let rec seq : (k : ℕ) → {A : Set ℕ // # A = ℵ₀}
      | 0 => ⟨(Set.univ : Set ℕ), by
          rw [@mk_univ, mk_nat]⟩
      | k + 1 => ⟨next (seq k) (seq k).2, next_inf (seq k) (seq k).2⟩

    have h_rec (k : ℕ) := h_next (seq k).1 (seq k).2

    have h'_rec (k : ℕ) : (seq (k + 1)).1 ⊆ (seq k).1 := by
      intro a ha



    let a (k : ℕ) : ℕ := min (seq k).1 (seq k).2

    let R := range a

    let i (k : ℕ) : Fin 2 := (h_rec k).choose_spec.2.choose
    let hi (k : ℕ) := (h_rec k).choose_spec.2.choose_spec

    let i' (Y : abcd ℕ 1) : Fin 2 := i $ (singleton_of_card_one Y.2).choose

    obtain ⟨C, hC⟩ := pigeonhole_principle ℕ (Fin 2) mk_nat (mk_fin 2) i'

  --   --have {Y : Set ℕ} (hY : Y ∈  abcd (Nat.succ n) A) (k : ℕ) (h : ∀ c ∈ Y, a k ≤ c) : c $ abcd_monotone (subset_univ A) hY = 0
    --have {Y : Set ℕ} (hY₁ : # Y = Nat.succ n) (k : ℕ) (hk : k ∈ Y) (h : ∀ l ∈ Y, a k ≤ a l) : sorry := sorry
  --   --have {Y : abcd A n} {k : ℕ} (hY : Y.1 ⊆ R) (ha₁ : a ∈ Y.1) (ha₂ : ∀ b ∈ Y.1, a ≤ b) :

    let H := a '' C

    use H
    constructor
    · rw [← hC.1]
      apply mk_image_eq

    · obtain ⟨colour, hcolour⟩ := hC.2
      use colour
      intro Y hY
      have : # Y = Nat.succ n := by sorry




-- quantify over universes?

--lemma arrows_lift {A : Type} {κ : Cardinal} {n : ℕ} {B : Type} (h : arrows_type A κ n B) : ∀ u_1, u_2, arrows_type (ULift.{u_1, 1} A) κ n (ULift.{u_2, 1} B) := sorry
#check ite

lemma this_is_a_lemma (m : ℕ) (a : Fin (m + 1)) : a ≠ m → a < m := by
  intro h
  refine LE.le.lt_of_ne' ?_ (id (Ne.symm h))
  exact Fin.le_val_last a

theorem ramsey (n m : ℕ) : arrows_card ℵ₀ ℵ₀ n m := by
  apply arrows_card_lift
  induction m
  case zero =>
    simp
    exact arrows_of_right_empty $ le_of_lt (nat_lt_aleph0 n)
  case succ m hm =>

    apply arrows_card_of_arrows_type
    intro c

    -- let c' (Y : abcd (ULift.{u_1, 0} ℕ) n) : ULift.{u_2, 0} (Fin 2) := {
    --   down := if (c Y).down < m then 0 else 1
    -- }-- if (c Y).down < m then 0 else 1 --Need to look up how I can define something by cases

    let f (a : (Fin (Nat.succ m))) : (Fin 2) := if a < m then 0 else 1

    have hf (a : (Fin (Nat.succ m))) (ha : (f a) = 1) : a = m := by
      simp at ha
      apply le_antisymm
      · exact Fin.le_val_last a
      · exact Fin.not_lt.mp ha
    -- have hc'₀ (Y : abcd (ULift.{u_1, 0} ℕ) n) (hY : (c Y).down < m) : (c' Y).down = 0 := by sorry
    -- have hc'₁ (Y : abcd (ULift.{u_1, 0} ℕ) n) (hY : (c Y).down = m) : (c' Y).down = 1 := by sorry

    --have : # (ULift.{u_1, 0} ℕ) = ℵ₀ := by exact?


    obtain ⟨H, hH⟩ := ramsey_two n ℕ (Fin 2) mk_nat (mk_fin 2) (f ∘ c)

    obtain ⟨i, hi⟩ := hH.2

    by_cases i = 0
    ·
      have {Y : abcd ℕ n} (hY : Y.1 ⊆ H) : c Y < m := sorry



      let c'' (Y : abcd H n) : (ULift.{u_2, 0} (Fin m)) := ⟨((c Y) : ℕ), sorry⟩
      sorry -- let c'' (Y : abcd H n) : (ULift.{u_2, 0} (Fin m)) := --⟨((c ⟨Y.1, sorry⟩) : ULift.{u_2, 0} ℕ), sorry⟩
    · have ieo : i = 1 := fin2_one_of_ne_two i h
      use H
      constructor
      · rw [mk_nat]
        exact hH.1
      · use m
        intro Y hY
        have : (f ∘ c) Y = 1 := by rw [hi Y hY, ieo]

        simp at this
        by_contra neg
        apply this
        have that : c Y ≠ m := by
          exact neg
        exact this_is_a_lemma m (c Y) that




lemma split_pair {A : Type*} {Y : Set A} (hY : # Y = 2) : ∃ x : A, ∃ y : A, x ≠ y ∧ Y = {x, y} := by sorry




example : ¬arrows_card (2^ℵ₀) 3 2 ℵ₀ := by

  have h₁ : 2 ^ ℵ₀ = # (ℕ → Fin 2) := by simp
  have h₂ : ℵ₀ = # ℕ := by simp

  rw [h₁, h₂]

  rw [← arrows_card_iff_arrows_type]

  intro h

  --probably want some lemma / function separating a set of cardinality 2 into its two components

  let c (Y : abcd (ℕ → Fin 2) 2) : ℕ := sorry

  obtain ⟨H, hH⟩ := h c



  sorry


#check Set.Nonempty

noncomputable section --huh, this is needed for the definition of ℶ

open Ordinal


--Remark: The definition of beth numbers in mathlib is not entirely congruent with the one in the script I use
def ℶ.{u} (κ : Cardinal.{u}) (α : Ordinal.{u}) : Cardinal :=
  limitRecOn α κ (fun _ x => (2 : Cardinal) ^ x) fun a _ IH => ⨆ b : Iio a, IH b.1 b.2

lemma ℶ_zero {κ : Cardinal} : ℶ κ 0  = κ := limitRecOn_zero _ _ _

open Order -- TODO: maybe put on top

lemma ℶ_succ {κ : Cardinal} {α : Ordinal} : ℶ κ (succ α) = 2 ^ (ℶ κ α)
  := limitRecOn_succ _ _ _ _

lemma ℶ_limit {κ : Cardinal} {α : Ordinal} : α.IsLimit → ℶ κ α = ⨆ β : Iio α, ℶ κ β :=
  limitRecOn_limit _ _ _ _

example {α : Ordinal} : beth α = ℶ ℵ₀ α := rfl

-- I cant write the name of the theorem properly, because "Erdős" is not allowed as a string

theorem erdos_rado {n : ℕ} {κ : Cardinal} (hκ : ℵ₀ ≤ κ) : -- this complains about universes unless ℶ takes input only from the same universe
    arrows_card (succ (ℶ κ n)) (succ κ) (n + 1) κ  := by
  induction n
  case zero =>
    simp
    rw [ℶ_zero]
    intro A B hA hB c

    let f (x : A) : (abcd A 1) := ⟨{x}, by rw [abcd]; simp⟩

    have hf : f.Bijective := by
      constructor
      · intro x y hxy
        simp at hxy
        exact hxy
      · intro y
        obtain ⟨x, hx⟩ := singleton_of_card_one y.2
        use x
        ext1
        rw [hx]

    have hA' : succ κ ≤ # (abcd A 1) := by
      rw [← hA]
      rw [le_def]

      use f
      exact Function.Bijective.injective hf

    have hκ' : ℵ₀ ≤ succ κ := by
      calc ℵ₀
        _ ≤ κ := hκ
        _ ≤ succ κ := by exact le_succ κ

    have hB' : #B < Ordinal.cof (ord (succ κ)) := by
      rw [hB, (isRegular_succ hκ).cof_eq]
      exact lt_succ κ

    obtain ⟨i, hi⟩ := infinite_pigeonhole_card c (succ κ) hA' hκ' hB'

    obtain ⟨H', hH'⟩ := le_mk_iff_exists_subset.mp hi

    use f ⁻¹' H'

    constructor
    · rw [← hH'.2]
      apply mk_preimage_of_injective_of_subset_range
      · exact hf.injective
      · intro x hx
        exact hf.surjective x
    · use i
      intro Y hY
      apply hH'.1

      obtain ⟨y⟩ := nonempty_of_card_pos $ le_of_eq Y.2.symm

      have : f y.1 = Y := by
        ext1
        simp
        obtain ⟨x, hx⟩ := singleton_of_card_one Y.2
        have : y.1 = x := by
          let h := y.2
          simp_rw [hx] at h
          exact h
        simp_rw [hx]
        simp
        exact this

      rw [← this]
      exact hY y.2

  case succ n hn =>
    intro A B hA hB c

    -- maybe add some type like "almost a colouring" and save some headaches with casts

    let c' (a : A) (Y : abcd ((univ : Set A) \ {a} : Set A) (n + 1)) := c ⟨insert a (Subtype.val '' Y.1), by
        have : # (Subtype.val '' Y.1) = n + 1 := by
          have : #Y.1 = n + 1 := by
            exact Y.2
          simp_rw [← this]
          exact mk_image_eq Subtype.coe_injective
        have : # (insert a (Subtype.val '' Y.1) : Set A) = n + 1 + 1 := by
          simp_rw [← this]
          apply mk_insert
          intro h
          obtain ⟨b, hb⟩ := h
          exact ((mem_diff b.1).mp b.2).2 hb.2
        norm_cast at this⟩
    --let c' (a : A) (Y : abcd A (n + 1)) : B := sorry

    have thingy {a : A} {B : Set A} {Y : abcd A (n + 1)} (ha : a ∉ B) (hY : Y.1 ⊆ B) : Subtype.val ⁻¹' Y.1 ∈ abcd ((Set.univ : Set A) \ {a} : Set A) (n + 1) := by
      have : # Y.1 = n + 1 := by exact Y.2
      simp_rw [← this]
      apply mk_preimage_of_injective_of_subset_range
      · exact Subtype.coe_injective
      · simp
        intro x hx
        intro hx'
        subst hx'
        exact ha $ hY hx

    have claim : ∃ A' : Set A, # A = ℶ κ (n + 1) ∧ ∀ B : Set A, # B = ℶ κ n → ∀ b ∈ Bᶜ, ∃ a ∈ (A' \ B),
         ∀ Y : abcd A (n + 1), Y.1 ⊆ B → c' a ⟨Subtype.val ⁻¹' Y.1, sorry⟩ = c' b ⟨Subtype.val ⁻¹' Y, sorry⟩ := sorry

    obtain ⟨X, hX⟩ := claim



    sorry
