import Mathlib.SetTheory.Cardinal.Basic
import Mathlib.SetTheory.Cardinal.Ordinal
import Mathlib.SetTheory.Cardinal.Cofinality

open Ordinal
open Cardinal
open Set

def abcd {X : Type*} (s : Set X) (ν : Cardinal) : Set (Set X) := {Y | Y ⊆ s ∧ # Y = ν} --TODO: rename this

def abcd_type (X : Type*) (ν : Cardinal) : Set (Set X) := abcd (Set.univ : Set X) ν
/-
def abcd_le {X : Type*} (ν : Cardinal) (A : Set X) : Set (Set X) := {Y | # Y ≤ ν ∧ Y ⊆ A}

def abcd_lt {X : Type*} (ν : Cardinal) (A : Set X) : Set (Set X) := {Y | # Y < ν ∧ Y ⊆ A}
-/


lemma abcd_monotone {X : Type*} {n : ℕ} {s₁ s₂ : Set X} (Y : abcd s₁ n) (h : s₁ ⊆ s₂): Y.1 ∈ abcd s₂ n := by
  constructor
  · exact subset_trans Y.2.1 h
  · exact Y.2.2

lemma abcd_inj.{u} {X X' : Type u} {n : ℕ} {f : X → X'} (hf: f.Injective) (Y : abcd_type X n) : f '' Y.1 ∈ abcd_type X' n := by
  constructor
  · exact subset_univ (f '' ↑Y)
  · simp_rw [← Y.2.2]
    exact mk_image_eq hf


/-
@[simp] lemma abcd_monotone' {X : Type*} {ν : Cardinal} {B C Y: Set X} (hB : Y ⊆ B) (hY : Y ∈ abcd ν C) :
  Y ∈ abcd ν B := ⟨hY.1, hB⟩

-/
def coloring {X : Type*} (s : Set X) (n : ℕ) (μ : Type*) := (abcd s n) → μ

example {X : Type*} (A A' : Set X) : A ∩ A' ⊆ A := by exact Set.inter_subset_left A A'

def homogeneous_of_color {X μ : Type*} {s : Set X} {n : ℕ} (c : coloring s n μ) (H : Set X) (i : μ)  : Prop :=
  ∀ Y : abcd s n, Y.1 ⊆ H →  c Y  = i

def homogeneous {A B : Type*} {s : Set A} {n : ℕ} (c : coloring s n B) (H : Set A) : Prop :=
  ∃ i : B, homogeneous_of_color c H i

def arrows_concrete {A : Type*} (s : Set A) (κ : Cardinal) (n : ℕ) (B : Type*) : Prop :=
  ∀ (c : coloring s n B), ∃ H : Set A, H ⊆ s ∧ # H = κ ∧ homogeneous c H

def arrows_abstract (lambda κ : Cardinal) (n : ℕ) (μ : Cardinal) : Prop :=
  ∀ (A B : Type*), ∀ s : Set A, # s = lambda → # B = μ → arrows_concrete s κ n B
/-
lemma nice_iso_left {X X' : Type u1} {μ : Type*} (κ : Cardinal) (n : ℕ) (A : Set X) (A' : Set X') (f : X → X') (hf : f.Bijective)
  (h : arrows κ n A μ) : arrows κ n A' μ := by sorry
-/

-- universe u

-- example {A B : Type u} (h : # A = #B) : Nonempty (A ≃ B) := by exact Cardinal.eq.mp
#check Function.RightInverse
#check Cardinal.eq


--this lemma could be useful: If we have two types which are in an arrows relation, that relation can be extended to all types
--of the same cardinality
lemma arrows_abstract_of_arrows_concrete {A : Type*} {s : Set A} {κ : Cardinal} {n : ℕ} {B : Type*} (h: arrows_concrete s κ n B) :
    arrows_abstract (# s) κ n (# B) := by
  intro A' B' s' hA' hB' c

  obtain ⟨F, f, hF, hf⟩ := Cardinal.eq.mp hA'
  obtain ⟨g, G, hg, hG⟩ := Cardinal.eq.mp hB'

  let f' (Y : abcd s n) : abcd s' n := ⟨f '' Y.1, by
    apply abcd_inj
    exact Function.LeftInverse.injective hf
    ⟩


  obtain ⟨H, hH⟩ := h (g ∘ c ∘ f')



  let H' := f '' H
  use H'
  constructor
  · rw [← hH.1]
    apply mk_image_eq
    exact Function.LeftInverse.injective hf
  · obtain ⟨i, hi⟩ := hH.2
    use G i
    intro Y' hY'

    let Y : abcd A n := ⟨F '' Y', by
      apply abcd_inj
      exact Function.LeftInverse.injective hF⟩
    have hY₁ : Y.1 ⊆ H := by
      intro y hy
      obtain ⟨y', hy'⟩ := hy
      specialize hY' hy'.1
      obtain ⟨x, hx⟩ := hY'
      rw [← hx.2, hf] at hy'
      rw [hy'.2] at hx

      exact hx.1

    have hY₂ : f' Y = Y' := by
      ext y'
      constructor
      · intro hy'
        obtain ⟨y, hy⟩ := hy'
        obtain ⟨x, hx⟩ := hy.1
        rw [← hy.2, ← hx.2, hF]
        exact hx.1
      · intro hy'
        simp
        use y'
        constructor
        · exact hy'
        · exact hF y'

    have : g (c Y') = g (G i) := by
      calc g (c Y')
        _ = g (c (f' Y)) := by rw [hY₂]
        _ = (g ∘ c ∘ f') Y := by simp
        _ = i := by rw [← hi Y hY₁]
        _ = g (G i) := by exact (hG i).symm

    have that : g.Injective := by exact Function.LeftInverse.injective hg

    exact that this


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


-- WIP
lemma ramsey_two (n : ℕ) : arrows_card (ℵ₀ : Cardinal) ℵ₀ n 2 := by

  induction n
  case zero => exact rathole_principle
  case succ n hn =>
    apply arrows_card_of_arrows_type
  --   rw [Nat.succ_eq_add_one]
    intro c

    --have ih' (A : Set ℕ) : arrows ℵ₀ n A (Fin 2) := sorry -- monotone_left (Set.subset_univ A) hn
    let N := ULift.{u_1, 0} ℕ
    have ih' (a : N) (A : Set N) (h : # A = ℵ₀) : arrows_type (A \ {a} : Set N) ℵ₀ n (ULift.{u_2, 0} $ Fin 2) := by
      apply hn
      · apply le_antisymm
        · exact mk_le_aleph0
        · apply add_one_le_add_one_iff_of_lt_aleph_0.mp
          simp
          rw [← mk_singleton a, ← h]
          exact le_mk_diff_add_mk A {a}
      · rfl

    let f (a : N) (A : Set N) (Y : abcd (A \ {a} : Set N) n) : abcd N (Nat.succ n) := ⟨insert a (Subtype.val '' Y.1), by
      -- have cardY : # Y.1 = n := Y.2
      -- simp_rw [cardY]
      have : # (insert a (Subtype.val '' Y.1) : Set N) = n + 1 := by
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

    let c' (a : N) (A : Set N) (Y : abcd (A \ {a} : Set N) n ) := c $ f a A Y

    let min (A : Set N) (hA : # A = ℵ₀) : {a : N // a ∈ A ∧ ∀ b ∈ A, a.down ≤ b.down} := sorry--a ≤ b} := by sorry, need to apply well-ordering theorem (or rephrase this proof just for ℕ and Fin 2, and then do this with the ordering on ℕ)

  --   --let select (A : Set ℕ) (hA : # A = ℵ₀) : ∃ (B : Set ℕ),
    let next (A : Set N) (hA : # A = ℵ₀) : Set N := Subtype.val '' (Exists.choose $ ih' (min A hA) A hA (c' (min A hA) A))

    --let next (A : Set N) (hA : # A = ℵ₀) : Set N := Subtype.val '' next' A hA

    let next_inf (A : Set N) (hA : # A = ℵ₀) : # (next A hA) = ℵ₀ := by --(Exists.choose_spec $ ih' (min A₀ hA₀) A₀ hA₀ (c' (min A₀ hA₀) A₀)).1
      rw [← (Exists.choose_spec $ ih' (min A hA) A hA (c' (min A hA) A)).1]
      exact mk_image_eq Subtype.coe_injective

  --   let next_inf (A₀ : Set A) (hA₀ : # A₀ = ℵ₀) : # (next A₀ hA₀) = ℵ₀ := by
  --     rw [← next_inf' A₀ hA₀]
  --     apply mk_image_eq
  --     exact Subtype.coe_injective


    let rec seq : (k : ℕ) → {A : Set N // # A = ℵ₀}
      | 0 => ⟨(Set.univ : Set N), by
          rw [@mk_univ]
          rfl⟩
      | k + 1 => ⟨next (seq k) (seq k).2, next_inf (seq k) (seq k).2⟩

    let a (k : ℕ) : N := min (seq k).1 (seq k).2

    let R := range a

  --   --have {Y : Set ℕ} (hY : Y ∈  abcd (Nat.succ n) A) (k : ℕ) (h : ∀ c ∈ Y, a k ≤ c) : c $ abcd_monotone (subset_univ A) hY = 0

  --   --have {Y : abcd A n} {k : ℕ} (hY : Y.1 ⊆ R) (ha₁ : a ∈ Y.1) (ha₂ : ∀ b ∈ Y.1, a ≤ b) :
    sorry

-- quantify over universes?

--lemma arrows_lift {A : Type} {κ : Cardinal} {n : ℕ} {B : Type} (h : arrows_type A κ n B) : ∀ u_1, u_2, arrows_type (ULift.{u_1, 1} A) κ n (ULift.{u_2, 1} B) := sorry
#check ite

theorem ramsey (n m : ℕ) : arrows_card ℵ₀ ℵ₀ n m := by
  induction m
  case zero => exact arrows_of_right_empty $ le_of_lt (nat_lt_aleph0 n)
  case succ m hm =>

    apply arrows_card_of_arrows_type
    intro c

    -- let c' (Y : abcd (ULift.{u_1, 0} ℕ) n) : ULift.{u_2, 0} (Fin 2) := {
    --   down := if (c Y).down < m then 0 else 1
    -- }-- if (c Y).down < m then 0 else 1 --Need to look up how I can define something by cases

    let f (a : ULift.{u_2, 0} (Fin (Nat.succ m))) : ULift.{u_2, 0} (Fin 2) := { down := if a.down < m then 0 else 1}

    have hf (a : ULift.{u_2, 0} (Fin (Nat.succ m))) (ha : (f a).down = 1) : a.down = m := by
      simp at ha
      apply le_antisymm
      · exact Fin.le_val_last a.down
      · exact Fin.not_lt.mp ha
    -- have hc'₀ (Y : abcd (ULift.{u_1, 0} ℕ) n) (hY : (c Y).down < m) : (c' Y).down = 0 := by sorry
    -- have hc'₁ (Y : abcd (ULift.{u_1, 0} ℕ) n) (hY : (c Y).down = m) : (c' Y).down = 1 := by sorry

    --have : # (ULift.{u_1, 0} ℕ) = ℵ₀ := by exact?


    obtain ⟨H, hH⟩ := ramsey_two n (ULift.{u_1, 0} ℕ) (ULift.{u_2, 0} (Fin 2)) rfl rfl (f ∘ c)

    obtain ⟨i, hi⟩ := hH.2

    by_cases i.down = 0
    · sorry -- let c'' (Y : abcd H n) : (ULift.{u_2, 0} (Fin m)) := --⟨((c ⟨Y.1, sorry⟩) : ULift.{u_2, 0} ℕ), sorry⟩
    · have ieo : i.down = 1 := fin2_one_of_ne_two i.down h
      use H
      constructor
      · exact hH.1
      · use { down := m }
        intro Y hY
        have : ((f ∘ c) Y).down = 1 := by rw [hi Y hY, ieo]
        simp at this
        sorry




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
