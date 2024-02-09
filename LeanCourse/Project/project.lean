import Mathlib.SetTheory.Cardinal.Basic
import Mathlib.SetTheory.Cardinal.Ordinal
import Mathlib.SetTheory.Cardinal.Cofinality
import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Data.Real.Basic
import Mathlib.Data.Real.Cardinality

open Ordinal
open Cardinal
open Set


-- the entirety of this formalization is based on the notes by Stefan Geschke, they can be found at
-- https://www.math.uni-hamburg.de/home/geschke/teaching/InfiniteRamseyNotes.pdf

-- this file takes about 40 seconds to check on my (somewhat good) laptop
-- the major problem here is ramsey_two, which needs to check a lot of cardinalities



-- this notion for ν = 2 corresponds to undirected edges
def edges (X : Type*) (ν : Cardinal) : Set (Set X) := {Y | # Y = ν}

lemma edges_monotone {A' : Type*} {n : ℕ} {A : Set A'} (Y : edges A n) : Subtype.val '' Y.1 ∈ edges A' n := by
  have : # (Subtype.val '' Y.1) = # Y := mk_image_eq Subtype.coe_injective
  rw [Y.2] at this
  exact this

lemma edges_inj {A A' : Type*} {n : ℕ} {f : A → A'} (hf: f.Injective) {Y : edges A n} : f '' Y.1 ∈ edges A' n := by
  have : lift.{u_1, u_2} # (f '' Y.1) = lift.{u_2, u_1} # Y := mk_image_eq_lift f Y.1 hf
  rw [Y.2] at this
  simp at this
  exact this

def coloring (X : Type*) (n : ℕ) (μ : Type*) := (edges X n) → μ

example {X : Type*} (A A' : Set X) : A ∩ A' ⊆ A := by exact Set.inter_subset_left A A'

def homogeneous_of_color {X μ : Type*} {n : ℕ} (c : coloring X n μ) (H : Set X) (i : μ)  : Prop :=
  ∀ Y : edges X n, Y.1 ⊆ H →  c Y  = i

def homogeneous {A B : Type*} {n : ℕ} (c : coloring A n B) (H : Set A) : Prop :=
  ∃ i : B, homogeneous_of_color c H i

def arrows_type (A : Type*) (κ : Cardinal) (n : ℕ) (B : Type*) : Prop :=
  ∀ (c : coloring A n B), ∃ H : Set A, # H = κ ∧ homogeneous c H


-- A note on notation: The source I adapted used λ as a cardinal. Due to lambda terms I was unable to do so. Instead we use lambda.
def arrows_card (lambda κ : Cardinal) (n : ℕ) (μ : Cardinal) : Prop :=
  ∀ (A B : Type*), # A = lambda → # B = μ → arrows_type A κ n B

lemma arrows_type_bij.{u} {A A' : Type u} {κ : Cardinal} {n : ℕ} {B B' : Type*} (f : Equiv A A') (g : Equiv B B') :
    arrows_type A κ n B → arrows_type A' κ n B' := by
  intro h c

  let f' (Y : edges A n) : edges A' n := ⟨f.toFun '' Y, by
    apply edges_inj
    exact f.left_inv.injective
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

    let Y : edges A n := ⟨f.invFun '' Y', by
      apply edges_inj
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

  let c (Y : edges A n) : B := c' ⟨Subtype.val '' Y.1, edges_monotone Y⟩

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
    have hY₁ : Y ∈ edges A n := by
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
    have hY'₂ : Subtype.val '' Y ∈ edges A' n := edges_monotone ⟨Y, hY₁⟩
    let Y'' : edges A' n := ⟨Subtype.val '' Y, hY'₂⟩

    have : Y' = Y'' := by
      ext1
      exact hY₃

    rw [this]

    calc c' Y''
      _ = c ⟨Y, hY₁⟩ := by rfl
      _ = i := by exact hi { val := Y, property := hY₁ } hY₂

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

    have : ∃ i' : B', f i' = i := by
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

  have this : Nonempty (edges A n) := by
    rw [← hA] at nleqlambda
    obtain ⟨Y, hY⟩ := le_mk_iff_exists_set.mp nleqlambda
    simp
    use Y
    exact hY

  rw [← not_isEmpty_iff] at this
  rw [mk_eq_zero_iff] at hB

  have that : IsEmpty (edges A n) := by exact c.isEmpty

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

-- The bane of my existence, I never want to have to think about LEAN cardinals again
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

  let c (Y : edges A n) : B := (c' ⟨f '' Y, edges_inj f_inj⟩).down

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

-- lemma neq_of_not_member_singleton {A : Type*} {a b : A} (h : a ∉ ({b} : Set A)) : b ≠ a := by
--   exact Ne.symm h

lemma fin2_one_of_ne_zero {x : Fin 2} (h : x ≠ 0) : x = 1 := by
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


-- a (somewhat) trivial variant of the pigeonhole principle
lemma rathole_principle : arrows_card ℵ₀ ℵ₀ 0 2 := by
  intro A B hA _ c
  use Set.univ
  simp
  constructor
  · exact hA
  · have : ∅ ∈ edges A 0 := by exact mk_emptyCollection A
    let i := c ⟨∅, this⟩
    use i
    intro Y _

    have : Y = ⟨∅, this⟩ := by
      ext1
      rw [← mk_emptyCollection_iff]
      exact Y.2
    rw [this]

lemma singleton_edges {A : Type*} (x : A) : {x} ∈ edges A 1  := by
    rw [edges]
    simp

lemma mono_backwards {A B : Type*} [LinearOrder A] [LinearOrder B] {f : A → B} (ha : Monotone f) {k l : A} (hkl : f k < f l) : k < l := by
  by_contra hyp
  simp at hyp
  exact LT.lt.false $ lt_of_le_of_lt (ha hyp) hkl

-- this is how the usual pigeonhole principle (in its most basic form) looks in this context.
-- Note: Since LEAN doesnt identify singleton sets and their contents, this lemma is (usually) less usable
-- than the versions from Mathlib
lemma pigeonhole_principle_edges : arrows_card ℵ₀ ℵ₀ 1 2 := by
  intro A B hA hB

  intro c
  by_contra hyp
  push_neg at hyp

  let H (i : B) := {x : A | c ⟨{x}, singleton_edges x⟩ = i}

  have Hhom (i : B): homogeneous c $ H i := by
    use i
    intro Y hY
    obtain ⟨n, hn⟩ := singleton_of_card_one Y.2
    have : n ∈ H i := by
      rw [← @Set.singleton_subset_iff, ← hn]
      exact hY

    calc c Y
      _ = c ⟨{n}, singleton_edges n⟩ := by rw [← Subtype.coe_eq_of_eq_mk hn]
      _ = i := this

  obtain ⟨x, y, hxy⟩ := mk_eq_two_iff.mp hB

  have that :  (Set.univ : Set A) = H x ∪ H y  := by
    ext a
    constructor
    · intro _
      simp
      have : c ⟨{a}, singleton_edges a⟩ ∈ ({x, y} : Set B) := by
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

lemma card_eq_of_bijection.{u} {A B : Type u} {f : A → B} (hf : Function.Bijective f) : # A = # B := by
  rw [Cardinal.eq]

  -- TODO: this seems weirdly unhandy, this should be easier!

  use Equiv.ofBijective f hf
  use (Equiv.ofBijective f hf).symm
  exact Equiv.left_inv' (Equiv.ofBijective f hf)
  exact Equiv.right_inv' (Equiv.ofBijective f hf)



-- a version of mk_ne_zero_iff for Sets
lemma set_nonempty_iff {A : Type*} {Y : Set A} : Y.Nonempty ↔ # Y ≠ 0 := by
  constructor
  · intro h
    rw [mk_ne_zero_iff]
    exact Nonempty.coe_sort h
  · intro h
    rw [nonempty_iff_ne_empty, ←nonempty_iff_ne_empty', ← mk_ne_zero_iff]
    exact h



lemma cardinal_succ_eq_add_one_of_finite {A : Type*} (hA : # A < ℵ₀) : Order.succ # A = # A + 1 := by
  rw [lt_aleph0] at hA
  obtain ⟨n, hn⟩ := hA
  rw [hn]
  norm_cast

lemma nonempty_of_succ_n {A : Type*} {n : ℕ} {Y : edges A (Nat.succ n)} : Y.1.Nonempty := by
  rw [set_nonempty_iff]
  let yyyy := Y.2
  rw [yyyy]
  exact NeZero.natCast_ne (Nat.succ n) Cardinal.{u_1}


-- this is only used for recursively defining something in the proof of ramseys theorem for 2 colors
private def seq' (next : {A : Set ℕ // # A = ℵ₀} → {A : Set ℕ // # A = ℵ₀}) :
                        ℕ → {A : Set ℕ // # A = ℵ₀}
      | 0 => ⟨(Set.univ : Set ℕ), by
          rw [@mk_univ, mk_nat]⟩
      | k + 1 => next $ seq' next k


lemma card_minus_one {A : Type*} {n : ℕ} {Y : Set A} {a : A} (hA : # Y = (n + 1 : ℕ)) (ha : a ∈ Y) : # ↑(Y \ {a}) = n := by
  apply Order.succ_injective
  norm_cast
  --rw [succ_eq_add_one]
  rw [← hA]
  have a_k_sub_Y : {a} ⊆ Y := by
    exact singleton_subset_iff.mpr ha
  rw [← mk_diff_add_mk a_k_sub_Y]
  simp
  have finite : # ↑(Y \ {a}) < ℵ₀ := by
    apply lt_of_le_of_lt
    · have sub_Y : (Y \ {a}) ⊆ Y := by simp
      exact mk_le_mk_of_subset sub_Y
    · rw [hA]
      exact nat_lt_aleph0 (Nat.succ n)
  rw [cardinal_succ_eq_add_one_of_finite finite]

set_option maxHeartbeats 415000 -- thats about as far down as I can bring this

theorem ramsey_two.{u1, u2} (n : ℕ) : arrows_card (ℵ₀ : Cardinal.{u1}) (ℵ₀ : Cardinal.{u1}) n (2 : Cardinal.{u2}):= by
  rw [← lift_aleph0.{0, u1}]
  rw [← lift_two.{u2, 0}]
  apply arrows_card_lift
  induction n
  case zero => exact rathole_principle
  case succ n hn =>
    nth_rw 1 [← mk_nat]
    rw [← show ((2 : ℕ) : Cardinal) = 2 from rfl, ← mk_fin 2]
    apply arrows_card_of_arrows_type
    intro c

    have ih' (a : ℕ) (B : {A : Set ℕ // # A = ℵ₀}) : arrows_type (B.1 \ {b | b ≤ a} : Set ℕ) ℵ₀ n (Fin 2) := by
      apply hn
      · apply le_antisymm
        · exact mk_le_aleph0
        · by_contra neg
          simp at neg
          have thingy : {b | b ∈ B.1 ∧ b ≤ a}.Finite := by
            apply (finite_le_nat a).subset
            simp

          have that : B.1.Finite := by
            have : B.1 = {x | x ∈ B.1 ∧ a < x} ∪ {b | b ∈ B.1 ∧ b ≤ a} := by
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
          exact infinite_coe_iff.mp $ infinite_iff.mpr $ Eq.le (id B.2.symm)
      · exact mk_fin 2

    let f (a : ℕ) (A : Set ℕ) (Y : edges (A \ {b | b ≤ a} : Set ℕ) n) : edges ℕ (Nat.succ n) := ⟨insert a (Subtype.val '' Y.1), by
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

    let c' (a : ℕ) (A : Set ℕ) (Y : edges (A \ {b | b ≤ a} : Set ℕ) n ) := c $ f a A Y

    let mind (B : {A : Set ℕ // # A = ℵ₀}) : {a : ℕ // a ∈ B.1 ∧ ∀ b ∈ B.1, a ≤ b} := { --maybe find better name for "mind", right now this is just to avoid confusion with the usual minimum
      val := sInf B.1
      property := by
        constructor
        · apply Nat.sInf_mem
          apply nonempty_coe_sort.mp
          rw [← mk_ne_zero_iff, B.2]
          exact aleph0_ne_zero
        · exact fun b a ↦ Nat.sInf_le a
    }

    let h_next (B : {A : Set ℕ // # A = ℵ₀}) := ih' (mind B) B (c' (mind B) B.1)


    have next_inf (B : {A : Set ℕ // # A = ℵ₀}) : # (Subtype.val '' (h_next B).choose) = ℵ₀ := by
      conv_rhs => rw [← (h_next B).choose_spec.1]
      apply mk_image_eq Subtype.coe_injective

    let next (B : {A : Set ℕ // # A = ℵ₀}) : {A : Set ℕ // # A = ℵ₀} := ⟨Subtype.val '' (h_next B).choose, next_inf B⟩


    let sequence := seq' next

    have delete_or_fix (k : ℕ) : (sequence (k + 1)).1 = (next $ sequence k).1 := by rfl

    have h_rec (k : ℕ) := h_next $ sequence k

    let a (k : ℕ) : ℕ := mind $ sequence k

    have ha (k : ℕ) : a k ∈ (sequence k).1 := by
      exact (mind $ sequence k).2.1


    have h'_rec {k : ℕ} : (sequence (k + 1)).1 ⊆ (sequence k).1 \ {x | x ≤ a k} := by
      intro a ha
      obtain ⟨a', ha'⟩ := ha
      rw [← ha'.2]
      exact a'.2

    have sequence_monotone {a b : ℕ} (hab : a ≤ b) : (sequence b).1 ⊆ (sequence a).1 := by
      have {k l : ℕ} : (sequence $ k + l).1 ⊆ (sequence k) := by
        induction l
        case zero => trivial
        case succ m hm =>
          intro x hx
          apply hm (h'_rec hx).1

      obtain ⟨l, hl⟩ := le_iff_exists_add.mp hab
      rw [hl]
      exact this

    have a_mon : StrictMono a := by
      have ha₁ (k : ℕ) {b : ℕ} (hb : b ∈ (sequence (k + 1)).1) : a k < b := by
        specialize h'_rec hb
        have : ¬ b ≤ a k := by
          exact h'_rec.2
        exact Nat.not_le.mp this

      have ha₁' (k l : ℕ) (hl : 0 < l): a k < a (k + l) := by
        induction l
        case zero => trivial
        case succ m hm =>
          have : a k ≤ a (k + m) := by
            obtain left | right := Nat.eq_zero_or_pos m
            · rw [left]
              exact le_of_eq rfl
            · exact le_of_lt $ hm right
          apply lt_of_le_of_lt this
          exact ha₁ (k + m) (ha (k + m + 1))

      intro x y hxy
      obtain ⟨z, hz⟩ := lt_iff_exists_add.mp hxy
      rw [hz.2]
      apply ha₁' x z hz.1

    let i (k : ℕ) : Fin 2 := (h_rec k).choose_spec.2.choose
    let hi (k : ℕ) := (h_rec k).choose_spec.2.choose_spec

    have claim : ∃ colour : Fin 2, # (i ⁻¹' {colour}) = ℵ₀ := by
      rw [← mk_nat]
      apply Ordinal.infinite_pigeonhole
      · exact aleph0_le_mk ℕ
      · simp
        exact nat_lt_aleph0 2
    obtain ⟨colour, hcolour⟩ := claim

    let H := a '' (i ⁻¹' {colour})

    use H
    constructor
    · rw [← hcolour]
      exact mk_image_eq $ StrictMono.injective a_mon
    · use colour
      intro Y hY
      let k := sInf (a ⁻¹' Y.1)

      have ak_mem : a k ∈ Y.1 := by
        rw [← Set.mem_preimage]
        apply Nat.sInf_mem
        obtain ⟨y, hy⟩ := nonempty_of_succ_n
        obtain ⟨x, hx⟩ := hY hy
        use x
        rw [mem_preimage, hx.2]
        exact hy
              --       simp_rw [← yyyyyy]
              --       norm_num
              --       exact Cardinal.succ_ne_zero ↑n
              --     obtain ⟨y, hy⟩ := Y_nonempty
              --     obtain ⟨x, hx⟩ := hY hy
              --     use x
              --     rw [mem_preimage, hx.2]
              --     exact hy

      have k_min {b : ℕ} (hb : b ∈ Y.1) : a k ≤ b := by
        obtain ⟨l, hl⟩ := hY hb
        rw [← hl.2]
        apply a_mon.monotone
        apply Nat.sInf_le
        rw [←hl.2] at hb
        exact hb


      have that : c Y = i k := by
        have this' : Y.1 \ {a k} ⊆ (sequence (k + 1)).1 := by
          intro y hy
          obtain ⟨l, hl⟩ := hY hy.1
          have k_lt_l : k < l := by
            apply mono_backwards a_mon.monotone
            rw [hl.2]
            apply lt_of_le_of_ne
            · exact k_min hy.1
            · exact Ne.symm hy.2

          rw [←hl.2]
          exact sequence_monotone k_lt_l $ ha l
        have that : Y.1 \ {a k} ⊆ (sequence k).1 \ {b | b ≤ a k} := by
          apply subset_trans this' h'_rec

        let Y' : (edges ↑((sequence k).1 \ {b | b ≤ (mind $ sequence k).1}) ↑n) := {
          val := {y | y.1 ∈ Y.1 ∧ y.1 ≠ a k}
          property := by

            rw [← card_minus_one Y.2 ak_mem]

            let g (x : {y : ↑((sequence k).1 \ {b | b ≤ (mind $ sequence k).1}) | y.1 ∈ Y.1 ∧ y.1 ≠ a k})
                    : ↑(Y.1 \ {a k}) := ⟨x.1.1, x.2⟩
            have g_bij : g.Bijective := by
              constructor
              · intro x y hxy
                ext
                rw [Subtype.ext_iff] at hxy
                exact hxy

              · intro y
                use ⟨⟨y.1, that y.2⟩, y.2⟩

            exact card_eq_of_bijection g_bij
        }
        have hY' : Y'.1 ⊆ (h_next $ sequence k).choose := by
          intro y hy
          have dumsda : y.1 ∈ Y.1 \ {a k} := by
            exact hy
          specialize this' dumsda
          rw [delete_or_fix] at this'
          obtain ⟨x, hx⟩ := this'
          have x_eq_y : x = y := by
            ext
            exact hx.2
          rw [←x_eq_y]
          exact hx.1
        specialize hi k Y' hY'
        have dingsda : c' (a k) (sequence k).1 Y' = c Y := by
          simp
          congr
          ext x
          constructor
          · intro hx
            by_cases x = a k
            · rw [h]
              have claim : k ∈ a ⁻¹' Y.1 := by
                apply Nat.sInf_mem
                apply Set.Nonempty.preimage'
                · have : Nonempty Y.1 := by --TODO
                    rw [← mk_ne_zero_iff, Y.2]
                    exact NeZero.natCast_ne (Nat.succ n) Cardinal.{0}
                  apply nonempty_of_nonempty_subtype
                · apply subset_trans hY
                  simp
              exact claim
            · have claim := mem_of_mem_insert_of_ne hx h
              simp at claim
              obtain ⟨x',hx'⟩ := claim
              rw [← hx'.2.2]
              exact hx'.1.1
          · intro ha
            by_cases x = a k
            · rw [h]
              simp
            · apply mem_insert_of_mem
              specialize that ⟨ha, h⟩

              use ⟨x, that⟩
              constructor
              · constructor
                · exact ha
                · simp
                  simp at h
                  exact h
              · simp


        have : a k = (mind $ sequence k).1 := by rfl

        rw [← dingsda]
        rw [hi]

      rw [that]

      have : k ∈ a ⁻¹' Y.1 := by
        apply Nat.sInf_mem

        have Y_not_empty : Set.Nonempty Y.1 := by
          rw [← Set.nonempty_coe_sort, ← mk_ne_zero_iff, ← Cardinal.one_le_iff_ne_zero]
          have h : # Y.1 = n + 1 := by
            norm_cast
            exact Y.2
          rw [h]
          simp
        obtain ⟨x, hx⟩ := hY Y_not_empty.some_mem
        use x
        have : a x ∈ Y.1 := by
          rw [hx.2]
          exact Nonempty.some_mem Y_not_empty
        exact this
      have : k ∈ i ⁻¹' {colour} := by
        obtain ⟨x, hx⟩ := hY this
        rw [← a_mon.injective hx.2]
        exact hx.1
      exact this


set_option maxHeartbeats 200000


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

    let f (a : (Fin (Nat.succ m))) : (Fin 2) := if a < m then 0 else 1

    obtain ⟨H, hH⟩ := ramsey_two n ℕ (Fin 2) mk_nat (mk_fin 2) (f ∘ c)

    obtain ⟨i, hi⟩ := hH.2

    by_cases i = 0
    ·
      have {Y : edges ℕ n} (hY : Y.1 ⊆ H) : c Y < m := by
        specialize hi Y hY
        rw [h] at hi
        simp at hi
        exact Fin.not_le.mp hi

      have (Y : edges H n) : (c ⟨Subtype.val '' Y.1, edges_monotone Y⟩ : ℕ) < m := by
        have {Y : edges ℕ n} (hY : Y.1 ⊆ H) : (c Y : ℕ) < m := by
          by_contra neg
          simp at neg
          specialize hi Y hY
          rw [h] at hi
          simp at hi
          have hi := Fin.not_le.mp hi
          simp_rw [le_antisymm neg $ Fin.is_le (c Y), Fin.cast_val_eq_self (c Y)] at hi
          simp at hi


        apply this
        simp

      let c' (Y : edges H n) : Fin m := Fin.castLT (c ⟨Subtype.val '' Y.1, edges_monotone Y⟩) (this Y) -- this complains about "unused variables"

      rw [← mk_nat] at hH

      obtain ⟨H', hH'⟩ := hm H (Fin m) hH.1 rfl c' -- obviously c' is used though

      use Subtype.val '' H'
      constructor
      · rw [← hH'.1]
        exact mk_image_eq Subtype.coe_injective
      · obtain ⟨i', hi'⟩ := hH'.2
        use Fin.castLE (Nat.le_add_right m 1) i'
        intro Y hY
        ext
        simp

        have : Subtype.val ⁻¹' Y.1 ∈ edges H n := by
          have : n = # Y.1 := by exact Y.2.symm
          simp_rw [this]
          apply mk_preimage_of_injective_of_subset_range
          · exact Subtype.coe_injective
          · intro y hy
            obtain ⟨x, hx⟩ := hY hy
            use x
            exact hx.2

        have that : Subtype.val ⁻¹' Y.1 ⊆ H' := by
          intro x hx
          specialize hY hx
          simp at hY
          exact hY

        specialize hi' ⟨Subtype.val ⁻¹' Y.1, this⟩ that
        rw [← hi']
        simp
        have Y_sub_H : Y.1 ∩ H = Y.1 := by
          rw [Set.inter_eq_left]
          intro y hy
          obtain ⟨x, hx⟩ := hY hy
          rw [← hx.2]
          exact Subtype.mem x
        simp_rw [Y_sub_H]
    · have ieo : i = 1 := fin2_one_of_ne_zero h
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


example : ¬arrows_card (2^ℵ₀) 3 2 ℵ₀ := by

  have h₁ : 2 ^ ℵ₀ = # (ℕ → Fin 2) := by simp
  have h₂ : ℵ₀ = # ℕ := by simp

  rw [h₁, h₂]

  rw [← arrows_card_iff_arrows_type]

  intro h

  -- the usual way to proof this is to consider the coloring
  --    that colours a pair of (distinct) sequences with the least number such that the two disagree
  -- any homogenous set has size at most 2,
  --    since three different binary sequences cant disagree pairwise

  let c (Y : edges (ℕ → Fin 2) 2) : ℕ := sInf {k : ℕ | ∀ a ∈ Y.1, ∀ b ∈ Y.1, a ≠ b → a k ≠ b k}

  have hc (Y : edges (ℕ → Fin 2) 2) : c Y ∈ {k : ℕ | ∀ a ∈ Y.1, ∀ b ∈ Y.1, a ≠ b → a k ≠ b k} := by
    apply Nat.sInf_mem
    --by_contra neg

    --have := Set.not_nonempty_iff_eq_empty.mp neg

    obtain ⟨a, b, hab⟩ := Cardinal.mk_eq_two_iff.mp Y.2

    have a_neq_b : a.1 ≠ b.1 := by
      intro neg
      apply hab.1
      ext1
      exact neg


    have hY : Y.1 = {a.1,b.1} := by
      ext x
      constructor
      · intro hx
        simp
        have : ⟨x, hx⟩ ∈ ({a,b} : Set Y) := by
          rw [hab.2]
          trivial
        --simp at this
        obtain x_eq_a | x_eq_b := this
        · left
          rw [← x_eq_a]
        · right
          rw [← x_eq_b]
      · intro hx
        obtain x_eq_a | x_eq_b := hx
        · rw [x_eq_a]
          exact a.2
        · rw [x_eq_b]
          exact b.2

    --apply hab.1
    --ext k
    obtain ⟨k, hk⟩ := Function.ne_iff.mp a_neq_b
    use k
    intro x hx y hy hxy
    rw [hY] at hx hy
    obtain x_eq_a | x_eq_b := hx
    · subst x
      obtain y_eq_a | y_eq_b := hy
      · subst y
        simp at hxy
      · subst y
        exact hk
    · subst x
      obtain y_eq_a | y_eq_b := hy
      · subst y
        exact hk.symm
      · subst y
        simp at hxy



  obtain ⟨H, hH⟩ := h c

  obtain ⟨i, hi⟩ := hH.2

  let f (a : H) : Fin 2 := a.1 i

  have f_inj : f.Injective := by
    intro a b

    by_contra h
    push_neg at h

    have a_neq_b : a.1 ≠ b.1 := by
      intro neg
      apply h.2
      ext1
      exact neg

    let Y : Set (ℕ → Fin 2) := {a.1, b.1}

    have hY₁ : # Y = 2 := by
      simp_rw [←one_add_one_eq_two]
      have : a.1 ∉ ({b.1} : Set (ℕ → Fin 2)) := a_neq_b
      rw [mk_insert this]
      simp

    have hY₂ : c ⟨Y, hY₁⟩ = i := by
      have : Y ⊆ H := by
        intro x hx
        simp at hx
        obtain x_eq_a | x_eq_b := hx
        · rw [x_eq_a]
          exact a.2
        · rw [x_eq_b]
          exact b.2

      exact hi ⟨Y, hY₁⟩ this

    specialize hc ⟨Y, hY₁⟩ a.1 (mem_insert a.1 {b.1}) b.1 (mem_insert_of_mem (a.1) rfl) a_neq_b
    rw [hY₂] at hc
    simp at h
    exact hc h.1


  have : # (Fin 2) = 3 := by
    apply le_antisymm
    · simp
      norm_num
    · rw [← hH.1, le_def]
      use f

  simp at this

-- Everything below this line is the product of hubris

-- variable (κ : Cardinal.{0})
-- #check (ord κ).out

-- instance {o : WellOrder} [Infinite o.α] : InfSet o.α := sorry

-- instance {κ : Cardinal} {hκ : ℵ₀ ≤ κ}: LinearOrder ((ord κ).out.α → Fin 2) where
--   le a b := a = b ∨ a (sInf {x | a x ≠ b x}) < b ((sInf {x | a x ≠ b x}))
--   le_refl := by simp
--   le_trans a b c hab hbc := by
--     obtain a_eq_b | a_lt_b := hab
--     · rw [a_eq_b]
--       exact hbc
--     · obtain b_eq_c | b_lt_c := hbc
--       · rw [← b_eq_c]
--         right
--         exact a_lt_b
--       · right


--lemma to_be_named {κ : Cardinal} (hκ : ℵ₀ ≤ κ) : ¬∃

example {κ : Cardinal} : ¬arrows_card (2 ^ κ) (Order.succ κ) 2 2 := by
  sorry

-- this one is giving troubles with universes, abandon mission
-- example : ¬arrows_card (2 ^ aleph0) (aleph.{1} 1) 2 2 := by
--   have card_R : 2 ^ ℵ₀ = # ℝ := Cardinal.mk_real.symm
--   rw [card_R]

--   let omega₁ := ord.{0} $ aleph 1

--  have card_omega : aleph.{1} 1 = # omega₁ := by simp


noncomputable section --huh, this is needed for the definition of ℶ

open Ordinal


--Remark: The definition of beth numbers in mathlib is not entirely congruent with the one in the script I use
--  for our purposes α : ℕ actually suffices
-- different sources use different notation for the more general version of this function (for κ arbitrary)
-- while my direct source uses ℶ, wikipedia for example calls the general version of this function exp
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

-- also, this is more about being able to state it than proving it, since I value my sanity somewhat
theorem erdos_rado {n : ℕ} {κ : Cardinal} (hκ : ℵ₀ ≤ κ) :
    arrows_card (succ (ℶ κ n)) (succ κ) (n + 1) κ  := by
  induction n
  case zero =>
    simp
    rw [ℶ_zero]
    intro A B hA hB c

    let f (x : A) : (edges A 1) := ⟨{x}, by rw [edges]; simp⟩

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

    have hA' : succ κ ≤ # (edges A 1) := by
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

    let c' (a : A) (Y : edges ((univ : Set A) \ {a} : Set A) (n + 1)) := c ⟨insert a (Subtype.val '' Y.1), by
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

    have thingy {a : A} {B : Set A} {Y : edges A (n + 1)} (ha : a ∉ B) (hY : Y.1 ⊆ B) : Subtype.val ⁻¹' Y.1 ∈ edges ((Set.univ : Set A) \ {a} : Set A) (n + 1) := by
      have : # Y.1 = n + 1 := by exact Y.2
      simp_rw [← this]
      apply mk_preimage_of_injective_of_subset_range
      · exact Subtype.coe_injective
      · simp
        intro x hx
        intro hx'
        subst hx'
        exact ha $ hY hx

    have claim : ∃ A' : Set A, # A' = ℶ κ (n + 1) ∧ ∀ B : Set A, # B = ℶ κ n → ∀ b ∈ Bᶜ, ∃ a ∈ (A' \ B),
         ∀ Y : edges A (n + 1), Y.1 ⊆ B → c' a ⟨Subtype.val ⁻¹' Y.1, sorry⟩ = c' b ⟨Subtype.val ⁻¹' Y, sorry⟩ := sorry

    obtain ⟨X, hX⟩ := claim



    sorry

open Classical

--lemma inaccessible_of_union {c : Cardinal} (hc : ∀ c' : Cardinal, 0 < c' → c' < c → ∀ (A : c'.out → (Set c.out)), (∀ i, # (A i) < c) → (∀ i, ∀ j, i ≠ j → A i ∩ A j = ∅) → (⋃ i, A i) ≠ Set.univ) : c.IsInaccessible := by sorry

def weakly_compact.{u_1, u_2} (c : Cardinal) : Prop := (ℵ₀ < c) ∧ arrows_card.{u_1, u_2} c c 2 2
