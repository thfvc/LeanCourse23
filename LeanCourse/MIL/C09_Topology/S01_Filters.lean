import LeanCourse.Common
import Mathlib.Topology.Instances.Real

open Set Filter Topology

def principal {α : Type*} (s : Set α) : Filter α
    where
  sets := { t | s ⊆ t }
  univ_sets := by simp
  sets_of_superset := by
    simp
    intro x y hx hy
    exact Subset.trans hx hy
  inter_sets := by
    simp
    intro x y hx hy
    exact ⟨hx, hy⟩

example : Filter ℕ :=
  { sets := { s | ∃ a, ∀ b, a ≤ b → b ∈ s }
    univ_sets := by simp
    sets_of_superset := by
      simp
      intro x y a hx hy
      use a
      intro b hb
      apply hy
      specialize hx b hb
      exact hx
    inter_sets := by
      simp
      intro x₁ x₂ a₁ hx₁ a₂ hx₂
      use max a₁ a₂
      intro b hb
      constructor
      · exact hx₁ b $ le_of_max_le_left hb
      · exact hx₂ b $ le_of_max_le_right hb
     }

def Tendsto₁ {X Y : Type*} (f : X → Y) (F : Filter X) (G : Filter Y) :=
  ∀ V ∈ G, f ⁻¹' V ∈ F

def Tendsto₂ {X Y : Type*} (f : X → Y) (F : Filter X) (G : Filter Y) :=
  map f F ≤ G

example {X Y : Type*} (f : X → Y) (F : Filter X) (G : Filter Y) :
    Tendsto₂ f F G ↔ Tendsto₁ f F G :=
  Iff.rfl

#check (@Filter.map_mono : ∀ {α β} {m : α → β}, Monotone (map m))

#check
  (@Filter.map_map :
    ∀ {α β γ} {f : Filter α} {m : α → β} {m' : β → γ}, map m' (map m f) = map (m' ∘ m) f)

example {X Y Z : Type*} {F : Filter X} {G : Filter Y} {H : Filter Z} {f : X → Y} {g : Y → Z}
    (hf : Tendsto₁ f F G) (hg : Tendsto₁ g G H) : Tendsto₁ (g ∘ f) F H := by
    intro V hV
    specialize hg V hV
    specialize hf (g ⁻¹' V) hg
    exact hf


variable (f : ℝ → ℝ) (x₀ y₀ : ℝ)

#check comap ((↑) : ℚ → ℝ) (𝓝 x₀)

#check Tendsto (f ∘ (↑)) (comap ((↑) : ℚ → ℝ) (𝓝 x₀)) (𝓝 y₀)

section
variable {α β γ : Type*} (F : Filter α) {m : γ → β} {n : β → α}

#check (comap_comap : comap m (comap n F) = comap (n ∘ m) F)

end

example : 𝓝 (x₀, y₀) = 𝓝 x₀ ×ˢ 𝓝 y₀ :=
  nhds_prod_eq

#check le_inf_iff

example (f : ℕ → ℝ × ℝ) (x₀ y₀ : ℝ) :
    Tendsto f atTop (𝓝 (x₀, y₀)) ↔
      Tendsto (Prod.fst ∘ f) atTop (𝓝 x₀) ∧ Tendsto (Prod.snd ∘ f) atTop (𝓝 y₀) := by
    constructor
    · intro h
      constructor
      · intro V hV
        let U : Set (ℝ × ℝ) := V ×ˢ (univ)
        have : U ∈ 𝓝 (x₀, y₀) := by
          rw [nhds_prod_eq]
          simp
          exact hV

        simp
        specialize h this
        simp at h
        obtain ⟨a, ha⟩ := h
        use a

      · intro V hV
        let U : Set (ℝ × ℝ) := univ ×ˢ V
        have : U ∈ 𝓝 (x₀, y₀) := by
          rw [nhds_prod_eq]
          simp
          exact hV
        simp
        specialize h this
        simp at h
        obtain ⟨a, ha⟩ := h
        use a
    · intro h
      intro V hV
      let h1 := h.1
      let h2 := h.2
      let V1 := {x | ∃ y : ℝ, (x,y) ∈ V}
      let V2 := {y | ∃ x : ℝ, (x,y) ∈ V}
      have V1V2subV : V ⊆ V1 ×ˢ V2 := by
        intro (x,y) hxy
        simp
        constructor
        · use y
        · use x

      have hV1V2 : V1 ×ˢ V2 ∈ 𝓝 (x₀,y₀) := by
        exact mem_of_superset hV V1V2subV
      have hV1 : V1 ∈ 𝓝 x₀ := by sorry
      have hV2 : V2 ∈ 𝓝 y₀ := by sorry

      specialize h1 hV1
      specialize h2 hV2
      simp
      simp at h1
      simp at h2
      obtain ⟨n₁, hn₁⟩ := h1
      obtain ⟨n₂, hn₂⟩ := h2
      use max n₁ n₂
      intro b hb
      sorry




example (x₀ : ℝ) : HasBasis (𝓝 x₀) (fun ε : ℝ ↦ 0 < ε) fun ε ↦ Ioo (x₀ - ε) (x₀ + ε) :=
  nhds_basis_Ioo_pos x₀

example (u : ℕ → ℝ) (x₀ : ℝ) :
    Tendsto u atTop (𝓝 x₀) ↔ ∀ ε > 0, ∃ N, ∀ n ≥ N, u n ∈ Ioo (x₀ - ε) (x₀ + ε) := by
  have : atTop.HasBasis (fun _ : ℕ ↦ True) Ici := atTop_basis
  rw [this.tendsto_iff (nhds_basis_Ioo_pos x₀)]
  simp

example (P Q : ℕ → Prop) (hP : ∀ᶠ n in atTop, P n) (hQ : ∀ᶠ n in atTop, Q n) :
    ∀ᶠ n in atTop, P n ∧ Q n :=
  hP.and hQ

example (u v : ℕ → ℝ) (h : ∀ᶠ n in atTop, u n = v n) (x₀ : ℝ) :
    Tendsto u atTop (𝓝 x₀) ↔ Tendsto v atTop (𝓝 x₀) :=
  tendsto_congr' h

example (u v : ℕ → ℝ) (h : u =ᶠ[atTop] v) (x₀ : ℝ) :
    Tendsto u atTop (𝓝 x₀) ↔ Tendsto v atTop (𝓝 x₀) :=
  tendsto_congr' h

#check eventually_of_forall
#check Eventually.mono
#check Eventually.and

example (P Q R : ℕ → Prop) (hP : ∀ᶠ n in atTop, P n) (hQ : ∀ᶠ n in atTop, Q n)
    (hR : ∀ᶠ n in atTop, P n ∧ Q n → R n) : ∀ᶠ n in atTop, R n := by
  apply (hP.and (hQ.and hR)).mono
  rintro n ⟨h, h', h''⟩
  exact h'' ⟨h, h'⟩

example (P Q R : ℕ → Prop) (hP : ∀ᶠ n in atTop, P n) (hQ : ∀ᶠ n in atTop, Q n)
    (hR : ∀ᶠ n in atTop, P n ∧ Q n → R n) : ∀ᶠ n in atTop, R n := by
  filter_upwards [hP, hQ, hR] with n h h' h''
  exact h'' ⟨h, h'⟩

#check mem_closure_iff_clusterPt
#check le_principal_iff
#check neBot_of_le

example (u : ℕ → ℝ) (M : Set ℝ) (x : ℝ) (hux : Tendsto u atTop (𝓝 x))
    (huM : ∀ᶠ n in atTop, u n ∈ M) : x ∈ closure M :=
  sorry
