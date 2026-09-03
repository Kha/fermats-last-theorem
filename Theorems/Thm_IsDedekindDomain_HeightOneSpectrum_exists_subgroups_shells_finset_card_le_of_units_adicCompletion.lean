import Definitions.Def_NumberField_AdelicHaar
import P2M.Util
import P2M.Sol.S_IsDedekindDomain_HeightOneSpectrum_exists_subgroups_shells_finset_card_le_of_units_adicCompletion

set_option autoImplicit false

open IsDedekindDomain NumberField

theorem IsDedekindDomain.HeightOneSpectrum.exists_subgroups_shells_finset_card_le_of_units_adicCompletion
    (K : Type) [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K)) (n₀ c : ℕ) (hn₀ : 1 ≤ n₀) (hc : 1 ≤ c) :
    ∃ (U₁ A : Subgroup (v.adicCompletion K)ˣ) (V : ℕ → Subgroup (v.adicCompletion K)ˣ) (sh : ℕ → Set (v.adicCompletion K)ˣ) (M₀ : ℕ),
      IsOpen (U₁ : Set (v.adicCompletion K)ˣ) ∧ IsCompact (U₁ : Set (v.adicCompletion K)ˣ) ∧
      IsOpen (A : Set (v.adicCompletion K)ˣ) ∧ IsCompact (A : Set (v.adicCompletion K)ˣ) ∧
      (∀ k, IsOpen (V k : Set (v.adicCompletion K)ˣ)) ∧ (∀ k, V k ≤ U₁) ∧ (∀ k, V k ≤ A) ∧
      (∀ t : (v.adicCompletion K)ˣ, t ∈ U₁ ↔ ‖(t : (v.adicCompletion K)) - 1‖ ≤ (Ideal.absNorm v.asIdeal : ℝ) ^ (-(n₀ : ℤ))) ∧
      (∀ a : (v.adicCompletion K)ˣ, a ∈ A ↔ ‖(a : (v.adicCompletion K)) - 1‖ ≤ (Ideal.absNorm v.asIdeal : ℝ) ^ (-(c : ℤ))) ∧
      (∀ (k : ℕ) (τ : (v.adicCompletion K)ˣ), τ ∈ V k ↔
        ‖(τ : (v.adicCompletion K)) - 1‖ ≤ (Ideal.absNorm v.asIdeal : ℝ) ^ (-((k + n₀ + c : ℕ) : ℤ))) ∧
      (∀ (k : ℕ) (t : (v.adicCompletion K)ˣ), t ∈ sh k ↔
        ‖(1 : (v.adicCompletion K)) - (t : (v.adicCompletion K))‖ = (Ideal.absNorm v.asIdeal : ℝ) ^ (-((k + n₀ : ℕ) : ℤ))) ∧
      (∀ t : (v.adicCompletion K)ˣ, t ∈ U₁ → ‖(t : (v.adicCompletion K))‖ = 1) ∧
      (∀ k, IsCompact (sh k)) ∧ (∀ k, sh k ⊆ (U₁ : Set (v.adicCompletion K)ˣ)) ∧ (∀ k, (1 : (v.adicCompletion K)ˣ) ∉ sh k) ∧
      (Pairwise fun k k' => Disjoint (sh k) (sh k')) ∧
      (∀ t : (v.adicCompletion K)ˣ, t ∈ U₁ → t ≠ 1 → ∃ k, t ∈ sh k) ∧
      (∀ k, ∀ t ∈ sh k, ∀ τ ∈ V k, t * τ ∈ sh k) ∧
      (∀ k, ∃ Ft : Finset (v.adicCompletion K)ˣ, Ft.card ≤ M₀ ∧ (↑Ft ⊆ sh k) ∧
        (∀ τ ∈ Ft, ∀ τ' ∈ Ft, τ ≠ τ' → τ⁻¹ * τ' ∉ V k) ∧
        ∀ t ∈ sh k, ∃ τ ∈ Ft, t⁻¹ * τ ∈ V k) ∧
      (∀ S : Set (v.adicCompletion K)ˣ, IsCompact S → ∃ Fa : Finset (v.adicCompletion K)ˣ,
        (∀ α ∈ Fa, ∀ α' ∈ Fa, α ≠ α' → α⁻¹ * α' ∉ A) ∧ ∀ a ∈ S, ∃ α ∈ Fa, a⁻¹ * α ∈ A) := by p2m_exact_reverting @_root_.P2MW.S_IsDedekindDomain_HeightOneSpectrum_exists_subgroups_shells_finset_card_le_of_units_adicCompletion.solution
