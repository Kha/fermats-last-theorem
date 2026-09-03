import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Complex.Log
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Topology.Compactness.LocallyCompact
import P2M.Util
import P2M.Sol.S_RegularSingular_exists_twoLevel_coeff_of_transport_of_slice_expansion

set_option autoImplicit false

theorem RegularSingular.exists_twoLevel_coeff_of_transport_of_slice_expansion
    {P : Type*} [TopologicalSpace P] [LocallyCompactSpace P] [FirstCountableTopology P]
    {n J : ℕ} (e : Fin n → ℂ) (he : Function.Injective e) (ρ δ : ℝ) (hδ : 0 < δ)
    (hre : ∀ i, (e i).re ≤ ρ)
    (hcl : ∀ i (k : ℕ), (e i + k).re ≤ ρ → ∃ i', e i' = e i + k)
    (hgap : ∀ i (k : ℕ), ρ < (e i + k).re → ρ + 2 * δ ≤ (e i + k).re)
    (S : Set P) (W : ℝ → ℝ → P → ℂ)
    (hWc : ContinuousOn (fun w : ℝ × ℝ × P => W w.1 w.2.1 w.2.2) (Set.Ioi 0 ×ˢ Set.Ioi 0 ×ˢ Set.univ))
    (htrans : ∀ K : Set P, IsCompact K → ∃ (lam₀ nB Ω : ℝ) (K₀ : Set P), 0 < lam₀ ∧ lam₀ ≤ 1 ∧ 0 ≤ nB ∧
      0 ≤ Ω ∧ IsCompact K₀ ∧ K₀ ⊆ S ∧ ∀ g ∈ K, ∃ (lam τ n₁ n₂ : ℝ) (κ₁ : ℂ) (k' : P), k' ∈ K₀ ∧
        lam₀ ≤ lam ∧ lam ≤ lam₀⁻¹ ∧ lam₀ ≤ τ ∧ τ ≤ lam₀⁻¹ ∧ |n₁| ≤ nB ∧ |n₂| ≤ nB ∧ ‖κ₁‖ ≤ Ω ∧
        ∀ y₁ y₂ : ℝ, 0 < y₁ → 0 < y₂ →
          W y₁ y₂ g = κ₁ * Complex.exp (2 * Real.pi * Complex.I * ((y₁ * n₁ + y₂ * n₂ : ℝ) : ℂ)) *
            W (lam * y₁) (τ * y₂) k')
    (hslice : ∀ K₀ : Set P, IsCompact K₀ → K₀ ⊆ S → ∀ Z : ℝ, 2 ≤ Z →
      ∃ (m C : ℝ) (cS : Fin n → Fin J → ℝ → P → ℂ) (c₂ : Fin n → Fin J → Fin n → Fin J → P → ℂ),
        (∀ k ∈ K₀, ∀ i j i' j', ‖c₂ i j i' j' k‖ ≤ C) ∧
        (∀ k ∈ K₀, ∀ z ∈ Set.Ioc (0 : ℝ) Z, ∀ i j, ‖cS i j z k‖ ≤ C * z ^ (-m)) ∧
        (∀ k ∈ K₀, ∀ z ∈ Set.Ioc (0 : ℝ) Z, ∀ y ∈ Set.Ioc (0 : ℝ) 1,
          ‖W y z k - ∑ i : Fin n, ∑ j : Fin J,
              cS i j z k * ((y : ℂ) ^ e i * ((Real.log y : ℝ) : ℂ) ^ (j : ℕ))‖ ≤ C * z ^ (-m) * y ^ (ρ + δ)) ∧
        (∀ k ∈ K₀, ∀ i j, ∀ z ∈ Set.Ioc (0 : ℝ) 1,
          ‖cS i j z k - ∑ i' : Fin n, ∑ j' : Fin J,
              c₂ i j i' j' k * ((z : ℂ) ^ e i' * ((Real.log z : ℝ) : ℂ) ^ (j' : ℕ))‖ ≤ C * z ^ (ρ + δ))) :
    ∃ c : Fin n → Fin J → ℝ → P → ℂ,
      (∀ i j, ContinuousOn (fun p : ℝ × P => c i j p.1 p.2) {p | 0 < p.1}) ∧
      (∀ K : Set P, IsCompact K → ∀ b : ℝ, 1 ≤ b → ∃ C : ℝ, ∀ k ∈ K, ∀ y₂ : ℝ, b⁻¹ ≤ y₂ → y₂ ≤ b →
        ∀ y₁ : ℝ, 0 < y₁ → y₁ ≤ 1 →
        ‖W y₁ y₂ k - ∑ i : Fin n, ∑ j : Fin J,
            c i j y₂ k * ((y₁ : ℂ) ^ e i * ((Real.log y₁ : ℝ) : ℂ) ^ (j : ℕ))‖ ≤ C * y₁ ^ (ρ + δ)) ∧
      ∃ c' : Fin n → Fin J → Fin n → Fin J → P → ℂ,
        (∀ i j i' j', Continuous (c' i j i' j')) ∧
        ∀ K : Set P, IsCompact K → ∃ C : ℝ, ∀ k ∈ K, ∀ (i : Fin n) (j : Fin J), ∀ y₂ : ℝ, 0 < y₂ → y₂ ≤ 1 →
          ‖c i j y₂ k - ∑ i' : Fin n, ∑ j' : Fin J,
              c' i j i' j' k * ((y₂ : ℂ) ^ e i' * ((Real.log y₂ : ℝ) : ℂ) ^ (j' : ℕ))‖ ≤ C * y₂ ^ (ρ + δ) := by p2m_exact_reverting @_root_.P2MW.S_RegularSingular_exists_twoLevel_coeff_of_transport_of_slice_expansion.solution
