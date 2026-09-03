import Mathlib
import P2M.Util
import P2M.Sol.S_LocalParametrix_exists_continuous_hasCompactSupport_invariant_apply_eq_integral_add_integral_of_compactSpace

set_option autoImplicit false

open MeasureTheory Topology

theorem LocalParametrix.exists_continuous_hasCompactSupport_invariant_apply_eq_integral_add_integral_of_compactSpace
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E] (μ : Measure E) [μ.IsAddHaarMeasure]
    {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
    (ρ : G →* (E →L[ℝ] E)) (hρ : Continuous fun p : G × E => ρ p.1 p.2)
    (x₀ : E) (hx₀ : ∀ k : G, ρ k x₀ = x₀)
    (D : (E → ℂ) → (E → ℂ))
    (hDc : ∀ F : E → ℂ, ContDiff ℝ (⊤ : ℕ∞) F → HasCompactSupport F → Continuous (D F))
    (hDρ : ∀ (k : G) (F : E → ℂ), ContDiff ℝ (⊤ : ℕ∞) F → HasCompactSupport F →
      D (fun x => F (ρ k x)) = fun x => D F (ρ k x))
    (hex : ∀ W ∈ 𝓝 x₀, ∃ g₁ g₂ : E → ℂ, Continuous g₁ ∧ Continuous g₂ ∧
      HasCompactSupport g₁ ∧ HasCompactSupport g₂ ∧ tsupport g₁ ⊆ W ∧ tsupport g₂ ⊆ W ∧
      ∀ F : E → ℂ, ContDiff ℝ (⊤ : ℕ∞) F → HasCompactSupport F →
        F x₀ = (∫ x, D F x * g₁ x ∂μ) + ∫ x, F x * g₂ x ∂μ)
    (V : Set E) (hV : V ∈ 𝓝 x₀) :
    ∃ g₁ g₂ : E → ℂ, Continuous g₁ ∧ Continuous g₂ ∧
      HasCompactSupport g₁ ∧ HasCompactSupport g₂ ∧ tsupport g₁ ⊆ V ∧ tsupport g₂ ⊆ V ∧
      (∀ (k : G) (x : E), g₁ (ρ k x) = g₁ x) ∧ (∀ (k : G) (x : E), g₂ (ρ k x) = g₂ x) ∧
      ∀ F : E → ℂ, ContDiff ℝ (⊤ : ℕ∞) F → HasCompactSupport F →
        F x₀ = (∫ x, D F x * g₁ x ∂μ) + ∫ x, F x * g₂ x ∂μ := by p2m_exact_reverting @_root_.P2MW.S_LocalParametrix_exists_continuous_hasCompactSupport_invariant_apply_eq_integral_add_integral_of_compactSpace.solution
