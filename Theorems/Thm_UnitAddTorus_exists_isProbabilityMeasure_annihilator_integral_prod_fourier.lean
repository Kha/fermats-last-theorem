import Mathlib
import P2M.Util
import P2M.Sol.S_UnitAddTorus_exists_isProbabilityMeasure_annihilator_integral_prod_fourier

set_option autoImplicit false

open MeasureTheory

theorem UnitAddTorus.exists_isProbabilityMeasure_annihilator_integral_prod_fourier
    (d : ℕ) (Q : AddSubgroup (Fin d → ℤ)) :
    ∃ m : Measure (Fin d → AddCircle (1 : ℝ)), IsProbabilityMeasure m ∧
      m {θ : Fin d → AddCircle (1 : ℝ) | ∀ q ∈ Q, (∏ i, fourier (q i) (θ i)) = 1}ᶜ = 0 ∧
      (∀ n : Fin d → ℤ, n ∈ Q → ∫ θ, (∏ i, fourier (n i) (θ i)) ∂m = 1) ∧
      (∀ n : Fin d → ℤ, n ∉ Q → ∫ θ, (∏ i, fourier (n i) (θ i)) ∂m = 0) ∧
      ({θ : Fin d → AddCircle (1 : ℝ) | ∀ q ∈ Q, (∏ i, fourier (q i) (θ i)) = 1}.Infinite →
        ∀ θ : Fin d → AddCircle (1 : ℝ), m {θ} = 0) := by p2m_exact_reverting @_root_.P2MW.S_UnitAddTorus_exists_isProbabilityMeasure_annihilator_integral_prod_fourier.solution
