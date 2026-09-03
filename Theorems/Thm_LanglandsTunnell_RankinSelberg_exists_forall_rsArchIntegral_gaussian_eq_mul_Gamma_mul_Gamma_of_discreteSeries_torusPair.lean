import Definitions.Def_LanglandsTunnell_RSCarrier
import Definitions.Def_LanglandsTunnell_RSCarrierSplit
import Definitions.Def_AutomorphicForm_SiegelCoordinates
import Definitions.Def_AutomorphicForm_RowIsometryInvariance
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import P2M.Util
import P2M.Sol.S_LanglandsTunnell_RankinSelberg_exists_forall_rsArchIntegral_gaussian_eq_mul_Gamma_mul_Gamma_of_discreteSeries_torusPair

set_option autoImplicit false

open MeasureTheory AutomorphicForm AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCoordinates RSCarrier

theorem LanglandsTunnell.RankinSelberg.exists_forall_rsArchIntegral_gaussian_eq_mul_Gamma_mul_Gamma_of_discreteSeries_torusPair :
    letI : MeasurableSpace (GL (Fin 2) ℝ) := borel _
    ∀ (_hHaar : RSCarrier.archMeasure.IsHaarMeasure)
      (μN : Measure realUnipotent) [μN.IsHaarMeasure],
    ∃ C' : ℝ, 0 < C' ∧
      ∀ (k : ℕ) (_hk : 1 ≤ k) (C : ℂ) (W W' : GL (Fin 2) ℝ → ℂ)
        (_hW : Measurable W) (_hW' : Measurable W')
        (_hN : ∀ n ∈ realUnipotent, ∀ g : GL (Fin 2) ℝ, W (n * g) * W' (n * g) = W g * W' g)
        (_hK : ∀ κ ∈ rowIsometrySubgroup ℝ, Matrix.GeneralLinearGroup.det κ = 1 →
          ∀ g : GL (Fin 2) ℝ, W (g * κ) * W' (g * κ) = W g * W' g)
        (_hT : ∀ (a₁ a₂ : ℝ) (h₁ : a₁ ≠ 0) (h₂ : 0 < a₂),
          W (upperUnit a₁ 0 a₂ h₁ h₂.ne') * W' (upperUnit a₁ 0 a₂ h₁ h₂.ne') =
            if 0 < a₁ then C * (((a₁ / a₂ : ℝ) : ℂ) ^ k * Complex.exp (-(4 * Real.pi * (a₁ / a₂) : ℝ))) else 0)
        (σ₀ : ℝ) (_hσ₀ : 0 ≤ σ₀)
        (_hint : ∀ s : ℂ, σ₀ < s.re → Integrable
          (fun g : GL (Fin 2) ℝ =>
            (W g * (W' g * Complex.exp (-(Real.pi *
                (((g : Matrix (Fin 2) (Fin 2) ℝ) 1 0) ^ 2 + ((g : Matrix (Fin 2) (Fin 2) ℝ) 1 1) ^ 2) : ℝ)))) *
              (((|(Matrix.GeneralLinearGroup.det g : ℝ)| : ℝ) : ℂ) ^ (s + 1 / 2 - 1 / 2)))
          (RSCarrier.archMeasure.withDensity (HaarQuotient.density realUnipotent μN))),
      ∀ s : ℂ, σ₀ < s.re →
        rsArchIntegral RSCarrier.archMeasure μN (s + 1 / 2) W
            (fun g : GL (Fin 2) ℝ => W' g * Complex.exp (-(Real.pi *
                (((g : Matrix (Fin 2) (Fin 2) ℝ) 1 0) ^ 2 + ((g : Matrix (Fin 2) (Fin 2) ℝ) 1 1) ^ 2) : ℝ))) =
          (C' : ℂ) * C * ((4 * (Real.pi : ℂ)) ^ (-(s + (k : ℂ) - 1)) * Complex.Gamma (s + (k : ℂ) - 1)) *
            ((Real.pi : ℂ) ^ (-s) * Complex.Gamma s) := by p2m_exact_reverting @_root_.P2MW.S_LanglandsTunnell_RankinSelberg_exists_forall_rsArchIntegral_gaussian_eq_mul_Gamma_mul_Gamma_of_discreteSeries_torusPair.solution
