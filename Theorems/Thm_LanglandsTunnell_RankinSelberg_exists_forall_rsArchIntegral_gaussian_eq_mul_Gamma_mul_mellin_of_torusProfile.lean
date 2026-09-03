import Definitions.Def_LanglandsTunnell_RSCarrier
import Definitions.Def_LanglandsTunnell_RSCarrierSplit
import Definitions.Def_AutomorphicForm_SiegelCoordinates
import Definitions.Def_AutomorphicForm_RowIsometryInvariance
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import P2M.Util
import P2M.Sol.S_LanglandsTunnell_RankinSelberg_exists_forall_rsArchIntegral_gaussian_eq_mul_Gamma_mul_mellin_of_torusProfile

set_option autoImplicit false

open MeasureTheory AutomorphicForm AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCoordinates RSCarrier

theorem LanglandsTunnell.RankinSelberg.exists_forall_rsArchIntegral_gaussian_eq_mul_Gamma_mul_mellin_of_torusProfile
    :
    letI : MeasurableSpace (GL (Fin 2) ℝ) := borel _
    ∀ (_hHaar : RSCarrier.archMeasure.IsHaarMeasure)
      (μN : Measure realUnipotent) [μN.IsHaarMeasure],
    ∃ C' : ℝ, 0 < C' ∧
      ∀ (W W' : GL (Fin 2) ℝ → ℂ) (P : ℝ → ℝ) (x₀ : ℝ)
        (_hW : Measurable W) (_hW' : Measurable W') (_hP : Measurable P)
        (_hN : ∀ n ∈ realUnipotent, ∀ g : GL (Fin 2) ℝ, W (n * g) * W' (n * g) = W g * W' g)
        (_hK : ∀ κ ∈ rowIsometrySubgroup ℝ, Matrix.GeneralLinearGroup.det κ = 1 →
          ∀ g : GL (Fin 2) ℝ, W (g * κ) * W' (g * κ) = W g * W' g)
        (_hT : ∀ (a₁ a₂ : ℝ) (h₁ : a₁ ≠ 0) (h₂ : 0 < a₂),
          W (upperUnit a₁ 0 a₂ h₁ h₂.ne') * W' (upperUnit a₁ 0 a₂ h₁ h₂.ne') = ((P (a₁ / a₂) : ℝ) : ℂ))
        (_hP0 : ∀ y : ℝ, 0 ≤ P y)
        (_hPne : ¬ (∀ᵐ y : ℝ, P y = 0))
        (_hPint : ∀ σ : ℝ, x₀ < σ → Integrable (fun y : ℝ => P y * |y| ^ (σ - 2))),
      ∃ M : ℂ → ℂ,
        AnalyticOnNhd ℂ M {s : ℂ | x₀ < s.re} ∧
        (∀ σ : ℝ, x₀ < σ → (M σ).im = 0 ∧ 0 < (M σ).re) ∧
        (∀ s : ℂ, x₀ < s.re → M s = ∫ y : ℝ, ((P y : ℝ) : ℂ) * ((|y| : ℝ) : ℂ) ^ (s - 2)) ∧
        ∀ s : ℂ, 0 < s.re →
          Integrable
            (fun g : GL (Fin 2) ℝ =>
              (W g * (W' g * Complex.exp (-(Real.pi *
                  (((g : Matrix (Fin 2) (Fin 2) ℝ) 1 0) ^ 2 + ((g : Matrix (Fin 2) (Fin 2) ℝ) 1 1) ^ 2) : ℝ)))) *
                (((|(Matrix.GeneralLinearGroup.det g : ℝ)| : ℝ) : ℂ) ^ (s + 1 / 2 - 1 / 2)))
            (RSCarrier.archMeasure.withDensity (HaarQuotient.density realUnipotent μN)) →
          rsArchIntegral RSCarrier.archMeasure μN (s + 1 / 2) W
              (fun g : GL (Fin 2) ℝ => W' g * Complex.exp (-(Real.pi *
                  (((g : Matrix (Fin 2) (Fin 2) ℝ) 1 0) ^ 2 + ((g : Matrix (Fin 2) (Fin 2) ℝ) 1 1) ^ 2) : ℝ))) =
            (C' : ℂ) * ((1 / 2 : ℂ) * (Real.pi : ℂ) ^ (-s) * Complex.Gamma s) * M s := by p2m_exact_reverting @_root_.P2MW.S_LanglandsTunnell_RankinSelberg_exists_forall_rsArchIntegral_gaussian_eq_mul_Gamma_mul_mellin_of_torusProfile.solution
