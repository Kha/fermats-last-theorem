import Definitions.Def_LanglandsTunnell_RSCarrier
import Definitions.Def_LanglandsTunnell_RSCarrierSplit
import Definitions.Def_AutomorphicForm_SiegelCoordinates
import Definitions.Def_AutomorphicForm_RowIsometryInvariance
import P2M.Util
import P2M.Sol.S_LanglandsTunnell_Converse_exists_const_rsArchIntegral_eq_mul_integral_diagonal

set_option autoImplicit false

open MeasureTheory AutomorphicForm AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCoordinates RSCarrier

theorem LanglandsTunnell.Converse.exists_const_rsArchIntegral_eq_mul_integral_diagonal :
    letI : MeasurableSpace (GL (Fin 2) ℝ) := borel _
    ∀ (_hHaar : RSCarrier.archMeasure.IsHaarMeasure),
    ∃ c : ℝ, 0 < c ∧
      ∀ (μN : Measure realUnipotent) [μN.IsHaarMeasure] (s : ℂ) (W F : GL (Fin 2) ℝ → ℂ)
        (_hN : ∀ n ∈ realUnipotent, ∀ g : GL (Fin 2) ℝ, W (n * g) * F (n * g) = W g * F g)
        (_hK : ∀ k ∈ rowIsometrySubgroup ℝ, Matrix.GeneralLinearGroup.det k = 1 →
          ∀ g : GL (Fin 2) ℝ, W (g * k) * F (g * k) = W g * F g)
        (_hW : Measurable W) (_hF : Measurable F)
        (_hint : Integrable
          (fun g : GL (Fin 2) ℝ =>
            (W g * F g) * (((|(Matrix.GeneralLinearGroup.det g : ℝ)| : ℝ) : ℂ) ^ (s - 1 / 2)))
          (RSCarrier.archMeasure.withDensity (HaarQuotient.density realUnipotent μN))),
        rsArchIntegral RSCarrier.archMeasure μN s W F =
          ((c / (μN {n : realUnipotent |
              ((n : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) 0 1 ∈ Set.Icc (0 : ℝ) 1}).toReal : ℝ) : ℂ) *
            ∫ a₂ in Set.Ioi (0 : ℝ), ∫ a₁ : ℝ,
              if h : a₁ ≠ 0 ∧ 0 < a₂ then
                let p : GL (Fin 2) ℝ := upperUnit a₁ 0 a₂ h.1 h.2.ne'
                ((W p * F p) * (((|(Matrix.GeneralLinearGroup.det p : ℝ)| : ℝ) : ℂ) ^ (s - 1 / 2))) *
                  (((a₁ ^ 2)⁻¹ : ℝ) : ℂ)
              else 0 := by p2m_exact_reverting @_root_.P2MW.S_LanglandsTunnell_Converse_exists_const_rsArchIntegral_eq_mul_integral_diagonal.solution
