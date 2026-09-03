import Definitions.Def_LanglandsTunnell_RSCarrier
import Definitions.Def_LanglandsTunnell_RSCarrierSplit
import Definitions.Def_NumberField_AdelicLevel
import Definitions.Def_AutomorphicForm_SiegelCoordinates
import Definitions.Def_AutomorphicForm_RowIsometryInvariance
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import P2M.Util
import P2M.Sol.S_LanglandsTunnell_RankinSelberg_mul_conj_mul_abs_det_rpow_upperUnit_eq_abs_rpow_mul_norm_sq_of_diagOne_eq

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicLevel AutomorphicForm AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCoordinates RSCarrier

theorem LanglandsTunnell.RankinSelberg.mul_conj_mul_abs_det_rpow_upperUnit_eq_abs_rpow_mul_norm_sq_of_diagOne_eq
    (WA : GL (Fin 2) ℝ → ℂ) (χ : ℝˣ → ℂ) (Wr : ℝ → ℂ) (e : ℝ)
    (hχ : ∀ z : ℝˣ, ‖χ z‖ = |(z : ℝ)| ^ e)
    (hZ : ∀ (z : ℝˣ) (h : GL (Fin 2) ℝ), WA (Matrix.GeneralLinearGroup.scalar (Fin 2) z * h) = χ z * WA h)
    (hdiag : ∀ t : ℝˣ, WA (diagOne t) = Wr (t : ℝ)) :
    ∀ (a₁ a₂ : ℝ) (h₁ : a₁ ≠ 0) (h₂ : 0 < a₂),
      WA (upperUnit a₁ 0 a₂ h₁ h₂.ne') *
          ((starRingEnd ℂ) (WA (upperUnit a₁ 0 a₂ h₁ h₂.ne')) * (((|a₁ * a₂| ^ (-e) : ℝ) : ℝ) : ℂ)) =
        (((|a₁ / a₂| ^ (-e) * ‖Wr (a₁ / a₂)‖ ^ 2 : ℝ) : ℝ) : ℂ) := by p2m_exact_reverting @_root_.P2MW.S_LanglandsTunnell_RankinSelberg_mul_conj_mul_abs_det_rpow_upperUnit_eq_abs_rpow_mul_norm_sq_of_diagOne_eq.solution
