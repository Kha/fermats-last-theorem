import Mathlib
import P2M.Util
import P2M.Sol.S_AutomorphicForm_apply_one_eq_zero_of_isLocallyConstant_of_forall_exists_integral_integral_eq_zero

set_option autoImplicit false

open MeasureTheory

theorem AutomorphicForm.apply_one_eq_zero_of_isLocallyConstant_of_forall_exists_integral_integral_eq_zero
    {F : Type*} [NontriviallyNormedField F] [IsUltrametricDist F] [ProperSpace F]
    [MeasurableSpace F] [BorelSpace F] [MeasurableSpace Fˣ] [BorelSpace Fˣ]
    (μ : Measure F) [μ.IsAddHaarMeasure] (ν : Measure Fˣ) [ν.IsHaarMeasure]
    (Φ : Matrix (Fin 2) (Fin 2) F → ℂ) (hΦ : IsLocallyConstant Φ) (hΦc : HasCompactSupport Φ)
    (ϖ : F) (hϖ : ‖ϖ‖ < 1) (hϖsq : ∀ a t : F, t ≠ 0 → ‖a‖ ^ 2 ≠ ‖ϖ‖ * ‖t‖ ^ 2)
    (hvan : ∀ ε : ℝ, 0 < ε → ∃ r r' : F, r' ≠ 0 ∧ ‖r'‖ < ‖r‖ ∧ ‖r‖ < ε ∧
      (∫ b, ∫ a, Φ (1 + !![a, (b : F); (ϖ * r ^ 2 - a ^ 2) / b, -a]) ∂μ ∂ν) = 0 ∧
      (∫ b, ∫ a, Φ (1 + !![a, (b : F); (ϖ * r' ^ 2 - a ^ 2) / b, -a]) ∂μ ∂ν) = 0) :
    Φ 1 = 0 := by p2m_exact_reverting @_root_.P2MW.S_AutomorphicForm_apply_one_eq_zero_of_isLocallyConstant_of_forall_exists_integral_integral_eq_zero.solution
