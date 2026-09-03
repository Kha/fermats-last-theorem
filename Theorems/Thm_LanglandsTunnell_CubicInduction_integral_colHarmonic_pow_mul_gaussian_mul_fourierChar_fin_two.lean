import Mathlib
import P2M.Util
import P2M.Sol.S_LanglandsTunnell_CubicInduction_integral_colHarmonic_pow_mul_gaussian_mul_fourierChar_fin_two

set_option autoImplicit false

open MeasureTheory

theorem LanglandsTunnell.CubicInduction.integral_colHarmonic_pow_mul_gaussian_mul_fourierChar_fin_two
    (m : ℕ) (ε : ℝ) (hε : ε = 1 ∨ ε = -1) (ξ : Fin 2 → ℝ) :
    Integrable (fun u : Fin 2 → ℝ =>
        (((u 0 : ℝ) : ℂ) + (ε : ℂ) * Complex.I * ((u 1 : ℝ) : ℂ)) ^ m *
          (Real.exp (-(Real.pi * ∑ i : Fin 2, u i ^ 2)) : ℂ) *
          Complex.exp (-(2 * Real.pi * Complex.I * ((∑ i : Fin 2, ξ i * u i : ℝ) : ℂ)))) ∧
    (∫ u : Fin 2 → ℝ,
        (((u 0 : ℝ) : ℂ) + (ε : ℂ) * Complex.I * ((u 1 : ℝ) : ℂ)) ^ m *
          (Real.exp (-(Real.pi * ∑ i : Fin 2, u i ^ 2)) : ℂ) *
          Complex.exp (-(2 * Real.pi * Complex.I * ((∑ i : Fin 2, ξ i * u i : ℝ) : ℂ))))
      = (-Complex.I) ^ m * (((ξ 0 : ℝ) : ℂ) + (ε : ℂ) * Complex.I * ((ξ 1 : ℝ) : ℂ)) ^ m *
          (Real.exp (-(Real.pi * ∑ i : Fin 2, ξ i ^ 2)) : ℂ) := by p2m_exact_reverting @_root_.P2MW.S_LanglandsTunnell_CubicInduction_integral_colHarmonic_pow_mul_gaussian_mul_fourierChar_fin_two.solution
