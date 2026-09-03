import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Complex
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.Prod
import P2M.Util
import P2M.Sol.S_LanglandsTunnell_setIntegral_oneSided_torusPair_flatBracket_eq_const_mul_laplaceMellin_and_mirror_eq_zero

set_option autoImplicit false

open MeasureTheory Set

theorem LanglandsTunnell.setIntegral_oneSided_torusPair_flatBracket_eq_const_mul_laplaceMellin_and_mirror_eq_zero
    (m : ℕ) (hm : 1 ≤ m) (β : ℂ) (g g' : ℝ → ℂ) (hg : Measurable g) (hg' : Measurable g')
    (Cg σg : ℝ) (hσg : 0 ≤ σg) (hgb : ∀ τ : ℝ, τ ≠ 0 → ‖g τ‖ ≤ Cg * (1 + |τ| ^ (-σg)))
    (Cg' σg' : ℝ) (hσg' : 0 ≤ σg') (hgb' : ∀ τ : ℝ, τ ≠ 0 → ‖g' τ‖ ≤ Cg' * (1 + |τ| ^ (-σg'))) :
    ∃ σ₀ : ℝ, ∀ α γ : ℂ, σ₀ < α.re → γ.re < -σ₀ → -2 * α + β - γ - 2 = (1 : ℂ) - (m : ℂ) →
      (∫ t in Ioi (0 : ℝ), ∫ y₁ in Iio (0 : ℝ), ∫ y₂ in Ioi (0 : ℝ),
          ((t : ℝ) : ℂ) ^ α * (Real.exp (-(2 * Real.pi * t)) : ℂ) *
            ((|y₁| : ℝ) : ℂ) ^ β * ((y₂ : ℝ) : ℂ) ^ γ *
            (Real.exp (-(Real.pi * ((y₁ ^ 2)⁻¹ + t ^ 2 * y₁ ^ 2 + (y₂ ^ 2)⁻¹))) : ℂ) *
            g (t * |y₁| / y₂) *
            (∫ z : ℝ, (((y₁⁻¹ - y₂⁻¹ + t * y₁ : ℝ) : ℂ) + Complex.I * (z : ℂ)) ^ m *
              (Real.exp (-(Real.pi * z ^ 2)) : ℂ)))
        = (1 / 2 : ℂ) * (2 * (Real.pi : ℂ)) ^ (-(α - β)) * Complex.Gamma (α - β) * (-2 : ℂ) ^ m *
          ∫ v in Ioi (0 : ℝ), g v * ((v : ℝ) : ℂ) ^ α * (Real.exp (-(2 * Real.pi * v)) : ℂ) ∧
      (∫ t in Ioi (0 : ℝ), ∫ y₁ in Iio (0 : ℝ), ∫ y₂ in Ioi (0 : ℝ),
          ((t : ℝ) : ℂ) ^ α * (Real.exp (-(2 * Real.pi * t)) : ℂ) *
            ((|y₁| : ℝ) : ℂ) ^ β * ((y₂ : ℝ) : ℂ) ^ γ *
            (Real.exp (-(Real.pi * ((y₁ ^ 2)⁻¹ + t ^ 2 * y₁ ^ 2 + (y₂ ^ 2)⁻¹))) : ℂ) *
            g' (t * |y₁| / y₂) *
            (∫ z : ℝ, (((-y₁⁻¹ - y₂⁻¹ - t * y₁ : ℝ) : ℂ) + Complex.I * (z : ℂ)) ^ m *
              (Real.exp (-(Real.pi * z ^ 2)) : ℂ)))
        = 0 := by p2m_exact_reverting @_root_.P2MW.S_LanglandsTunnell_setIntegral_oneSided_torusPair_flatBracket_eq_const_mul_laplaceMellin_and_mirror_eq_zero.solution
