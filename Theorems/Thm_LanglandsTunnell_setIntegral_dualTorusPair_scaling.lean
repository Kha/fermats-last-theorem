import Mathlib.Analysis.SpecialFunctions.Pow.Complex
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.Prod
import P2M.Util
import P2M.Sol.S_LanglandsTunnell_setIntegral_dualTorusPair_scaling

set_option autoImplicit false

open MeasureTheory Set

theorem LanglandsTunnell.setIntegral_dualTorusPair_scaling
    (A₁ A₂ β γ : ℂ) (m n : ℕ) (S : ℝ → ℂ) (hS : ∀ c : ℝ, 0 < c → ∀ y : ℝ, S (y / c) = S y)
    (g : ℝ → ℂ) :
    (∫ a₂ in Ioi (0 : ℝ), ∫ a₁ in Iio (0 : ℝ),
        ((|a₁| : ℝ) : ℂ) ^ A₁ * ((a₂ : ℝ) : ℂ) ^ A₂ * (Real.exp (-(2 * Real.pi * (|a₁| / a₂))) : ℂ) *
        ∫ y₁ : ℝ, ∫ y₂ in Ioi (0 : ℝ),
          ((y₁⁻¹ : ℝ) : ℂ) ^ n * S y₁ * ((|y₁| : ℝ) : ℂ) ^ β * ((y₂ : ℝ) : ℂ) ^ γ *
            (Real.exp (-(Real.pi * (((a₂ * y₂) ^ 2)⁻¹ + (y₁ ^ 2)⁻¹ + a₁ ^ 2 * y₂ ^ 2 + a₂ ^ 2 * y₁ ^ 2))) : ℂ) *
            g (y₁ / y₂) *
            (∫ z : ℝ, (((a₁ * y₂ - (a₂ * y₂)⁻¹ + a₂ * y₁ : ℝ) : ℂ) + Complex.I * (z : ℂ)) ^ m *
              (Real.exp (-(Real.pi * z ^ 2)) : ℂ)))
      = ∫ a₂ in Ioi (0 : ℝ), ∫ t in Iio (0 : ℝ), ∫ u : ℝ, ∫ Y in Ioi (0 : ℝ),
          ((a₂ : ℝ) : ℂ) ^ (A₁ + A₂ + (n : ℂ) - β - γ - 1) * (Real.exp (-(Real.pi * (a₂ ^ 2 * (u ^ 2)⁻¹))) : ℂ) *
          (((|t| : ℝ) : ℂ) ^ A₁ * (Real.exp (-(2 * Real.pi * |t|)) : ℂ) *
            (((u⁻¹ : ℝ) : ℂ) ^ n * S u * ((|u| : ℝ) : ℂ) ^ β * ((Y : ℝ) : ℂ) ^ γ) *
            (Real.exp (-(Real.pi * ((Y ^ 2)⁻¹ + t ^ 2 * Y ^ 2 + u ^ 2))) : ℂ) *
            g (u / Y) *
            (∫ z : ℝ, (((t * Y - Y⁻¹ + u : ℝ) : ℂ) + Complex.I * (z : ℂ)) ^ m *
              (Real.exp (-(Real.pi * z ^ 2)) : ℂ))) := by p2m_exact_reverting @_root_.P2MW.S_LanglandsTunnell_setIntegral_dualTorusPair_scaling.solution
