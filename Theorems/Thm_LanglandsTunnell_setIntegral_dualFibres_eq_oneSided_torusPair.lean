import Mathlib.Analysis.SpecialFunctions.Pow.Complex
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.Prod
import P2M.Util
import P2M.Sol.S_LanglandsTunnell_setIntegral_dualFibres_eq_oneSided_torusPair

set_option autoImplicit false

open MeasureTheory Set

theorem LanglandsTunnell.setIntegral_dualFibres_eq_oneSided_torusPair
    (A₁ β γ w : ℂ) (m n : ℕ) (S : ℝ → ℂ) (hS : ∀ c : ℝ, 0 < c → ∀ y : ℝ, S (y / c) = S y)
    (g : ℝ → ℂ)
    (hK : Integrable (fun q : ℝ × ℝ × ℝ =>
        ((|q.2.2| : ℝ) : ℂ) ^ (w + 1) *
          (((|q.1| : ℝ) : ℂ) ^ A₁ * (Real.exp (-(2 * Real.pi * |q.1|)) : ℂ) *
            (((q.2.2⁻¹ : ℝ) : ℂ) ^ n * S q.2.2 * ((|q.2.2| : ℝ) : ℂ) ^ β * ((q.2.1 : ℝ) : ℂ) ^ γ) *
            (Real.exp (-(Real.pi * ((q.2.1 ^ 2)⁻¹ + q.1 ^ 2 * q.2.1 ^ 2 + q.2.2 ^ 2))) : ℂ) *
            g (q.2.2 / q.2.1) *
            (∫ z : ℝ, (((q.1 * q.2.1 - q.2.1⁻¹ + q.2.2 : ℝ) : ℂ) + Complex.I * (z : ℂ)) ^ m *
              (Real.exp (-(Real.pi * z ^ 2)) : ℂ))))
        ((volume.restrict (Iio (0 : ℝ))).prod ((volume.restrict (Ioi (0 : ℝ))).prod (volume : Measure ℝ)))) :
    (∫ t in Iio (0 : ℝ), ∫ Y in Ioi (0 : ℝ), ∫ u : ℝ,
        ((|u| : ℝ) : ℂ) ^ (w + 1) *
          (((|t| : ℝ) : ℂ) ^ A₁ * (Real.exp (-(2 * Real.pi * |t|)) : ℂ) *
            (((u⁻¹ : ℝ) : ℂ) ^ n * S u * ((|u| : ℝ) : ℂ) ^ β * ((Y : ℝ) : ℂ) ^ γ) *
            (Real.exp (-(Real.pi * ((Y ^ 2)⁻¹ + t ^ 2 * Y ^ 2 + u ^ 2))) : ℂ) *
            g (u / Y) *
            (∫ z : ℝ, (((t * Y - Y⁻¹ + u : ℝ) : ℂ) + Complex.I * (z : ℂ)) ^ m *
              (Real.exp (-(Real.pi * z ^ 2)) : ℂ))))
      = (-1 : ℂ) ^ n * S (-1) *
          (∫ t in Ioi (0 : ℝ), ∫ y₁ in Iio (0 : ℝ), ∫ y₂ in Ioi (0 : ℝ),
            ((t : ℝ) : ℂ) ^ (A₁ - γ - 1) * (Real.exp (-(2 * Real.pi * t)) : ℂ) *
              ((|y₁| : ℝ) : ℂ) ^ (-γ - 2) * ((y₂ : ℝ) : ℂ) ^ ((n : ℂ) - w - β - 3) *
              (Real.exp (-(Real.pi * ((y₁ ^ 2)⁻¹ + t ^ 2 * y₁ ^ 2 + (y₂ ^ 2)⁻¹))) : ℂ) *
              (fun v : ℝ => g (-v)) (t * |y₁| / y₂) *
              (∫ z : ℝ, (((y₁⁻¹ - y₂⁻¹ + t * y₁ : ℝ) : ℂ) + Complex.I * (z : ℂ)) ^ m *
                (Real.exp (-(Real.pi * z ^ 2)) : ℂ))) +
        (-1 : ℂ) ^ m * S 1 *
          (∫ t in Ioi (0 : ℝ), ∫ y₁ in Iio (0 : ℝ), ∫ y₂ in Ioi (0 : ℝ),
            ((t : ℝ) : ℂ) ^ (A₁ - γ - 1) * (Real.exp (-(2 * Real.pi * t)) : ℂ) *
              ((|y₁| : ℝ) : ℂ) ^ (-γ - 2) * ((y₂ : ℝ) : ℂ) ^ ((n : ℂ) - w - β - 3) *
              (Real.exp (-(Real.pi * ((y₁ ^ 2)⁻¹ + t ^ 2 * y₁ ^ 2 + (y₂ ^ 2)⁻¹))) : ℂ) *
              g (t * |y₁| / y₂) *
              (∫ z : ℝ, (((-y₁⁻¹ - y₂⁻¹ - t * y₁ : ℝ) : ℂ) + Complex.I * (z : ℂ)) ^ m *
                (Real.exp (-(Real.pi * z ^ 2)) : ℂ))) := by p2m_exact_reverting @_root_.P2MW.S_LanglandsTunnell_setIntegral_dualFibres_eq_oneSided_torusPair.solution
