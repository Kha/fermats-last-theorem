import Mathlib.Analysis.SpecialFunctions.Pow.Complex
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.Prod
import P2M.Util
import P2M.Sol.S_LanglandsTunnell_setIntegral_oneSided_torusPair_eq_setIntegral_fiber

set_option autoImplicit false

open MeasureTheory Set

theorem LanglandsTunnell.setIntegral_oneSided_torusPair_eq_setIntegral_fiber
    (α β γ : ℂ) (g : ℝ → ℂ) (hg : Measurable g) (B : ℝ → ℝ → ℝ → ℝ → ℂ)
    (hB : Measurable fun x : ℝ × ℝ × ℝ × ℝ => B x.1 x.2.1 x.2.2.1 x.2.2.2)
    (hInt : Integrable (fun x : ℝ × ℝ × ℝ × ℝ =>
        ((x.1 : ℝ) : ℂ) ^ α * (Real.exp (-(2 * Real.pi * x.1)) : ℂ) *
          ((|x.2.1| : ℝ) : ℂ) ^ β * ((x.2.2.1 : ℝ) : ℂ) ^ γ *
          (Real.exp (-(Real.pi * ((x.2.1 ^ 2)⁻¹ + x.1 ^ 2 * x.2.1 ^ 2 + (x.2.2.1 ^ 2)⁻¹))) : ℂ) *
          g (x.1 * |x.2.1| / x.2.2.1) *
          (B (x.2.1⁻¹) (x.2.2.1⁻¹) (x.1 * x.2.1) x.2.2.2 * (Real.exp (-(Real.pi * x.2.2.2 ^ 2)) : ℂ)))
        ((volume.restrict (Ioi (0 : ℝ))).prod ((volume.restrict (Iio (0 : ℝ))).prod
          ((volume.restrict (Ioi (0 : ℝ))).prod volume)))) :
    ∫ t in Ioi (0 : ℝ), ∫ y₁ in Iio (0 : ℝ), ∫ y₂ in Ioi (0 : ℝ),
        ((t : ℝ) : ℂ) ^ α * (Real.exp (-(2 * Real.pi * t)) : ℂ) *
          ((|y₁| : ℝ) : ℂ) ^ β * ((y₂ : ℝ) : ℂ) ^ γ *
          (Real.exp (-(Real.pi * ((y₁ ^ 2)⁻¹ + t ^ 2 * y₁ ^ 2 + (y₂ ^ 2)⁻¹))) : ℂ) *
          g (t * |y₁| / y₂) *
          (∫ z : ℝ, B y₁⁻¹ y₂⁻¹ (t * y₁) z * (Real.exp (-(Real.pi * z ^ 2)) : ℂ))
      = ∫ v in Ioi (0 : ℝ), g v * ((v : ℝ) : ℂ) ^ α *
          ∫ σ in Ioi (0 : ℝ), ∫ w in Ioi (v / σ),
            (((σ * w - v : ℝ) : ℂ) ^ (α - β - 1)) * ((w : ℝ) : ℂ) ^ (-2 * α + β - γ - 2) *
              (Real.exp (-(Real.pi * (σ ^ 2 + w ^ 2))) : ℂ) *
              (∫ z : ℝ, B (-((σ * w - v) / w)) w (-(v / w)) z * (Real.exp (-(Real.pi * z ^ 2)) : ℂ)) := by p2m_exact_reverting @_root_.P2MW.S_LanglandsTunnell_setIntegral_oneSided_torusPair_eq_setIntegral_fiber.solution
