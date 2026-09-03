import Mathlib.Analysis.SpecialFunctions.Pow.Complex
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.Prod
import P2M.Util
import P2M.Sol.S_LanglandsTunnell_integrable_dualFibres_of_integrable_oneSided

set_option autoImplicit false

open MeasureTheory Set

theorem LanglandsTunnell.integrable_dualFibres_of_integrable_oneSided
    (A₁ β γ w : ℂ) (m n : ℕ) (S : ℝ → ℂ) (hS : ∀ c : ℝ, 0 < c → ∀ y : ℝ, S (y / c) = S y)
    (hSm : Measurable S) (g : ℝ → ℂ) (hg : Measurable g)
    (hminus : Integrable (fun x : ℝ × ℝ × ℝ × ℝ =>
        ((x.1 : ℝ) : ℂ) ^ (A₁ - γ - 1) * (Real.exp (-(2 * Real.pi * x.1)) : ℂ) *
          ((|x.2.1| : ℝ) : ℂ) ^ (-γ - 2) * ((x.2.2.1 : ℝ) : ℂ) ^ ((n : ℂ) - w - β - 3) *
          (Real.exp (-(Real.pi * ((x.2.1 ^ 2)⁻¹ + x.1 ^ 2 * x.2.1 ^ 2 + (x.2.2.1 ^ 2)⁻¹))) : ℂ) *
          (fun v : ℝ => g (-v)) (x.1 * |x.2.1| / x.2.2.1) *
          ((((x.2.1⁻¹ - x.2.2.1⁻¹ + x.1 * x.2.1 : ℝ) : ℂ) + Complex.I * (x.2.2.2 : ℂ)) ^ m *
            (Real.exp (-(Real.pi * x.2.2.2 ^ 2)) : ℂ)))
        ((volume.restrict (Ioi (0 : ℝ))).prod ((volume.restrict (Iio (0 : ℝ))).prod
          ((volume.restrict (Ioi (0 : ℝ))).prod volume))))
    (hplus : Integrable (fun x : ℝ × ℝ × ℝ × ℝ =>
        ((x.1 : ℝ) : ℂ) ^ (A₁ - γ - 1) * (Real.exp (-(2 * Real.pi * x.1)) : ℂ) *
          ((|x.2.1| : ℝ) : ℂ) ^ (-γ - 2) * ((x.2.2.1 : ℝ) : ℂ) ^ ((n : ℂ) - w - β - 3) *
          (Real.exp (-(Real.pi * ((x.2.1 ^ 2)⁻¹ + x.1 ^ 2 * x.2.1 ^ 2 + (x.2.2.1 ^ 2)⁻¹))) : ℂ) *
          g (x.1 * |x.2.1| / x.2.2.1) *
          ((((-x.2.1⁻¹ - x.2.2.1⁻¹ - x.1 * x.2.1 : ℝ) : ℂ) + Complex.I * (x.2.2.2 : ℂ)) ^ m *
            (Real.exp (-(Real.pi * x.2.2.2 ^ 2)) : ℂ)))
        ((volume.restrict (Ioi (0 : ℝ))).prod ((volume.restrict (Iio (0 : ℝ))).prod
          ((volume.restrict (Ioi (0 : ℝ))).prod volume)))) :
    Integrable (fun q : ℝ × ℝ × ℝ =>
        ((|q.2.2| : ℝ) : ℂ) ^ (w + 1) *
          (((|q.1| : ℝ) : ℂ) ^ A₁ * (Real.exp (-(2 * Real.pi * |q.1|)) : ℂ) *
            (((q.2.2⁻¹ : ℝ) : ℂ) ^ n * S q.2.2 * ((|q.2.2| : ℝ) : ℂ) ^ β * ((q.2.1 : ℝ) : ℂ) ^ γ) *
            (Real.exp (-(Real.pi * ((q.2.1 ^ 2)⁻¹ + q.1 ^ 2 * q.2.1 ^ 2 + q.2.2 ^ 2))) : ℂ) *
            g (q.2.2 / q.2.1) *
            (∫ z : ℝ, (((q.1 * q.2.1 - q.2.1⁻¹ + q.2.2 : ℝ) : ℂ) + Complex.I * (z : ℂ)) ^ m *
              (Real.exp (-(Real.pi * z ^ 2)) : ℂ))))
        ((volume.restrict (Iio (0 : ℝ))).prod ((volume.restrict (Ioi (0 : ℝ))).prod (volume : Measure ℝ))) ∧
    Integrable (fun q : ℝ × ℝ × ℝ =>
        ((|q.2.1| : ℝ) : ℂ) ^ (w + 1) *
          (((|q.1| : ℝ) : ℂ) ^ A₁ * (Real.exp (-(2 * Real.pi * |q.1|)) : ℂ) *
            (((q.2.1⁻¹ : ℝ) : ℂ) ^ n * S q.2.1 * ((|q.2.1| : ℝ) : ℂ) ^ β * ((q.2.2 : ℝ) : ℂ) ^ γ) *
            (Real.exp (-(Real.pi * ((q.2.2 ^ 2)⁻¹ + q.1 ^ 2 * q.2.2 ^ 2 + q.2.1 ^ 2))) : ℂ) *
            g (q.2.1 / q.2.2) *
            (∫ z : ℝ, (((q.1 * q.2.2 - q.2.2⁻¹ + q.2.1 : ℝ) : ℂ) + Complex.I * (z : ℂ)) ^ m *
              (Real.exp (-(Real.pi * z ^ 2)) : ℂ))))
        ((volume.restrict (Iio (0 : ℝ))).prod ((volume : Measure ℝ).prod (volume.restrict (Ioi (0 : ℝ))))) := by p2m_exact_reverting @_root_.P2MW.S_LanglandsTunnell_integrable_dualFibres_of_integrable_oneSided.solution
