import Mathlib.Analysis.MellinTransform
import Mathlib.Analysis.SpecialFunctions.Gamma.Deligne
import Mathlib.MeasureTheory.Integral.Prod
import P2M.Util
import P2M.Sol.S_LanglandsTunnell_mellinConvergent_and_mellin_gaussTorusTransform_eq_Gamma_mul_Jintegral

set_option autoImplicit false

open MeasureTheory Set

theorem LanglandsTunnell.mellinConvergent_and_mellin_gaussTorusTransform_eq_Gamma_mul_Jintegral
    (a : ℝ) (ha : a ≠ 0) (p q κ C : ℂ)
    (H : ℝ → ℂ)
    (hH : H = fun σ' => (Real.exp (-(Real.pi * a ^ 2 * σ' ^ 2)) : ℂ) *
        ∫ w in Set.Ioi (0 : ℝ),
          (C * (((|a| * σ' / w : ℝ)) : ℂ) *
              ((4 : ℂ) * ∫ r in Set.Ioi (0 : ℝ),
                ((r : ℂ) ^ p * (Real.exp (-(Real.pi * r ^ 2)) : ℂ)) *
                  ((((|a| * σ' / w) / r : ℝ) : ℂ) ^ q * (Real.exp (-(Real.pi * ((|a| * σ' / w) / r) ^ 2)) : ℂ)) / (r : ℂ))) *
            ((w : ℝ) : ℂ) ^ κ * (Real.exp (-(Real.pi * ((w ^ 2)⁻¹ + a ^ 2 * w ^ 2))) : ℂ))
    (z : ℂ) (hzq : -1 < (z + q).re) (hzp : -1 < (z + p).re) :
    MellinConvergent H z ∧
    Integrable (fun v : ℝ × ℝ =>
        (((1 + ((v.1 * v.2) ^ 2)⁻¹ : ℝ)) : ℂ) ^ (-((z + q + 1) / 2)) * ((v.1 : ℝ) : ℂ) ^ (κ - 1 - q) * ((v.2 : ℝ) : ℂ) ^ (p - q - 1) *
          (Real.exp (-(Real.pi * (v.2 ^ 2 + (v.1 ^ 2)⁻¹ + a ^ 2 * v.1 ^ 2))) : ℂ))
      (((volume : Measure ℝ).restrict (Set.Ioi 0)).prod ((volume : Measure ℝ).restrict (Set.Ioi 0))) ∧
    mellin H z =
      2 * C * ((|a| : ℝ) : ℂ) ^ (1 + q) * ((Real.pi * a ^ 2 : ℝ) : ℂ) ^ (-((z + q + 1) / 2)) * Complex.Gamma ((z + q + 1) / 2) *
        ∫ w in Set.Ioi (0 : ℝ), ∫ r in Set.Ioi (0 : ℝ),
          (((1 + ((w * r) ^ 2)⁻¹ : ℝ)) : ℂ) ^ (-((z + q + 1) / 2)) * ((w : ℝ) : ℂ) ^ (κ - 1 - q) * ((r : ℝ) : ℂ) ^ (p - q - 1) *
            (Real.exp (-(Real.pi * (r ^ 2 + (w ^ 2)⁻¹ + a ^ 2 * w ^ 2))) : ℂ) := by p2m_exact_reverting @_root_.P2MW.S_LanglandsTunnell_mellinConvergent_and_mellin_gaussTorusTransform_eq_Gamma_mul_Jintegral.solution
