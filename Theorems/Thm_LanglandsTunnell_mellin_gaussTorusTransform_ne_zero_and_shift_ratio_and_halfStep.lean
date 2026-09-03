import Mathlib.Analysis.MellinTransform
import Mathlib.Analysis.SpecialFunctions.Gamma.Deligne
import Mathlib.MeasureTheory.Integral.Prod
import P2M.Util
import P2M.Sol.S_LanglandsTunnell_mellin_gaussTorusTransform_ne_zero_and_shift_ratio_and_halfStep

set_option autoImplicit false

open MeasureTheory Set

theorem LanglandsTunnell.mellin_gaussTorusTransform_ne_zero_and_shift_ratio_and_halfStep
    (a : ℝ) (ha : a ≠ 0) (p q κ C : ℂ) (hC : C ≠ 0) (p' q' C' : ℂ) (hpq' : (p' + q').re ≤ (p + q).re)
    (H H' H'' : ℝ → ℂ)
    (hH : H = fun σ' => (Real.exp (-(Real.pi * a ^ 2 * σ' ^ 2)) : ℂ) *
        ∫ w in Set.Ioi (0 : ℝ),
          (C * (((|a| * σ' / w : ℝ)) : ℂ) *
              ((4 : ℂ) * ∫ r in Set.Ioi (0 : ℝ),
                ((r : ℂ) ^ p * (Real.exp (-(Real.pi * r ^ 2)) : ℂ)) *
                  ((((|a| * σ' / w) / r : ℝ) : ℂ) ^ q * (Real.exp (-(Real.pi * ((|a| * σ' / w) / r) ^ 2)) : ℂ)) / (r : ℂ))) *
            ((w : ℝ) : ℂ) ^ κ * (Real.exp (-(Real.pi * ((w ^ 2)⁻¹ + a ^ 2 * w ^ 2))) : ℂ))
    (hH' : H' = fun σ' => (Real.exp (-(Real.pi * a ^ 2 * σ' ^ 2)) : ℂ) *
        ∫ w in Set.Ioi (0 : ℝ),
          (C' * (((|a| * σ' / w : ℝ)) : ℂ) *
              ((4 : ℂ) * ∫ r in Set.Ioi (0 : ℝ),
                ((r : ℂ) ^ p' * (Real.exp (-(Real.pi * r ^ 2)) : ℂ)) *
                  ((((|a| * σ' / w) / r : ℝ) : ℂ) ^ q' * (Real.exp (-(Real.pi * ((|a| * σ' / w) / r) ^ 2)) : ℂ)) / (r : ℂ))) *
            ((w : ℝ) : ℂ) ^ (κ - 1) * (Real.exp (-(Real.pi * ((w ^ 2)⁻¹ + a ^ 2 * w ^ 2))) : ℂ))
    (hH'' : H'' = fun σ' => (Real.exp (-(Real.pi * a ^ 2 * σ' ^ 2)) : ℂ) *
        ∫ w in Set.Ioi (0 : ℝ),
          (C * (((|a| * σ' / w : ℝ)) : ℂ) *
              ((4 : ℂ) * ∫ r in Set.Ioi (0 : ℝ),
                ((r : ℂ) ^ p * (Real.exp (-(Real.pi * r ^ 2)) : ℂ)) *
                  ((((|a| * σ' / w) / r : ℝ) : ℂ) ^ q * (Real.exp (-(Real.pi * ((|a| * σ' / w) / r) ^ 2)) : ℂ)) / (r : ℂ))) *
            ((w : ℝ) : ℂ) ^ (κ - 2) * (Real.exp (-(Real.pi * ((w ^ 2)⁻¹ + a ^ 2 * w ^ 2))) : ℂ)) :
    ∀ δ : ℝ, 0 < δ → ∃ R : ℝ, ∀ x : ℝ, R ≤ x →
      mellin H (x : ℂ) ≠ 0 ∧
      ‖mellin H ((x : ℂ) + 2) - (x : ℂ) / (2 * (Real.pi : ℂ) * (a : ℂ) ^ 2) * mellin H (x : ℂ)‖ ≤ δ * x * ‖mellin H (x : ℂ)‖ ∧
      ‖mellin H' ((x : ℂ) - 1)‖ ≤ δ * ‖mellin H (x : ℂ)‖ ∧
      ‖mellin H'' (x : ℂ)‖ ≤ δ * ‖mellin H (x : ℂ)‖ := by p2m_exact_reverting @_root_.P2MW.S_LanglandsTunnell_mellin_gaussTorusTransform_ne_zero_and_shift_ratio_and_halfStep.solution
