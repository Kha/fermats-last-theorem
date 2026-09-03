import Definitions.Def_LanglandsTunnell_ArchParam
import Mathlib.Analysis.MellinTransform
import P2M.Util
import P2M.Sol.S_LanglandsTunnell_lowering_principal_profile_sum_eq

set_option autoImplicit false

open scoped Real

theorem LanglandsTunnell.lowering_principal_profile_sum_eq (u₁ u₂ : ℂ) (c : ℂ) (hc : c = (u₁ + u₂) / 2)
    (f : ℝ → ℂ)
    (hf : ∀ y : ℝ, f y =
      (y : ℂ) ^ (1 / 2 - c) *
        ((4 : ℂ) * ∫ t in Set.Ioi (0 : ℝ),
          ((t : ℂ) ^ (u₁ + signShift 1) * (Real.exp (-(π * t ^ 2)) : ℂ)) *
            (((y / t : ℝ) : ℂ) ^ (u₂ + signShift 0) * (Real.exp (-(π * (y / t) ^ 2)) : ℂ)) / (t : ℂ))
      + (y : ℂ) ^ (1 / 2 - c) *
        ((4 : ℂ) * ∫ t in Set.Ioi (0 : ℝ),
          ((t : ℂ) ^ (u₁ + signShift 0) * (Real.exp (-(π * t ^ 2)) : ℂ)) *
            (((y / t : ℝ) : ℂ) ^ (u₂ + signShift 1) * (Real.exp (-(π * (y / t) ^ 2)) : ℂ)) / (t : ℂ)))
    (y : ℝ) (hy : 0 < y) :
    2 * (y : ℂ) * deriv f y + (4 * (π : ℂ) * (y : ℂ) - 1) * f y =
      (u₁ - u₂) *
        ((y : ℂ) ^ (1 / 2 - c) *
            ((4 : ℂ) * ∫ t in Set.Ioi (0 : ℝ),
              ((t : ℂ) ^ (u₁ + signShift 0) * (Real.exp (-(π * t ^ 2)) : ℂ)) *
                (((y / t : ℝ) : ℂ) ^ (u₂ + signShift 1) * (Real.exp (-(π * (y / t) ^ 2)) : ℂ)) / (t : ℂ))
          - (y : ℂ) ^ (1 / 2 - c) *
            ((4 : ℂ) * ∫ t in Set.Ioi (0 : ℝ),
              ((t : ℂ) ^ (u₁ + signShift 1) * (Real.exp (-(π * t ^ 2)) : ℂ)) *
                (((y / t : ℝ) : ℂ) ^ (u₂ + signShift 0) * (Real.exp (-(π * (y / t) ^ 2)) : ℂ)) / (t : ℂ))) := by p2m_exact_reverting @_root_.P2MW.S_LanglandsTunnell_lowering_principal_profile_sum_eq.solution
