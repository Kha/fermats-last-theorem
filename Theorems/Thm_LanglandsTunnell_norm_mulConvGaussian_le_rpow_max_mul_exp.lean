import Definitions.Def_LanglandsTunnell_ArchParam
import P2M.Util
import P2M.Sol.S_LanglandsTunnell_norm_mulConvGaussian_le_rpow_max_mul_exp

set_option autoImplicit false

open scoped Real

theorem LanglandsTunnell.norm_mulConvGaussian_le_rpow_max_mul_exp (u₁ : ℂ) (a₁ : ZMod 2) (u₂ : ℂ)
    (a₂ : ZMod 2) :
    ∃ C : ℝ, ∀ y : ℝ, 1 ≤ y →
      ‖(4 : ℂ) * ∫ t in Set.Ioi (0 : ℝ),
        ((t : ℂ) ^ (u₁ + signShift a₁) * (Real.exp (-(π * t ^ 2)) : ℂ)) *
          (((y / t : ℝ) : ℂ) ^ (u₂ + signShift a₂) * (Real.exp (-(π * (y / t) ^ 2)) : ℂ)) / (t : ℂ)‖
        ≤ C * y ^ (max (u₁ + signShift a₁).re (u₂ + signShift a₂).re) * Real.exp (-(π * y)) := by p2m_exact_reverting @_root_.P2MW.S_LanglandsTunnell_norm_mulConvGaussian_le_rpow_max_mul_exp.solution
