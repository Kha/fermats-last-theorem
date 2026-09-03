import Definitions.Def_LanglandsTunnell_ArchParam
import Mathlib.Analysis.MellinTransform
import P2M.Util
import P2M.Sol.S_LanglandsTunnell_mellin_mulConvGaussian_eq_archFactor_principal

set_option autoImplicit false

open scoped Real

theorem LanglandsTunnell.mellin_mulConvGaussian_eq_archFactor_principal (u₁ : ℂ) (a₁ : ZMod 2)
    (u₂ : ℂ) (a₂ : ZMod 2) (s : ℂ) (h₁ : 0 < (s + (u₁ + signShift a₁)).re)
    (h₂ : 0 < (s + (u₂ + signShift a₂)).re) :
    mellin (fun y : ℝ => (4 : ℂ) * ∫ t in Set.Ioi (0 : ℝ),
        ((t : ℂ) ^ (u₁ + signShift a₁) * (Real.exp (-(π * t ^ 2)) : ℂ)) *
          (((y / t : ℝ) : ℂ) ^ (u₂ + signShift a₂) * (Real.exp (-(π * (y / t) ^ 2)) : ℂ)) / (t : ℂ))
        s =
      (RealArchParam.principal u₁ a₁ u₂ a₂).archFactor s := by p2m_exact_reverting @_root_.P2MW.S_LanglandsTunnell_mellin_mulConvGaussian_eq_archFactor_principal.solution
