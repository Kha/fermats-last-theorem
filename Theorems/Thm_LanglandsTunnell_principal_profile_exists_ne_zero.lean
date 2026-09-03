import Definitions.Def_LanglandsTunnell_ArchParam
import P2M.Util
import P2M.Sol.S_LanglandsTunnell_principal_profile_exists_ne_zero

set_option autoImplicit false

open scoped Real

theorem LanglandsTunnell.principal_profile_exists_ne_zero (u₁ : ℂ) (a₁ : ZMod 2) (u₂ : ℂ) (a₂ : ZMod 2)
    (c : ℂ) (f : ℝ → ℂ)
    (hf : ∀ y : ℝ, f y = (y : ℂ) ^ (1 / 2 - c) *
      ((4 : ℂ) * ∫ t in Set.Ioi (0 : ℝ),
        ((t : ℂ) ^ (u₁ + signShift a₁) * (Real.exp (-(π * t ^ 2)) : ℂ)) *
          (((y / t : ℝ) : ℂ) ^ (u₂ + signShift a₂) * (Real.exp (-(π * (y / t) ^ 2)) : ℂ)) / (t : ℂ))) :
    ∃ y : ℝ, 0 < y ∧ f y ≠ 0 := by p2m_exact_reverting @_root_.P2MW.S_LanglandsTunnell_principal_profile_exists_ne_zero.solution
