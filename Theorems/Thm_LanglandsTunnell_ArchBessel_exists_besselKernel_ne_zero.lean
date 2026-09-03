import Mathlib.Analysis.MellinTransform
import Definitions.Def_LanglandsTunnell_ArchBessel
import P2M.Util
import P2M.Sol.S_LanglandsTunnell_ArchBessel_exists_besselKernel_ne_zero

set_option autoImplicit false

p2m_open "LanglandsTunnell.ArchBessel~mellin_besselKernel_eq_mul_Gamma_mul_Gamma"

theorem LanglandsTunnell.ArchBessel.exists_besselKernel_ne_zero (ν : ℂ) :
    ∃ x : ℝ, 0 < x ∧ besselKernel ν x ≠ 0 := by p2m_exact_reverting @_root_.P2MW.S_LanglandsTunnell_ArchBessel_exists_besselKernel_ne_zero.solution
