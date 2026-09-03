import Mathlib.Analysis.MellinTransform
import Definitions.Def_LanglandsTunnell_ArchBessel
import P2M.Util
import P2M.Sol.S_LanglandsTunnell_ArchBessel_hasDerivAt_besselKernel_and_hasDerivAt_deriv_besselKernel

set_option autoImplicit false

p2m_open "LanglandsTunnell.ArchBessel~hasDerivAt_besselKernel~mul_besselKernel_eq_mul_sub"

theorem LanglandsTunnell.ArchBessel.hasDerivAt_besselKernel_and_hasDerivAt_deriv_besselKernel
    (ν : ℂ) (x : ℝ) (hx : 0 < x) :
    HasDerivAt (fun x : ℝ => besselKernel ν x) (-besselKernel (ν + 1) x + ν / (x : ℂ) * besselKernel ν x) x ∧
      HasDerivAt (deriv fun x : ℝ => besselKernel ν x)
        ((1 + ν ^ 2 / (x : ℂ) ^ 2) * besselKernel ν x - (deriv (fun x : ℝ => besselKernel ν x) x) / (x : ℂ)) x := by p2m_exact_reverting @_root_.P2MW.S_LanglandsTunnell_ArchBessel_hasDerivAt_besselKernel_and_hasDerivAt_deriv_besselKernel.solution
