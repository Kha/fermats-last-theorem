import Mathlib.Analysis.MellinTransform
import Definitions.Def_LanglandsTunnell_ArchBessel
import P2M.Util
import P2M.Sol.S_LanglandsTunnell_ArchBessel_hasDerivAt_besselKernel

set_option autoImplicit false

p2m_open "LanglandsTunnell.ArchBessel~integrableOn_exp_neg_mul_add_inv_mul_cpow"

theorem LanglandsTunnell.ArchBessel.hasDerivAt_besselKernel (ν : ℂ) (x : ℝ) (hx : 0 < x) :
    HasDerivAt (fun x : ℝ => besselKernel ν x)
      (-(besselKernel (ν - 1) x + besselKernel (ν + 1) x) / 2) x := by p2m_exact_reverting @_root_.P2MW.S_LanglandsTunnell_ArchBessel_hasDerivAt_besselKernel.solution
