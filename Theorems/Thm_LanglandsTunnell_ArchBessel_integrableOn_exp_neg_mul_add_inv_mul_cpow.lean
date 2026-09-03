import Mathlib.Analysis.MellinTransform
import Definitions.Def_LanglandsTunnell_ArchBessel
import P2M.Util
import P2M.Sol.S_LanglandsTunnell_ArchBessel_integrableOn_exp_neg_mul_add_inv_mul_cpow

set_option autoImplicit false

open LanglandsTunnell.ArchBessel

theorem LanglandsTunnell.ArchBessel.integrableOn_exp_neg_mul_add_inv_mul_cpow (ν : ℂ) (x : ℝ) (hx : 0 < x) :
    MeasureTheory.IntegrableOn
      (fun t : ℝ => (Real.exp (-(x * (t + t⁻¹) / 2)) : ℂ) * ((t : ℂ) ^ (ν - 1))) (Set.Ioi 0) := by p2m_exact_reverting @_root_.P2MW.S_LanglandsTunnell_ArchBessel_integrableOn_exp_neg_mul_add_inv_mul_cpow.solution
