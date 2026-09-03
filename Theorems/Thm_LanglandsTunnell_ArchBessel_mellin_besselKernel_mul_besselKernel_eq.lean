import Definitions.Def_LanglandsTunnell_ArchBessel
import Mathlib.Analysis.MellinTransform
import Mathlib.Analysis.SpecialFunctions.Gamma.Deligne
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import P2M.Util
import P2M.Sol.S_LanglandsTunnell_ArchBessel_mellin_besselKernel_mul_besselKernel_eq

set_option autoImplicit false

open Complex MeasureTheory Set LanglandsTunnell.ArchBessel

theorem LanglandsTunnell.ArchBessel.mellin_besselKernel_mul_besselKernel_eq (μ ν s : ℂ) (hs : |μ.re| + |ν.re| < s.re) :
    MellinConvergent (fun x : ℝ => besselKernel μ x * besselKernel ν x) s ∧
      mellin (fun x : ℝ => besselKernel μ x * besselKernel ν x) s =
        (2 : ℂ) ^ (s - 1) *
          (Complex.Gamma ((s + μ + ν) / 2) * Complex.Gamma ((s + μ - ν) / 2) *
            Complex.Gamma ((s - μ + ν) / 2) * Complex.Gamma ((s - μ - ν) / 2)) / Complex.Gamma s := by p2m_exact_reverting @_root_.P2MW.S_LanglandsTunnell_ArchBessel_mellin_besselKernel_mul_besselKernel_eq.solution
