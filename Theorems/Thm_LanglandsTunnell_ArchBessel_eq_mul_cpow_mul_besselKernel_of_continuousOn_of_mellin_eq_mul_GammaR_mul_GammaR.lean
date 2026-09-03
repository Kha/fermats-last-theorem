import Definitions.Def_LanglandsTunnell_ArchBessel
import Mathlib.Analysis.MellinTransform
import Mathlib.Analysis.SpecialFunctions.Gamma.Deligne
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import P2M.Util
import P2M.Sol.S_LanglandsTunnell_ArchBessel_eq_mul_cpow_mul_besselKernel_of_continuousOn_of_mellin_eq_mul_GammaR_mul_GammaR

set_option autoImplicit false

open Complex MeasureTheory Set LanglandsTunnell.ArchBessel

theorem LanglandsTunnell.ArchBessel.eq_mul_cpow_mul_besselKernel_of_continuousOn_of_mellin_eq_mul_GammaR_mul_GammaR
    (f : ℝ → ℂ) (A p q : ℂ) (σ₀ : ℝ)
    (hcont : ContinuousOn f (Set.Ioi 0))
    (hM : ∀ s : ℂ, σ₀ < s.re →
      MellinConvergent f s ∧ mellin f s = A * Complex.Gammaℝ (s + p) * Complex.Gammaℝ (s + q)) :
    ∀ t : ℝ, 0 < t →
      f t = 2 * A * ((t : ℂ) ^ ((p + q) / 2)) * besselKernel ((p - q) / 2) (2 * Real.pi * t) := by p2m_exact_reverting @_root_.P2MW.S_LanglandsTunnell_ArchBessel_eq_mul_cpow_mul_besselKernel_of_continuousOn_of_mellin_eq_mul_GammaR_mul_GammaR.solution
