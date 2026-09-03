import Mathlib.Analysis.MellinTransform
import Mathlib.Analysis.Calculus.Deriv.Basic
import Definitions.Def_LanglandsTunnell_ArchBessel
import P2M.Util
import P2M.Sol.S_LanglandsTunnell_ArchBessel_sq_eq_sq_of_whittakerODE_pair_of_add_mul_eq_mul_cpow_mul_besselKernel

set_option autoImplicit false

open LanglandsTunnell.ArchBessel hiding hasDerivAt_besselKernel_and_hasDerivAt_deriv_besselKernel exists_besselKernel_ne_zero

theorem LanglandsTunnell.ArchBessel.sq_eq_sq_of_whittakerODE_pair_of_add_mul_eq_mul_cpow_mul_besselKernel
    (ν μ c ε C a : ℂ) (P Q : ℝ → ℂ)
    (hP : DifferentiableOn ℝ P (Set.Ioi 0)) (hP' : DifferentiableOn ℝ (deriv P) (Set.Ioi 0))
    (hPode : ∀ y : ℝ, 0 < y →
      (y : ℂ) ^ 2 * deriv (deriv P) y
        + (1 / 4 - ν ^ 2 + 2 * (Real.pi : ℂ) * c * (y : ℂ) - 4 * (Real.pi : ℂ) ^ 2 * (y : ℂ) ^ 2) * P y = 0)
    (hQ : DifferentiableOn ℝ Q (Set.Ioi 0)) (hQ' : DifferentiableOn ℝ (deriv Q) (Set.Ioi 0))
    (hQode : ∀ y : ℝ, 0 < y →
      (y : ℂ) ^ 2 * deriv (deriv Q) y
        + (1 / 4 - ν ^ 2 - 2 * (Real.pi : ℂ) * c * (y : ℂ) - 4 * (Real.pi : ℂ) ^ 2 * (y : ℂ) ^ 2) * Q y = 0)
    (hC : C ≠ 0) (ha : a = 1 / 2 ∨ a = 3 / 2)
    (hH : ∀ y : ℝ, 0 < y → P y + ε * Q y = C * (y : ℂ) ^ a * besselKernel μ (2 * Real.pi * y)) :
    μ ^ 2 = ν ^ 2 := by p2m_exact_reverting @_root_.P2MW.S_LanglandsTunnell_ArchBessel_sq_eq_sq_of_whittakerODE_pair_of_add_mul_eq_mul_cpow_mul_besselKernel.solution
