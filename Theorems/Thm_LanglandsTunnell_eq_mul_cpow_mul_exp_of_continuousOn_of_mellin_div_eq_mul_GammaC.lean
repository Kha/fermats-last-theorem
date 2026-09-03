import Mathlib.Analysis.MellinTransform
import Mathlib.Analysis.SpecialFunctions.Gamma.Deligne
import P2M.Util
import P2M.Sol.S_LanglandsTunnell_eq_mul_cpow_mul_exp_of_continuousOn_of_mellin_div_eq_mul_GammaC

set_option autoImplicit false

open Complex

theorem LanglandsTunnell.eq_mul_cpow_mul_exp_of_continuousOn_of_mellin_div_eq_mul_GammaC
    (Wr : ℝ → ℂ) (A ν : ℂ) (σ₀ : ℝ)
    (hcont : ContinuousOn Wr (Set.Ioi 0))
    (hM : ∀ s : ℂ, σ₀ < s.re →
      MellinConvergent (fun t : ℝ => Wr t / (t : ℂ)) s ∧
        mellin (fun t : ℝ => Wr t / (t : ℂ)) s = A * Complex.Gammaℂ (s + ν)) :
    ∀ t : ℝ, 0 < t →
      Wr t = 2 * A * ((t : ℂ) ^ (ν + 1)) * Complex.exp (-(2 * Real.pi * t : ℝ)) := by p2m_exact_reverting @_root_.P2MW.S_LanglandsTunnell_eq_mul_cpow_mul_exp_of_continuousOn_of_mellin_div_eq_mul_GammaC.solution
