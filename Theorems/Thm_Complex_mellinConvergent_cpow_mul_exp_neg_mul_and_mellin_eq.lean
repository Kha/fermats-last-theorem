import Mathlib.Analysis.MellinTransform
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Gamma.Beta
import P2M.Util
import P2M.Sol.S_Complex_mellinConvergent_cpow_mul_exp_neg_mul_and_mellin_eq

set_option autoImplicit false

theorem Complex.mellinConvergent_cpow_mul_exp_neg_mul_and_mellin_eq
    (k r : ℝ) (hr : 0 < r) (s : ℂ) (hs : -k < s.re) :
    MellinConvergent (fun t : ℝ => ((t : ℂ) ^ (k : ℂ)) * Complex.exp (-((r : ℂ) * (t : ℂ)))) s ∧
    mellin (fun t : ℝ => ((t : ℂ) ^ (k : ℂ)) * Complex.exp (-((r : ℂ) * (t : ℂ)))) s =
      (1 / (r : ℂ)) ^ (s + (k : ℂ)) * Complex.Gamma (s + (k : ℂ)) := by p2m_exact_reverting @_root_.P2MW.S_Complex_mellinConvergent_cpow_mul_exp_neg_mul_and_mellin_eq.solution
