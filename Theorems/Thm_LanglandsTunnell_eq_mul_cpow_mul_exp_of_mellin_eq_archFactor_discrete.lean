import Definitions.Def_LanglandsTunnell_ArchParam
import Mathlib.Analysis.MellinTransform
import Mathlib.Analysis.MellinInversion
import P2M.Util
import P2M.Sol.S_LanglandsTunnell_eq_mul_cpow_mul_exp_of_mellin_eq_archFactor_discrete

set_option autoImplicit false

open scoped Real
open LanglandsTunnell

theorem LanglandsTunnell.eq_mul_cpow_mul_exp_of_mellin_eq_archFactor_discrete
    (u : ℂ) (n : ℕ) (hn : 1 ≤ n) (W : ℝ → ℂ)
    (hWc : ContinuousOn W {t : ℝ | t ≠ 0})
    (hneg : ∀ t : ℝ, t < 0 → W t = 0)
    (hMel : ∃ s₀ : ℝ, ∀ s : ℂ, s₀ < s.re →
      MellinConvergent (fun t : ℝ => W t / (t : ℂ)) s ∧
        mellin (fun t : ℝ => W t / (t : ℂ)) s = (RealArchParam.discrete u n hn).archFactor s)
    (t : ℝ) (ht : 0 < t) :
    W t = (2 : ℂ) * (t : ℂ) ^ (u + (n : ℂ) / 2 + 1) * (Real.exp (-(2 * π * t)) : ℂ) := by p2m_exact_reverting @_root_.P2MW.S_LanglandsTunnell_eq_mul_cpow_mul_exp_of_mellin_eq_archFactor_discrete.solution
