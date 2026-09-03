import Definitions.Def_LanglandsTunnell_ArchParam
import Mathlib.Analysis.MellinTransform
import Mathlib.Analysis.MellinInversion
import P2M.Util
import P2M.Sol.S_LanglandsTunnell_add_pow_mul_apply_neg_eq_mul_mulConvGaussian_of_mellin_sheet_eq_archFactor

set_option autoImplicit false

open scoped Real
p2m_open "LanglandsTunnell~mellin_mulConvGaussian_eq_archFactor_principal"

theorem LanglandsTunnell.add_pow_mul_apply_neg_eq_mul_mulConvGaussian_of_mellin_sheet_eq_archFactor
    (u₁ u₂ : ℂ) (a₁ a₂ : ZMod 2) (W : ℝ → ℂ)
    (hWc : ContinuousOn W {t : ℝ | t ≠ 0}) (b : ZMod 2)
    (hMel : ∃ s₀ : ℝ, ∀ s : ℂ, s₀ < s.re →
      MellinConvergent (fun t : ℝ => (W t + (-1 : ℂ) ^ b.val * W (-t)) / (t : ℂ)) s ∧
        mellin (fun t : ℝ => (W t + (-1 : ℂ) ^ b.val * W (-t)) / (t : ℂ)) s
          = ((RealArchParam.principal u₁ a₁ u₂ a₂).twist 0 b).archFactor s)
    (t : ℝ) (ht : 0 < t) :
    W t + (-1 : ℂ) ^ b.val * W (-t) =
      (t : ℂ) * ((4 : ℂ) * ∫ r in Set.Ioi (0 : ℝ),
        ((r : ℂ) ^ (u₁ + signShift (a₁ + b)) * (Real.exp (-(π * r ^ 2)) : ℂ)) *
          (((t / r : ℝ) : ℂ) ^ (u₂ + signShift (a₂ + b)) * (Real.exp (-(π * (t / r) ^ 2)) : ℂ)) / (r : ℂ)) := by p2m_exact_reverting @_root_.P2MW.S_LanglandsTunnell_add_pow_mul_apply_neg_eq_mul_mulConvGaussian_of_mellin_sheet_eq_archFactor.solution
