import Definitions.Def_LanglandsTunnell_CubicInduction_JacquetVector3
import Mathlib.Analysis.MellinTransform
import P2M.Util
import P2M.Sol.S_LanglandsTunnell_Converse_ArchDatumR_exists_lt_re_mellin_gaussian_mul_integral_twoSheet_torusKernel_ne_zero

set_option autoImplicit false

p2m_open "NumberField AutomorphicForm LanglandsTunnell~mellinConvergent_and_mellin_ofReal_pos_rpow_mul_exp_neg_mul_sq_add_inv_sq~mellinConvergent_integral_mul_comp_mul_and_mellin_eq_mellin_mul_mellin LanglandsTunnell.Converse MeasureTheory"

open LanglandsTunnell.Converse.ArchR Set in

theorem LanglandsTunnell.Converse.ArchDatumR.exists_lt_re_mellin_gaussian_mul_integral_twoSheet_torusKernel_ne_zero
    {P₂ : RealArchParam} (D : ArchDatumR P₂) (a : ℝ) (ha : a ≠ 0) (ν : ℂ) (ε : ℂ) (hε : ε = 1 ∨ ε = -1)
    (hg : ∃ τ : ℝ, 0 < τ ∧ D.W (ArchR.diagOne τ) + ε * D.W (ArchR.diagOne (-τ)) ≠ 0)
    (H : ℝ → ℂ)
    (hH : H = fun σ' => (Real.exp (-(Real.pi * a ^ 2 * σ' ^ 2)) : ℂ) *
        ∫ w in Set.Ioi (0 : ℝ),
          (D.W (ArchR.diagOne (a * (σ' / w))) + ε * D.W (ArchR.diagOne (-(a * (σ' / w))))) *
            (ArchR.centralChar P₂ w * ((|w| : ℝ) : ℂ)) * ((w : ℝ) : ℂ) ^ ν *
            (Real.exp (-(Real.pi * ((w ^ 2)⁻¹ + a ^ 2 * w ^ 2))) : ℂ))
    (hHc : ContinuousOn H (Set.Ioi 0)) (x₀ : ℝ) :
    ∃ s : ℂ, x₀ < s.re ∧ mellin H (s - 1) ≠ 0 := by p2m_exact_reverting @_root_.P2MW.S_LanglandsTunnell_Converse_ArchDatumR_exists_lt_re_mellin_gaussian_mul_integral_twoSheet_torusKernel_ne_zero.solution
