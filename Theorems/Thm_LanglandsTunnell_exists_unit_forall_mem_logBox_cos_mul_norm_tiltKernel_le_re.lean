import Mathlib.Analysis.SpecialFunctions.Pow.Complex
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Complex.Log
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import P2M.Util
import P2M.Sol.S_LanglandsTunnell_exists_unit_forall_mem_logBox_cos_mul_norm_tiltKernel_le_re

set_option autoImplicit false

open MeasureTheory Set

theorem LanglandsTunnell.exists_unit_forall_mem_logBox_cos_mul_norm_tiltKernel_le_re
    (S A B : ℂ) (δ ℓw ℓr : ℝ) (hδ : 0 ≤ δ)
    (hΔ : ((abs A.im) + (abs B.im)) * δ + (abs S.im) * Real.exp (4 * δ) * Real.exp (-(2 * (ℓw + ℓr))) ≤ Real.pi) :
    ∃ u : ℂ, ‖u‖ = 1 ∧ ∀ (w r M : ℝ), 0 ≤ M →
      w ∈ Icc (Real.exp (ℓw - δ)) (Real.exp (ℓw + δ)) → r ∈ Icc (Real.exp (ℓr - δ)) (Real.exp (ℓr + δ)) →
      Real.cos (((abs A.im) + (abs B.im)) * δ + (abs S.im) * Real.exp (4 * δ) * Real.exp (-(2 * (ℓw + ℓr)))) *
          ‖((1 + ((w * r) ^ 2)⁻¹ : ℝ) : ℂ) ^ (-S) * ((w : ℝ) : ℂ) ^ A * ((r : ℝ) : ℂ) ^ B * (M : ℂ)‖
        ≤ (u * (((1 + ((w * r) ^ 2)⁻¹ : ℝ) : ℂ) ^ (-S) * ((w : ℝ) : ℂ) ^ A * ((r : ℝ) : ℂ) ^ B * (M : ℂ))).re := by p2m_exact_reverting @_root_.P2MW.S_LanglandsTunnell_exists_unit_forall_mem_logBox_cos_mul_norm_tiltKernel_le_re.solution
