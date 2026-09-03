import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.MeasureTheory.Measure.Lebesgue.Complex
import P2M.Util
import P2M.Sol.S_AutomorphicForm_RealIwasawa_exists_forall_norm_weightFourierIntegral_continuation_le_mul_pow_abs_im_mul_pow_of_re_mem_Icc

open Set MeasureTheory
set_option autoImplicit false

theorem AutomorphicForm.RealIwasawa.exists_forall_norm_weightFourierIntegral_continuation_le_mul_pow_abs_im_mul_pow_of_re_mem_Icc
    (k : ℤ) (σ₁ σ₂ : ℝ) :
    let j : ℂ → ℝ → ℂ := fun w t => ∫ x : ℝ, ((((x : ℝ) : ℂ) - Complex.I) / ((Real.sqrt (1 + x ^ 2) : ℝ) : ℂ)) ^ k
          * (((1 + x ^ 2 : ℝ) : ℂ)) ^ (-w)
          * Complex.exp (-(((2 * Real.pi * t * x : ℝ) : ℂ) * Complex.I))
    ∃ A₀ : ℕ, ∀ N : ℕ, ∃ (C : ℝ) (A : ℕ), 0 < C ∧
      ∀ (t : ℝ), t ≠ 0 → ∀ (J : ℂ → ℂ), Differentiable ℂ J → (∀ w : ℂ, 1 / 2 < w.re → J w = j w t) →
        ∀ w : ℂ, σ₁ ≤ w.re → w.re ≤ σ₂ →
          ‖J w‖ ≤ C * (1 + |w.im|) ^ A * (max 1 |t|⁻¹) ^ A₀ * (1 + |t|) ^ (-(N : ℝ)) := by p2m_exact_reverting @_root_.P2MW.S_AutomorphicForm_RealIwasawa_exists_forall_norm_weightFourierIntegral_continuation_le_mul_pow_abs_im_mul_pow_of_re_mem_Icc.solution
