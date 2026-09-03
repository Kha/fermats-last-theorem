import Mathlib.Analysis.SpecialFunctions.Pow.Complex
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import P2M.Util
import P2M.Sol.S_MeanSquare_eq_zero_of_re_lt_one_half_or_log_of_liminf_sub_one_mul_lintegral_cpow_log_sq_le

set_option autoImplicit false

open MeasureTheory
open scoped ENNReal

theorem MeanSquare.eq_zero_of_re_lt_one_half_or_log_of_liminf_sub_one_mul_lintegral_cpow_log_sq_le
    (n J : ℕ) (e : Fin n → ℂ) (he : Function.Injective e) (d : Fin n → Fin J → ℂ)
    (hM : ∃ C : ℝ, ∀ ε : ℝ, 0 < ε → ∃ σ : ℝ, 1 < σ ∧ σ < 1 + ε ∧
      ENNReal.ofReal (σ - 1) *
          ∫⁻ y in Set.Ioc (0 : ℝ) 1,
            (‖∑ i : Fin n, ∑ j : Fin J, d i j * ((y : ℂ) ^ e i * ((Real.log y : ℝ) : ℂ) ^ (j : ℕ))‖₊ : ℝ≥0∞) ^ 2 *
              ENNReal.ofReal (y ^ (σ - 3)) ∂volume ≤
        ENNReal.ofReal C) :
    ∀ (i : Fin n) (j : Fin J), ((e i).re < 1 / 2 ∨ ((e i).re = 1 / 2 ∧ 1 ≤ (j : ℕ))) → d i j = 0 := by p2m_exact_reverting @_root_.P2MW.S_MeanSquare_eq_zero_of_re_lt_one_half_or_log_of_liminf_sub_one_mul_lintegral_cpow_log_sq_le.solution
