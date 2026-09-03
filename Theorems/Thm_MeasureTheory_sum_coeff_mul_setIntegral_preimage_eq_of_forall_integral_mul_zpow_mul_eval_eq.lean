import Mathlib
import P2M.Util
import P2M.Sol.S_MeasureTheory_sum_coeff_mul_setIntegral_preimage_eq_of_forall_integral_mul_zpow_mul_eval_eq

set_option autoImplicit false

open MeasureTheory

theorem MeasureTheory.sum_coeff_mul_setIntegral_preimage_eq_of_forall_integral_mul_zpow_mul_eval_eq
    {T : Type*} [MeasurableSpace T] (μ : Measure T) (d : T → ℤ) (hd : Measurable d)
    (g : T → ℂ) {a b : ℝ} (ha : 0 ≤ a) (hab : a < b)
    (hg : ∀ Y : ℂ, a < ‖Y‖ → ‖Y‖ < b → Integrable (fun t => g t * Y ^ d t) μ)
    (Q P : Polynomial ℂ) (n : ℤ)
    (hfe : ∀ Y : ℂ, a < ‖Y‖ → ‖Y‖ < b →
      (∫ t, g t * Y ^ d t ∂μ) * Q.eval Y = P.eval Y * Y ^ n)
    (j : ℤ) :
    ∑ i ∈ Q.support, Q.coeff i * ∫ t in d ⁻¹' {j - (i : ℤ)}, g t ∂μ =
      if n ≤ j then P.coeff (j - n).toNat else 0 := by p2m_exact_reverting @_root_.P2MW.S_MeasureTheory_sum_coeff_mul_setIntegral_preimage_eq_of_forall_integral_mul_zpow_mul_eval_eq.solution
