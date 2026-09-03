import Mathlib
import P2M.Util
import P2M.Sol.S_MeasureTheory_memLp_two_integral_and_integral_norm_sq_integral_le_of_integral_norm_sq_le_of_integrable_one_add_sq_mul

set_option autoImplicit false

open MeasureTheory

theorem MeasureTheory.memLp_two_integral_and_integral_norm_sq_integral_le_of_integral_norm_sq_le_of_integrable_one_add_sq_mul
    {X : Type*} [MeasurableSpace X] (μ : Measure X) [SFinite μ]
    (G : ℝ × X → ℂ) (_hG : AEStronglyMeasurable G ((volume : Measure ℝ).prod μ))
    (M : ℝ → ℝ) (_hM0 : ∀ t, 0 ≤ M t)
    (_hGt : ∀ t : ℝ, MemLp (fun x => G (t, x)) 2 μ ∧ (∫ x, ‖G (t, x)‖ ^ 2 ∂μ) ≤ M t)
    (_hM : Integrable (fun t : ℝ => (1 + t ^ 2) * M t)) :
    MemLp (fun x => ∫ t : ℝ, G (t, x)) 2 μ ∧
    (∫ x, ‖∫ t : ℝ, G (t, x)‖ ^ 2 ∂μ) ≤ Real.pi * ∫ t : ℝ, (1 + t ^ 2) * M t := by p2m_exact_reverting @_root_.P2MW.S_MeasureTheory_memLp_two_integral_and_integral_norm_sq_integral_le_of_integral_norm_sq_le_of_integrable_one_add_sq_mul.solution
