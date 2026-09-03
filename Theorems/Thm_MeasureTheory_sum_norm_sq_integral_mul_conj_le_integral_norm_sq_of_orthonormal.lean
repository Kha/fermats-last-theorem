import Mathlib
import P2M.Util
import P2M.Sol.S_MeasureTheory_sum_norm_sq_integral_mul_conj_le_integral_norm_sq_of_orthonormal

set_option autoImplicit false

open MeasureTheory
open scoped ComplexConjugate

theorem MeasureTheory.sum_norm_sq_integral_mul_conj_le_integral_norm_sq_of_orthonormal
    {X : Type*} [MeasurableSpace X] (μ : Measure X) {n : ℕ} (e : Fin n → X → ℂ)
    (hint : ∀ i j, Integrable (fun x => e i x * conj (e j x)) μ)
    (hon : ∀ i j, ∫ x, e i x * conj (e j x) ∂μ = if i = j then 1 else 0)
    (w : X → ℂ) (hw : Integrable (fun x => ‖w x‖ ^ 2) μ)
    (hwe : ∀ j, Integrable (fun x => w x * conj (e j x)) μ) :
    ∑ j, ‖∫ x, w x * conj (e j x) ∂μ‖ ^ 2 ≤ ∫ x, ‖w x‖ ^ 2 ∂μ := by p2m_exact_reverting @_root_.P2MW.S_MeasureTheory_sum_norm_sq_integral_mul_conj_le_integral_norm_sq_of_orthonormal.solution
