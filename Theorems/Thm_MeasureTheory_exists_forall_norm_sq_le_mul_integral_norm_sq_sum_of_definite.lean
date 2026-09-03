import Mathlib
import P2M.Util
import P2M.Sol.S_MeasureTheory_exists_forall_norm_sq_le_mul_integral_norm_sq_sum_of_definite

set_option autoImplicit false

open MeasureTheory
open scoped ComplexConjugate

theorem MeasureTheory.exists_forall_norm_sq_le_mul_integral_norm_sq_sum_of_definite
    {X : Type*} [MeasurableSpace X] (μ : Measure X) {n : ℕ} (b : Fin n → X → ℂ)
    (hint : ∀ i j : Fin n, Integrable (fun x => b i x * conj (b j x)) μ)
    (hdef : ∀ a : Fin n → ℂ, (∫ x, ‖∑ j, a j * b j x‖ ^ 2 ∂μ) = 0 → a = 0) :
    ∃ C : ℝ, 0 < C ∧ ∀ (a : Fin n → ℂ) (i : Fin n), ‖a i‖ ^ 2 ≤ C * ∫ x, ‖∑ j, a j * b j x‖ ^ 2 ∂μ := by p2m_exact_reverting @_root_.P2MW.S_MeasureTheory_exists_forall_norm_sq_le_mul_integral_norm_sq_sum_of_definite.solution
