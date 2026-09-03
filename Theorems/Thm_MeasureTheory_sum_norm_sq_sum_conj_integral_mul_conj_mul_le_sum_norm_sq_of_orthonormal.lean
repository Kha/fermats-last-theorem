import Mathlib
import P2M.Util
import P2M.Sol.S_MeasureTheory_sum_norm_sq_sum_conj_integral_mul_conj_mul_le_sum_norm_sq_of_orthonormal

set_option autoImplicit false

open MeasureTheory
open scoped ComplexConjugate

theorem MeasureTheory.sum_norm_sq_sum_conj_integral_mul_conj_mul_le_sum_norm_sq_of_orthonormal
    {X : Type*} [MeasurableSpace X] (μ : Measure X) {n m : ℕ}
    (e : Fin n → X → ℂ) (f : Fin m → X → ℂ)
    (_he : ∀ i, MemLp (e i) 2 μ) (_hf : ∀ j, MemLp (f j) 2 μ)
    (_heon : ∀ i i' : Fin n, ∫ x, e i x * conj (e i' x) ∂μ = if i = i' then 1 else 0)
    (_hfon : ∀ j j' : Fin m, ∫ x, f j x * conj (f j' x) ∂μ = if j = j' then 1 else 0)
    (x : Fin m → ℂ) :
    ∑ i : Fin n, ‖∑ j' : Fin m, conj (∫ y, e i y * conj (f j' y) ∂μ) * x j'‖ ^ 2 ≤ ∑ j' : Fin m, ‖x j'‖ ^ 2 := by p2m_exact_reverting @_root_.P2MW.S_MeasureTheory_sum_norm_sq_sum_conj_integral_mul_conj_mul_le_sum_norm_sq_of_orthonormal.solution
