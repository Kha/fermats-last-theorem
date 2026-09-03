import Mathlib
import P2M.Util
import P2M.Sol.S_AutomorphicForm_archIntertwiningReal_eq_prod_div_and_norm_eq_one_and_norm_deriv_le_of_re_eq_zero

set_option autoImplicit false

theorem AutomorphicForm.archIntertwiningReal_eq_prod_div_and_norm_eq_one_and_norm_deriv_le_of_re_eq_zero
    (k : ℤ) (ε j : ℕ) :
    let N : ℂ → ℂ := fun w => (-Complex.I) ^ k *
        ((∏ i ∈ Finset.range j, ((w + 1 - (ε : ℂ)) / 2 - 1 - (i : ℂ))) / (Real.pi : ℂ) ^ j) *
        Complex.Gammaℝ (w + 1 + (ε : ℂ)) * (Complex.Gammaℝ (w + 1 + ((ε + 2 * j : ℕ) : ℂ)))⁻¹
    (∀ w : ℂ, -1 < w.re → N w = (-Complex.I) ^ k *
        ∏ i ∈ Finset.range j, ((w - ((1 + ε + 2 * i : ℕ) : ℂ)) / (w + ((1 + ε + 2 * i : ℕ) : ℂ)))) ∧
    (∀ w : ℂ, w.re = 0 → ‖N w‖ = 1 ∧ DifferentiableAt ℂ N w ∧ ‖deriv N w‖ ≤ 2 * j) := by p2m_exact_reverting @_root_.P2MW.S_AutomorphicForm_archIntertwiningReal_eq_prod_div_and_norm_eq_one_and_norm_deriv_le_of_re_eq_zero.solution
