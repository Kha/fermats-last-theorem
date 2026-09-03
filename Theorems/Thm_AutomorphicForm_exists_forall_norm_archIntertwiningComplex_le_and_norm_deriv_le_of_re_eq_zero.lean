import Mathlib
import P2M.Util
import P2M.Sol.S_AutomorphicForm_exists_forall_norm_archIntertwiningComplex_le_and_norm_deriv_le_of_re_eq_zero

set_option autoImplicit false

theorem AutomorphicForm.exists_forall_norm_archIntertwiningComplex_le_and_norm_deriv_le_of_re_eq_zero
    (a m M : ℕ) (hm : 2 * a ≤ m) (hM : m = 2 * a → M = 0) :
    let N : ℂ → ℂ := fun W => ((a.factorial : ℕ) : ℂ) / 2 *
      (if m = 2 * a ∧ M = 0 then
        Complex.Gamma (W + 1) * (Complex.Gamma (W + 1 + (a : ℂ)))⁻¹
      else
        (W + (M : ℂ) / 2) * Complex.Gamma (W + (m : ℂ) / 2 - (a : ℂ)) * (Complex.Gamma (W + (m : ℂ) / 2 + 1))⁻¹)
    ∃ C : ℝ, 0 ≤ C ∧ ∀ W : ℂ, W.re = 0 → ‖N W‖ ≤ C ∧ DifferentiableAt ℂ N W ∧ ‖deriv N W‖ ≤ C := by p2m_exact_reverting @_root_.P2MW.S_AutomorphicForm_exists_forall_norm_archIntertwiningComplex_le_and_norm_deriv_le_of_re_eq_zero.solution
