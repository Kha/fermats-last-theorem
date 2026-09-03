import Mathlib
import P2M.Util
import P2M.Sol.S_NumberField_exists_differentiable_eq_sub_one_mul_dedekindZeta_and_apply_neg_two_mul_add_one_eq_zero

set_option autoImplicit false

open IsDedekindDomain NumberField

theorem NumberField.exists_differentiable_eq_sub_one_mul_dedekindZeta_and_apply_neg_two_mul_add_one_eq_zero
    (K : Type) [Field K] [NumberField K] :
    ∃ R : ℂ → ℂ, Differentiable ℂ R ∧ R 1 ≠ 0 ∧
      (∀ s : ℂ, 1 < s.re → R s = (s - 1) * NumberField.dedekindZeta K s) ∧
      ∀ n : ℕ, R (-2 * (n + 1)) = 0 := by p2m_exact_reverting @_root_.P2MW.S_NumberField_exists_differentiable_eq_sub_one_mul_dedekindZeta_and_apply_neg_two_mul_add_one_eq_zero.solution
