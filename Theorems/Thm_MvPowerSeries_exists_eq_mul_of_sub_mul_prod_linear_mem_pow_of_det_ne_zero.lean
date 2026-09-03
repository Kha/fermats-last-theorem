import Mathlib
import P2M.Util
import P2M.Sol.S_MvPowerSeries_exists_eq_mul_of_sub_mul_prod_linear_mem_pow_of_det_ne_zero

set_option autoImplicit false

universe u v

p2m_open "MvPowerSeries~exists_algEquiv_apply_X_eq~span_singleton_isPrime_of_sub_linear_mem_sq~exists_eq_X_sub_subst_mul_of_subst_eq_zero"

theorem MvPowerSeries.exists_eq_mul_of_sub_mul_prod_linear_mem_pow_of_det_ne_zero
    {κ : Type u} [Field κ] {ι : Type v} [Fintype ι]
    (a b : κ) (hab : a ≠ 0 ∨ b ≠ 0)
    (A B : ι → κ) (hsimple : ∀ i, a * B i - A i * b ≠ 0)
    (f : MvPowerSeries (Fin 2) κ)
    (hf : f - (C a * X 0 + C b * X 1) * ∏ i, (C (A i) * X 0 + C (B i) * X 1) ∈
      (Ideal.span {(X 0 : MvPowerSeries (Fin 2) κ), X 1}) ^ (Fintype.card ι + 2)) :
    ∃ (L f₁ : MvPowerSeries (Fin 2) κ),
      L - (C a * X 0 + C b * X 1) ∈ (Ideal.span {(X 0 : MvPowerSeries (Fin 2) κ), X 1}) ^ 2 ∧
      f₁ - ∏ i, (C (A i) * X 0 + C (B i) * X 1) ∈
        (Ideal.span {(X 0 : MvPowerSeries (Fin 2) κ), X 1}) ^ (Fintype.card ι + 1) ∧
      f = L * f₁ := by p2m_exact_reverting @_root_.P2MW.S_MvPowerSeries_exists_eq_mul_of_sub_mul_prod_linear_mem_pow_of_det_ne_zero.solution
