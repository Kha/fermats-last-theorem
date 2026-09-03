import Definitions.Def_UnramifiedWhittaker_HeckeRecursion
import P2M.Util
import P2M.Sol.S_LanglandsTunnell_CubicInduction_eq_zero_of_forall_sum_mul_pow_mul_heckeRecursionSeq_eq_zero

set_option autoImplicit false

theorem LanglandsTunnell.CubicInduction.eq_zero_of_forall_sum_mul_pow_mul_heckeRecursionSeq_eq_zero
    (d : ℕ) (c : ℕ → ℂ)
    (h : ∀ a₁ a₂ : ℂ, a₁ * a₂ ≠ 0 →
      ∑ j ∈ Finset.range (d / 2 + 1),
        c j * (a₁ * a₂) ^ j * UnramifiedWhittaker.heckeRecursionSeq 1 (a₁ + a₂) (a₁ * a₂) (d - 2 * j) = 0) :
    ∀ j : ℕ, j ≤ d / 2 → c j = 0 := by p2m_exact_reverting @_root_.P2MW.S_LanglandsTunnell_CubicInduction_eq_zero_of_forall_sum_mul_pow_mul_heckeRecursionSeq_eq_zero.solution
