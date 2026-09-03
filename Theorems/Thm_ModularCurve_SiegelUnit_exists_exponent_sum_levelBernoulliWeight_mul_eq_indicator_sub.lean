import Mathlib
import P2M.Util
import P2M.Sol.S_ModularCurve_SiegelUnit_exists_exponent_sum_levelBernoulliWeight_mul_eq_indicator_sub

set_option autoImplicit false

theorem ModularCurve.SiegelUnit.exists_exponent_sum_levelBernoulliWeight_mul_eq_indicator_sub
    (q : ℕ) [Fact q.Prime] :
    ∃ (μ : ZMod q → ℕ) (t e : ℕ), μ 0 = 0 ∧ 0 < e ∧
      ∀ x : ZMod q, x ≠ 0 →
        ∑ r : ZMod q, (μ r : ℤ) *
            (6 * (((r * x).val : ℕ) : ℤ) ^ 2 - 6 * (q : ℤ) * (((r * x).val : ℕ) : ℤ) + (q : ℤ) ^ 2) =
          (if x = 1 ∨ x = -1 then (e : ℤ) else 0) - (t : ℤ) := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_SiegelUnit_exists_exponent_sum_levelBernoulliWeight_mul_eq_indicator_sub.solution
