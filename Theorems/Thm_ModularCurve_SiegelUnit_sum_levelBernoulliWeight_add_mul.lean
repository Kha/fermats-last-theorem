import Mathlib
import P2M.Util
import P2M.Sol.S_ModularCurve_SiegelUnit_sum_levelBernoulliWeight_add_mul

set_option autoImplicit false

theorem ModularCurve.SiegelUnit.sum_levelBernoulliWeight_add_mul (N : ℕ) [NeZero N] (p r : ℤ) :
    ∑ s : ZMod N,
        (6 * ((((p : ZMod N) + s * (r : ZMod N)).val : ℕ) : ℤ) ^ 2
          - 6 * (N : ℤ) * ((((p : ZMod N) + s * (r : ZMod N)).val : ℕ) : ℤ) + (N : ℤ) ^ 2) =
      (N : ℤ) * (6 * (p % (Int.gcd r N : ℤ)) ^ 2
        - 6 * (Int.gcd r N : ℤ) * (p % (Int.gcd r N : ℤ)) + (Int.gcd r N : ℤ) ^ 2) := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_SiegelUnit_sum_levelBernoulliWeight_add_mul.solution
