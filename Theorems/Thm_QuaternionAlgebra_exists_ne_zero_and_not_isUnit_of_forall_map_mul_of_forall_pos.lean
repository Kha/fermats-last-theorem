import Mathlib
import P2M.Util
import P2M.Sol.S_QuaternionAlgebra_exists_ne_zero_and_not_isUnit_of_forall_map_mul_of_forall_pos

set_option autoImplicit false

open scoped Quaternion

theorem QuaternionAlgebra.exists_ne_zero_and_not_isUnit_of_forall_map_mul_of_forall_pos
    {a b : ℚ} (hab : 0 < a ∨ 0 < b) (Q : QuadraticMap ℚ ℍ[ℚ, a, b] ℚ)
    (hmul : ∀ x y : ℍ[ℚ, a, b], Q (x * y) = Q x * Q y) (hpos : ∀ x : ℍ[ℚ, a, b], x ≠ 0 → 0 < Q x) :
    ∃ x : ℍ[ℚ, a, b], x ≠ 0 ∧ ¬ IsUnit x := by p2m_exact_reverting @_root_.P2MW.S_QuaternionAlgebra_exists_ne_zero_and_not_isUnit_of_forall_map_mul_of_forall_pos.solution
