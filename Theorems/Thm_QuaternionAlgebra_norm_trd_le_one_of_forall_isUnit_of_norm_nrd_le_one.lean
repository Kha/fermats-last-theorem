import Mathlib
import Definitions.Def_QuaternionAlgebra_Order
import Definitions.Def_QuaternionAlgebra_ReducedNorm
import P2M.Util
import P2M.Sol.S_QuaternionAlgebra_norm_trd_le_one_of_forall_isUnit_of_norm_nrd_le_one

set_option autoImplicit false

open scoped Quaternion

theorem QuaternionAlgebra.norm_trd_le_one_of_forall_isUnit_of_norm_nrd_le_one
    (p : ℕ) [Fact p.Prime] (a b : ℚ_[p])
    (hdiv : ∀ x : ℍ[ℚ_[p], a, b], x ≠ 0 → IsUnit x)
    (z : ℍ[ℚ_[p], a, b]) (hz : ‖QuaternionAlgebra.nrd z‖ ≤ 1) :
    ‖QuaternionAlgebra.trd z‖ ≤ 1 := by p2m_exact_reverting @_root_.P2MW.S_QuaternionAlgebra_norm_trd_le_one_of_forall_isUnit_of_norm_nrd_le_one.solution
