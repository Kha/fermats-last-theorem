import Mathlib
import Definitions.Def_QuaternionAlgebra_Order
import Definitions.Def_QuaternionAlgebra_ReducedNorm
import P2M.Util
import P2M.Sol.S_QuaternionAlgebra_norm_nrd_add_le_max_of_forall_isUnit

set_option autoImplicit false

open scoped Quaternion

theorem QuaternionAlgebra.norm_nrd_add_le_max_of_forall_isUnit
    (p : ℕ) [Fact p.Prime] (a b : ℚ_[p])
    (hdiv : ∀ x : ℍ[ℚ_[p], a, b], x ≠ 0 → IsUnit x)
    (x y : ℍ[ℚ_[p], a, b]) :
    ‖QuaternionAlgebra.nrd (x + y)‖ ≤ max ‖QuaternionAlgebra.nrd x‖ ‖QuaternionAlgebra.nrd y‖ := by p2m_exact_reverting @_root_.P2MW.S_QuaternionAlgebra_norm_nrd_add_le_max_of_forall_isUnit.solution
