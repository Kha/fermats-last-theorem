import Mathlib
import Definitions.Def_QuaternionAlgebra_Order
import Definitions.Def_QuaternionAlgebra_ReducedNorm
import P2M.Util
import P2M.Sol.S_QuaternionAlgebra_exists_subalgebra_coe_eq_setOf_norm_nrd_le_one_fg_span_eq_top_of_forall_isUnit

set_option autoImplicit false

open scoped Quaternion

theorem QuaternionAlgebra.exists_subalgebra_coe_eq_setOf_norm_nrd_le_one_fg_span_eq_top_of_forall_isUnit
    (p : ℕ) [Fact p.Prime] (a b : ℚ_[p])
    (hdiv : ∀ x : ℍ[ℚ_[p], a, b], x ≠ 0 → IsUnit x) :
    ∃ O : Subalgebra ℤ_[p] ℍ[ℚ_[p], a, b],
      (O : Set ℍ[ℚ_[p], a, b]) = {z | ‖QuaternionAlgebra.nrd z‖ ≤ 1} ∧
      (Subalgebra.toSubmodule O).FG ∧
      Submodule.span ℚ_[p] (O : Set ℍ[ℚ_[p], a, b]) = ⊤ := by p2m_exact_reverting @_root_.P2MW.S_QuaternionAlgebra_exists_subalgebra_coe_eq_setOf_norm_nrd_le_one_fg_span_eq_top_of_forall_isUnit.solution
