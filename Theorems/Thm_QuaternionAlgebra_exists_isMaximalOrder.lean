import Mathlib
import Definitions.Def_QuaternionAlgebra_EichlerOrder
import P2M.Util
import P2M.Sol.S_QuaternionAlgebra_exists_isMaximalOrder

set_option autoImplicit false

open scoped TensorProduct Quaternion
open IsDedekindDomain NumberField

theorem QuaternionAlgebra.exists_isMaximalOrder (a b : ℚ) (ha : a ≠ 0) (hb : b ≠ 0) :
    ∃ Λ : Submodule ℤ ℍ[ℚ, a, b], QuaternionAlgebra.IsMaximalOrder Λ := by p2m_exact_reverting @_root_.P2MW.S_QuaternionAlgebra_exists_isMaximalOrder.solution
