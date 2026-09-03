import Mathlib
import Definitions.Def_QuaternionAlgebra_EichlerOrder
import P2M.Util
import P2M.Sol.S_QuaternionAlgebra_IsMaximalOrder_map_algEquiv

set_option autoImplicit false

open scoped Quaternion

theorem QuaternionAlgebra.IsMaximalOrder.map_algEquiv {a b a' b' : ℚ}
    (e : ℍ[ℚ, a, b] ≃ₐ[ℚ] ℍ[ℚ, a', b']) {Λ : Submodule ℤ ℍ[ℚ, a, b]}
    (hΛ : QuaternionAlgebra.IsMaximalOrder Λ) :
    QuaternionAlgebra.IsMaximalOrder (Λ.map (e.toLinearMap.restrictScalars ℤ)) := by p2m_exact_reverting @_root_.P2MW.S_QuaternionAlgebra_IsMaximalOrder_map_algEquiv.solution
