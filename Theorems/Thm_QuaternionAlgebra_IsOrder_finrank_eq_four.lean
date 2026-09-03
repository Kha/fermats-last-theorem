import Mathlib
import Definitions.Def_QuaternionAlgebra_Order
import P2M.Util
import P2M.Sol.S_QuaternionAlgebra_IsOrder_finrank_eq_four

open scoped Quaternion

theorem QuaternionAlgebra.IsOrder.finrank_eq_four {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]}
    (hΛ : QuaternionAlgebra.IsOrder Λ) : Module.finrank ℤ Λ = 4 := by p2m_exact_reverting @_root_.P2MW.S_QuaternionAlgebra_IsOrder_finrank_eq_four.solution
