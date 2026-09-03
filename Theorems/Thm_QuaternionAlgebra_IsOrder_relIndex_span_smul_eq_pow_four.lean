import Mathlib
import Definitions.Def_QuaternionAlgebra_Order
import P2M.Util
import P2M.Sol.S_QuaternionAlgebra_IsOrder_relIndex_span_smul_eq_pow_four

set_option autoImplicit false

open scoped Quaternion
open QuaternionAlgebra

theorem QuaternionAlgebra.IsOrder.relIndex_span_smul_eq_pow_four
    {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]} (hΛ : IsOrder Λ) (n : ℕ) (hn : 0 < n) :
    (Submodule.span ℤ ((fun y : ℍ[ℚ, a, b] => (n : ℤ) • y) '' (Λ : Set ℍ[ℚ, a, b]))).toAddSubgroup.relIndex
        Λ.toAddSubgroup = n ^ 4 := by p2m_exact_reverting @_root_.P2MW.S_QuaternionAlgebra_IsOrder_relIndex_span_smul_eq_pow_four.solution
