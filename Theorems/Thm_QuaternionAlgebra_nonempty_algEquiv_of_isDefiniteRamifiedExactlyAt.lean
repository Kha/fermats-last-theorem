import Mathlib
import Definitions.Def_QuaternionAlgebra_EichlerOrder
import P2M.Util
import P2M.Sol.S_QuaternionAlgebra_nonempty_algEquiv_of_isDefiniteRamifiedExactlyAt
attribute [-simp] QuaternionAlgebra.baseChangeRight_tmul QuaternionAlgebra.mapOfAlgebraMapEq_apply QuaternionAlgebra.baseChange_tmul

set_option autoImplicit false

open scoped Quaternion

theorem QuaternionAlgebra.nonempty_algEquiv_of_isDefiniteRamifiedExactlyAt
    {q : ℕ} [Fact q.Prime] {a b c d : ℚ}
    (h₁ : QuaternionAlgebra.IsDefiniteRamifiedExactlyAt a b q)
    (h₂ : QuaternionAlgebra.IsDefiniteRamifiedExactlyAt c d q) :
    Nonempty (ℍ[ℚ, a, b] ≃ₐ[ℚ] ℍ[ℚ, c, d]) := by p2m_exact_reverting @_root_.P2MW.S_QuaternionAlgebra_nonempty_algEquiv_of_isDefiniteRamifiedExactlyAt.solution
