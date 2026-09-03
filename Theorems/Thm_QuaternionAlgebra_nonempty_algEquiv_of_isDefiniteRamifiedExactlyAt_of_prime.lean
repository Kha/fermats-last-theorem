import Mathlib
import Definitions.Def_QuaternionAlgebra_EichlerOrder
import P2M.Util
import P2M.Sol.S_QuaternionAlgebra_nonempty_algEquiv_of_isDefiniteRamifiedExactlyAt_of_prime
attribute [-simp] QuaternionAlgebra.baseChangeRight_tmul QuaternionAlgebra.mapOfAlgebraMapEq_apply QuaternionAlgebra.baseChange_tmul

set_option autoImplicit false

open scoped TensorProduct Quaternion
open IsDedekindDomain NumberField

theorem QuaternionAlgebra.nonempty_algEquiv_of_isDefiniteRamifiedExactlyAt_of_prime
    (a b a' b' : ℚ) (q : ℕ) (hq : q.Prime)
    (h : QuaternionAlgebra.IsDefiniteRamifiedExactlyAt a b q) (h' : QuaternionAlgebra.IsDefiniteRamifiedExactlyAt a' b' q) :
    Nonempty (ℍ[ℚ, a, b] ≃ₐ[ℚ] ℍ[ℚ, a', b']) := by p2m_exact_reverting @_root_.P2MW.S_QuaternionAlgebra_nonempty_algEquiv_of_isDefiniteRamifiedExactlyAt_of_prime.solution
