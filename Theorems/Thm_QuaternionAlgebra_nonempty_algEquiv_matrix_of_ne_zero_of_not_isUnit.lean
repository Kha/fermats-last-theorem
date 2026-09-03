import Mathlib
import P2M.Util
import P2M.Sol.S_QuaternionAlgebra_nonempty_algEquiv_matrix_of_ne_zero_of_not_isUnit

set_option autoImplicit false

open scoped Quaternion

theorem QuaternionAlgebra.nonempty_algEquiv_matrix_of_ne_zero_of_not_isUnit
    {F : Type*} [Field F] [NeZero (2 : F)] {a b : F} (ha : a ≠ 0) (hb : b ≠ 0)
    (x : ℍ[F, a, b]) (hx : x ≠ 0) (hxu : ¬ IsUnit x) :
    Nonempty (ℍ[F, a, b] ≃ₐ[F] Matrix (Fin 2) (Fin 2) F) := by p2m_exact_reverting @_root_.P2MW.S_QuaternionAlgebra_nonempty_algEquiv_matrix_of_ne_zero_of_not_isUnit.solution
