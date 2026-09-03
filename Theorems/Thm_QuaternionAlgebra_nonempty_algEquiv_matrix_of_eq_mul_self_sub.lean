import Mathlib
import P2M.Util
import P2M.Sol.S_QuaternionAlgebra_nonempty_algEquiv_matrix_of_eq_mul_self_sub

theorem QuaternionAlgebra.nonempty_algEquiv_matrix_of_eq_mul_self_sub
    {F : Type*} [Field F] [NeZero (2 : F)] {a b : F} (ha : a ≠ 0) (hb : b ≠ 0)
    {u v : F} (huv : b = u * u - a * (v * v)) :
    Nonempty (QuaternionAlgebra F a 0 b ≃ₐ[F] Matrix (Fin 2) (Fin 2) F) := by p2m_exact_reverting @_root_.P2MW.S_QuaternionAlgebra_nonempty_algEquiv_matrix_of_eq_mul_self_sub.solution
