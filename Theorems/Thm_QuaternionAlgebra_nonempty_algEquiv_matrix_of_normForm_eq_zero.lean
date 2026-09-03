import Mathlib
import Definitions.Def_QuaternionAlgebra_EichlerOrder
import Definitions.Def_Submodule_FiniteAdeleBox
import Definitions.Def_Submodule_LocalBox
import P2M.Util
import P2M.Sol.S_QuaternionAlgebra_nonempty_algEquiv_matrix_of_normForm_eq_zero

set_option autoImplicit false

open scoped TensorProduct Quaternion Pointwise
open IsDedekindDomain NumberField

theorem QuaternionAlgebra.nonempty_algEquiv_matrix_of_normForm_eq_zero
    (K : Type) [Field K] (h2 : (2 : K) ≠ 0) (a b : K) (ha : a ≠ 0) (hb : b ≠ 0)
    (x₀ x₁ x₂ x₃ : K) (hx : ¬ (x₀ = 0 ∧ x₁ = 0 ∧ x₂ = 0 ∧ x₃ = 0))
    (h0 : x₀ ^ 2 - a * x₁ ^ 2 - b * x₂ ^ 2 + a * b * x₃ ^ 2 = 0) :
    Nonempty (ℍ[K, a, b] ≃ₐ[K] Matrix (Fin 2) (Fin 2) K) := by p2m_exact_reverting @_root_.P2MW.S_QuaternionAlgebra_nonempty_algEquiv_matrix_of_normForm_eq_zero.solution
