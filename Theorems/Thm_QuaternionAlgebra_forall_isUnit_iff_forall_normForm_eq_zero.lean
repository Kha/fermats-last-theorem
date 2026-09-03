import Mathlib
import Definitions.Def_QuaternionAlgebra_EichlerOrder
import P2M.Util
import P2M.Sol.S_QuaternionAlgebra_forall_isUnit_iff_forall_normForm_eq_zero

set_option autoImplicit false

open scoped TensorProduct Quaternion
open IsDedekindDomain NumberField

theorem QuaternionAlgebra.forall_isUnit_iff_forall_normForm_eq_zero
    (K : Type) [Field K] (a b : K) :
    (∀ x : ℍ[K, a, b], x ≠ 0 → IsUnit x) ↔
      ∀ x₀ x₁ x₂ x₃ : K, x₀ ^ 2 - a * x₁ ^ 2 - b * x₂ ^ 2 + a * b * x₃ ^ 2 = 0 →
        x₀ = 0 ∧ x₁ = 0 ∧ x₂ = 0 ∧ x₃ = 0 := by p2m_exact_reverting @_root_.P2MW.S_QuaternionAlgebra_forall_isUnit_iff_forall_normForm_eq_zero.solution
