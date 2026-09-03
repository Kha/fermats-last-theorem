import Mathlib
import Definitions.Def_QuaternionAlgebra_EichlerOrder
import P2M.Util
import P2M.Sol.S_QuaternionAlgebra_forall_tensorProduct_adicCompletion_isUnit_iff_forall_normForm_eq_zero

set_option autoImplicit false

open scoped TensorProduct Quaternion
open IsDedekindDomain NumberField

theorem QuaternionAlgebra.forall_tensorProduct_adicCompletion_isUnit_iff_forall_normForm_eq_zero
    (a b : ℚ) (v : HeightOneSpectrum (𝓞 ℚ)) :
    (∀ x : ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ, x ≠ 0 → IsUnit x) ↔
      ∀ x₀ x₁ x₂ x₃ : v.adicCompletion ℚ,
        x₀ ^ 2 - (a : v.adicCompletion ℚ) * x₁ ^ 2 - (b : v.adicCompletion ℚ) * x₂ ^ 2 +
            (a : v.adicCompletion ℚ) * (b : v.adicCompletion ℚ) * x₃ ^ 2 = 0 →
          x₀ = 0 ∧ x₁ = 0 ∧ x₂ = 0 ∧ x₃ = 0 := by p2m_exact_reverting @_root_.P2MW.S_QuaternionAlgebra_forall_tensorProduct_adicCompletion_isUnit_iff_forall_normForm_eq_zero.solution
