import Mathlib
import Definitions.Def_QuaternionAlgebra_EichlerOrder
import P2M.Util
import P2M.Sol.S_QuaternionAlgebra_forall_tensorProduct_adicCompletion_isUnit_iff_of_algEquiv

set_option autoImplicit false

open scoped Quaternion TensorProduct
open IsDedekindDomain NumberField

theorem QuaternionAlgebra.forall_tensorProduct_adicCompletion_isUnit_iff_of_algEquiv
    {a b a' b' : ℚ} (e : ℍ[ℚ, a, b] ≃ₐ[ℚ] ℍ[ℚ, a', b']) (v : HeightOneSpectrum (𝓞 ℚ)) :
    (∀ x : ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ, x ≠ 0 → IsUnit x) ↔
      (∀ x : ℍ[ℚ, a', b'] ⊗[ℚ] v.adicCompletion ℚ, x ≠ 0 → IsUnit x) := by p2m_exact_reverting @_root_.P2MW.S_QuaternionAlgebra_forall_tensorProduct_adicCompletion_isUnit_iff_of_algEquiv.solution
