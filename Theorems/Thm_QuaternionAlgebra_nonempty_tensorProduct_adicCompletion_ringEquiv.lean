import Mathlib
import Definitions.Def_QuaternionAlgebra_EichlerOrder
import P2M.Util
import P2M.Sol.S_QuaternionAlgebra_nonempty_tensorProduct_adicCompletion_ringEquiv

set_option autoImplicit false

open scoped TensorProduct Quaternion
open IsDedekindDomain NumberField

theorem QuaternionAlgebra.nonempty_tensorProduct_adicCompletion_ringEquiv
    (a b : ℚ) (v : HeightOneSpectrum (𝓞 ℚ)) :
    Nonempty (ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ ≃+*
      ℍ[v.adicCompletion ℚ, (a : v.adicCompletion ℚ), (b : v.adicCompletion ℚ)]) := by p2m_exact_reverting @_root_.P2MW.S_QuaternionAlgebra_nonempty_tensorProduct_adicCompletion_ringEquiv.solution
