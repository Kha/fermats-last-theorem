import Mathlib
import Definitions.Def_QuaternionAlgebra_EichlerOrder
import P2M.Util
import P2M.Sol.S_QuaternionAlgebra_exists_algHom_matrix_injective_of_isDefiniteRamifiedExactlyAt_of_forall_isUnit

set_option autoImplicit false

open scoped Quaternion TensorProduct
open IsDedekindDomain NumberField

theorem QuaternionAlgebra.exists_algHom_matrix_injective_of_isDefiniteRamifiedExactlyAt_of_forall_isUnit
    {a b c d : ℚ} (q : ℕ) [Fact q.Prime]
    (hH : QuaternionAlgebra.IsDefiniteRamifiedExactlyAt c d q)
    (hBq : ∀ v : HeightOneSpectrum (𝓞 ℚ), (q : 𝓞 ℚ) ∈ v.asIdeal →
      ∀ x : ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ, x ≠ 0 → IsUnit x) :
    ∃ f : ℍ[ℚ, a, b] →ₐ[ℚ] Matrix (Fin 2) (Fin 2) ℍ[ℚ, c, d], Function.Injective f := by p2m_exact_reverting @_root_.P2MW.S_QuaternionAlgebra_exists_algHom_matrix_injective_of_isDefiniteRamifiedExactlyAt_of_forall_isUnit.solution
