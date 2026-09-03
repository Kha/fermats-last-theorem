import Mathlib
import Definitions.Def_QuaternionAlgebra_EichlerOrder
import P2M.Util
import P2M.Sol.S_QuaternionAlgebra_exists_algHom_matrix_injective_forall_apply_mem_of_isOrder_of_isMaximalOrder
attribute [-simp] QuaternionAlgebra.nrd_coe QuaternionAlgebra.nrd_one QuaternionAlgebra.trd_mk QuaternionAlgebra.nrd_mk QuaternionAlgebra.nrd_neg QuaternionAlgebra.nrd_zero QuaternionAlgebra.nrd_star QuaternionAlgebra.baseChangeRight_tmul QuaternionAlgebra.mapOfAlgebraMapEq_apply QuaternionAlgebra.baseChange_tmul LocalGL2.swapUnit_val

set_option autoImplicit false

open scoped Quaternion TensorProduct
open IsDedekindDomain NumberField

theorem QuaternionAlgebra.exists_algHom_matrix_injective_forall_apply_mem_of_isOrder_of_isMaximalOrder
    {a b c d : ℚ} (q : ℕ) [Fact q.Prime]
    (hH : QuaternionAlgebra.IsDefiniteRamifiedExactlyAt c d q)
    (hBq : ∀ v : HeightOneSpectrum (𝓞 ℚ), (q : 𝓞 ℚ) ∈ v.asIdeal →
      ∀ x : ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ, x ≠ 0 → IsUnit x)
    (Λ : Submodule ℤ ℍ[ℚ, a, b]) (hΛ : QuaternionAlgebra.IsOrder Λ)
    (O : Submodule ℤ ℍ[ℚ, c, d]) (hO : QuaternionAlgebra.IsMaximalOrder O) :
    ∃ j : ℍ[ℚ, a, b] →ₐ[ℚ] Matrix (Fin 2) (Fin 2) ℍ[ℚ, c, d], Function.Injective j ∧
      ∀ m ∈ Λ, ∀ i l : Fin 2, j m i l ∈ O := by p2m_exact_reverting @_root_.P2MW.S_QuaternionAlgebra_exists_algHom_matrix_injective_forall_apply_mem_of_isOrder_of_isMaximalOrder.solution
