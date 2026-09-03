import Mathlib
import Definitions.Def_QuaternionAlgebra_EichlerOrder
import P2M.Util
import P2M.Sol.S_QuaternionAlgebra_IsMaximalOrder_exists_matrix_forall_mulVec_mem_iff_of_le
attribute [-simp] QuaternionAlgebra.nrd_coe QuaternionAlgebra.nrd_one QuaternionAlgebra.trd_mk QuaternionAlgebra.nrd_mk QuaternionAlgebra.nrd_neg QuaternionAlgebra.nrd_zero QuaternionAlgebra.nrd_star QuaternionAlgebra.baseChangeRight_tmul QuaternionAlgebra.mapOfAlgebraMapEq_apply QuaternionAlgebra.baseChange_tmul LocalGL2.swapUnit_val

set_option autoImplicit false

open scoped Quaternion
open QuaternionAlgebra

theorem QuaternionAlgebra.IsMaximalOrder.exists_matrix_forall_mulVec_mem_iff_of_le
    {c d : ℚ} (q : ℕ) [Fact q.Prime] (hH : IsDefiniteRamifiedExactlyAt c d q)
    (O : Submodule ℤ ℍ[ℚ, c, d]) (hO : IsMaximalOrder O)
    (I₁ I₂ : Submodule ℤ ℍ[ℚ, c, d])
    (h₁O : I₁ ≤ O) (h₁mul : ∀ z ∈ I₁, ∀ o ∈ O, z * o ∈ I₁) (h₁full : ∃ n : ℤ, n ≠ 0 ∧ ∀ o ∈ O, n • o ∈ I₁)
    (h₂O : I₂ ≤ O) (h₂mul : ∀ z ∈ I₂, ∀ o ∈ O, z * o ∈ I₂) (h₂full : ∃ n : ℤ, n ≠ 0 ∧ ∀ o ∈ O, n • o ∈ I₂) :
    ∃ γ γ' : Matrix (Fin 2) (Fin 2) ℍ[ℚ, c, d], γ * γ' = 1 ∧ γ' * γ = 1 ∧
      ∀ x : Fin 2 → ℍ[ℚ, c, d],
        (∀ i, (γ'.mulVec x) i ∈ O) ↔ (x 0 ∈ I₁ ∧ x 1 ∈ I₂) := by p2m_exact_reverting @_root_.P2MW.S_QuaternionAlgebra_IsMaximalOrder_exists_matrix_forall_mulVec_mem_iff_of_le.solution
