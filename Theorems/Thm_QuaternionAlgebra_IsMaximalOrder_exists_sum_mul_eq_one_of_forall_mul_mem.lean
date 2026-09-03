import Mathlib
import Definitions.Def_QuaternionAlgebra_EichlerOrder
import P2M.Util
import P2M.Sol.S_QuaternionAlgebra_IsMaximalOrder_exists_sum_mul_eq_one_of_forall_mul_mem
attribute [-simp] QuaternionAlgebra.nrd_coe QuaternionAlgebra.nrd_one QuaternionAlgebra.trd_mk QuaternionAlgebra.nrd_mk QuaternionAlgebra.nrd_neg QuaternionAlgebra.nrd_zero QuaternionAlgebra.nrd_star QuaternionAlgebra.baseChangeRight_tmul QuaternionAlgebra.mapOfAlgebraMapEq_apply QuaternionAlgebra.baseChange_tmul LocalGL2.swapUnit_val

set_option autoImplicit false

open scoped Quaternion
open QuaternionAlgebra hiding nrd

theorem QuaternionAlgebra.IsMaximalOrder.exists_sum_mul_eq_one_of_forall_mul_mem
    {c d : ℚ} (q : ℕ) [Fact q.Prime] (hH : IsDefiniteRamifiedExactlyAt c d q)
    (O : Submodule ℤ ℍ[ℚ, c, d]) (hO : IsMaximalOrder O)
    (I : Submodule ℤ ℍ[ℚ, c, d]) (hIO : I ≤ O) (hmul : ∀ z ∈ I, ∀ o ∈ O, z * o ∈ I)
    (hfull : ∃ n : ℤ, n ≠ 0 ∧ ∀ o ∈ O, n • o ∈ I) :
    ∃ (t : Finset ℍ[ℚ, c, d]) (y : ℍ[ℚ, c, d] → ℍ[ℚ, c, d]),
      (∀ x ∈ t, x ∈ I) ∧ (∀ x ∈ t, ∀ z ∈ I, y x * z ∈ O) ∧ ∑ x ∈ t, x * y x = 1 := by p2m_exact_reverting @_root_.P2MW.S_QuaternionAlgebra_IsMaximalOrder_exists_sum_mul_eq_one_of_forall_mul_mem.solution
