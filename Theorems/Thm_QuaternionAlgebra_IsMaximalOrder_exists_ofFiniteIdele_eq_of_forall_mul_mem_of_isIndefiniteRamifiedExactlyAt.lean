import Mathlib
import Definitions.Def_QuaternionAlgebra_EichlerOrder
import Definitions.Def_Submodule_FiniteAdeleBox
import Definitions.Def_CerednikDrinfeld_ShimuraCurve
import P2M.Util
import P2M.Sol.S_QuaternionAlgebra_IsMaximalOrder_exists_ofFiniteIdele_eq_of_forall_mul_mem_of_isIndefiniteRamifiedExactlyAt
attribute [-simp] QuaternionAlgebra.baseChangeRight_tmul QuaternionAlgebra.mapOfAlgebraMapEq_apply QuaternionAlgebra.baseChange_tmul

set_option autoImplicit false

open scoped TensorProduct Quaternion
open IsDedekindDomain NumberField QuaternionAlgebra

theorem QuaternionAlgebra.IsMaximalOrder.exists_ofFiniteIdele_eq_of_forall_mul_mem_of_isIndefiniteRamifiedExactlyAt
    {a b : ℚ} {q q' : ℕ} [Fact q.Prime] [Fact q'.Prime] (hB : IsIndefiniteRamifiedExactlyAt a b q q')
    {Λ : Submodule ℤ ℍ[ℚ, a, b]} (hΛ : IsMaximalOrder Λ)
    (I : Submodule ℤ ℍ[ℚ, a, b]) (hIΛ : I ≤ Λ)
    (hmul : ∀ z ∈ I, ∀ μ ∈ Λ, z * μ ∈ I)
    (hfull : ∃ n : ℤ, n ≠ 0 ∧ ∀ μ ∈ Λ, n • μ ∈ I) :
    ∃ x : (ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ,
      Submodule.ofFiniteIdele Λ x = I := by p2m_exact_reverting @_root_.P2MW.S_QuaternionAlgebra_IsMaximalOrder_exists_ofFiniteIdele_eq_of_forall_mul_mem_of_isIndefiniteRamifiedExactlyAt.solution
