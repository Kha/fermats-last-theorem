import Mathlib
import Definitions.Def_QuaternionAlgebra_EichlerOrder
import P2M.Util
import P2M.Sol.S_QuaternionAlgebra_IsMaximalOrder_exists_ofFiniteIdele_eq_of_forall_mul_mem
attribute [-simp] QuaternionAlgebra.baseChangeRight_tmul QuaternionAlgebra.mapOfAlgebraMapEq_apply QuaternionAlgebra.baseChange_tmul QuaternionAlgebra.nrd_coe QuaternionAlgebra.nrd_one QuaternionAlgebra.trd_mk QuaternionAlgebra.nrd_mk QuaternionAlgebra.nrd_neg QuaternionAlgebra.nrd_zero QuaternionAlgebra.nrd_star

set_option autoImplicit false
open scoped Quaternion TensorProduct NumberField Pointwise
open QuaternionAlgebra

theorem QuaternionAlgebra.IsMaximalOrder.exists_ofFiniteIdele_eq_of_forall_mul_mem
    {a b : ℚ} (p : ℕ) [Fact p.Prime] (hdef : IsDefiniteRamifiedExactlyAt a b p)
    {Λ : Submodule ℤ ℍ[ℚ, a, b]} (hΛ : IsMaximalOrder Λ)
    (I : Submodule ℤ ℍ[ℚ, a, b]) (hIΛ : I ≤ Λ)
    (hmul : ∀ z ∈ I, ∀ μ ∈ Λ, z * μ ∈ I)
    (hfull : ∃ n : ℤ, n ≠ 0 ∧ ∀ μ ∈ Λ, n • μ ∈ I) :
    ∃ x : (ℍ[ℚ, a, b] ⊗[ℚ] IsDedekindDomain.FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ,
      Submodule.ofFiniteIdele Λ x = I := by p2m_exact_reverting @_root_.P2MW.S_QuaternionAlgebra_IsMaximalOrder_exists_ofFiniteIdele_eq_of_forall_mul_mem.solution
