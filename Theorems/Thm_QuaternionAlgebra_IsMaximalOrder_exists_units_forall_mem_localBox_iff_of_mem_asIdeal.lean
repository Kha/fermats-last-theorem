import Mathlib
import Definitions.Def_QuaternionAlgebra_EichlerOrder
import P2M.Util
import P2M.Sol.S_QuaternionAlgebra_IsMaximalOrder_exists_units_forall_mem_localBox_iff_of_mem_asIdeal
attribute [-simp] QuaternionAlgebra.nrd_coe QuaternionAlgebra.nrd_one QuaternionAlgebra.trd_mk QuaternionAlgebra.nrd_mk QuaternionAlgebra.nrd_neg QuaternionAlgebra.nrd_zero QuaternionAlgebra.nrd_star QuaternionAlgebra.baseChangeRight_tmul QuaternionAlgebra.mapOfAlgebraMapEq_apply QuaternionAlgebra.baseChange_tmul

set_option autoImplicit false
open scoped Quaternion TensorProduct NumberField Pointwise
p2m_open "QuaternionAlgebra~nrd IsDedekindDomain"

theorem QuaternionAlgebra.IsMaximalOrder.exists_units_forall_mem_localBox_iff_of_mem_asIdeal
    {a b : ℚ} (p : ℕ) [Fact p.Prime] (hdef : IsDefiniteRamifiedExactlyAt a b p)
    {Λ : Submodule ℤ ℍ[ℚ, a, b]} (hΛ : IsMaximalOrder Λ)
    (I : Submodule ℤ ℍ[ℚ, a, b]) (hIΛ : I ≤ Λ)
    (hmul : ∀ z ∈ I, ∀ μ ∈ Λ, z * μ ∈ I)
    (hfull : ∃ n : ℤ, n ≠ 0 ∧ ∀ μ ∈ Λ, n • μ ∈ I)
    (v : HeightOneSpectrum (𝓞 ℚ)) (hpv : (p : 𝓞 ℚ) ∈ v.asIdeal) :
    ∃ X : (ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ)ˣ,
      ∀ t : ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ,
        t ∈ Submodule.localBox I v ↔
          ((X⁻¹ : (ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ)ˣ) : ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ) * t ∈
            Submodule.localBox Λ v := by p2m_exact_reverting @_root_.P2MW.S_QuaternionAlgebra_IsMaximalOrder_exists_units_forall_mem_localBox_iff_of_mem_asIdeal.solution
