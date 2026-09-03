import Mathlib
import P2M.Util
import P2M.Sol.S_Submodule_mem_ideal_smul_top_of_smul_mem_of_free_of_noZeroSMulDivisors_quotient

set_option autoImplicit false

theorem Submodule.mem_ideal_smul_top_of_smul_mem_of_free_of_noZeroSMulDivisors_quotient
    {𝒪 : Type*} [CommRing 𝒪] {R : Type*} [CommRing R] [Algebra 𝒪 R]
    {M : Type*} [AddCommGroup M] [Module R M] [Module 𝒪 M] [IsScalarTower 𝒪 R M] [Module.Free R M]
    (I : Ideal R) [NoZeroSMulDivisors 𝒪 (R ⧸ I)]
    (a : 𝒪) (ha : a ≠ 0) (m : M) (h : a • m ∈ (I • ⊤ : Submodule R M)) :
    m ∈ (I • ⊤ : Submodule R M) := by p2m_exact_reverting @_root_.P2MW.S_Submodule_mem_ideal_smul_top_of_smul_mem_of_free_of_noZeroSMulDivisors_quotient.solution
