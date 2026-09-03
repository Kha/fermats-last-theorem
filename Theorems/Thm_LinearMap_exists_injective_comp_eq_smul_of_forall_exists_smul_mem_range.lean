import Mathlib
import P2M.Util
import P2M.Sol.S_LinearMap_exists_injective_comp_eq_smul_of_forall_exists_smul_mem_range

set_option autoImplicit false

theorem LinearMap.exists_injective_comp_eq_smul_of_forall_exists_smul_mem_range
    {𝒪 : Type} [CommRing 𝒪] [IsDomain 𝒪]
    {R : Type} [CommRing R] [Algebra 𝒪 R]
    {V : Type} [AddCommGroup V] [Module R V] [Module 𝒪 V] [IsScalarTower 𝒪 R V] [Module.Finite 𝒪 V]
    {Y : Type} [AddCommGroup Y] [Module R Y] [Module 𝒪 Y] [IsScalarTower 𝒪 R Y]
    {M : Type} [AddCommGroup M] [Module R M] [Module 𝒪 M] [IsScalarTower 𝒪 R M]
    (htf : ∀ (a : 𝒪) (m : M), a ≠ 0 → a • m = 0 → m = 0)
    (ι : Y →ₗ[R] M) (hι : Function.Injective ι)
    (hloc : ∀ m : M, ∃ a : 𝒪, a ≠ 0 ∧ a • m ∈ LinearMap.range ι)
    (J : V →ₗ[R] M) (hJ : Function.Injective J) :
    ∃ (a : 𝒪) (_ : a ≠ 0) (j : V →ₗ[R] Y), Function.Injective j ∧ ∀ v : V, ι (j v) = a • J v := by p2m_exact_reverting @_root_.P2MW.S_LinearMap_exists_injective_comp_eq_smul_of_forall_exists_smul_mem_range.solution
