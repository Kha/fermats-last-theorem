import Mathlib.Algebra.Module.Torsion.Basic
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.RingTheory.Finiteness.Basic
import Mathlib.RingTheory.PrincipalIdealDomain
import P2M.Util
import P2M.Sol.S_Module_exists_injective_linearMap_pi_and_smul_mem_range_of_finrank_torsionBySet_eq_mul

set_option autoImplicit false

theorem Module.exists_injective_linearMap_pi_and_smul_mem_range_of_finrank_torsionBySet_eq_mul
    {𝒪 : Type*} [CommRing 𝒪] [IsDomain 𝒪] [IsPrincipalIdealRing 𝒪]
    {T : Type*} [CommRing T] [Algebra 𝒪 T] [Module.Finite 𝒪 T]
    {M : Type*} [AddCommGroup M] [Module T M] [Module 𝒪 M] [IsScalarTower 𝒪 T M]
    [Module.Finite 𝒪 M] [Module.IsTorsionFree 𝒪 M]
    {ι : Type*} [Fintype ι]
    {A : ι → Type*} [∀ i, CommRing (A i)] [∀ i, IsDomain (A i)] [∀ i, Algebra 𝒪 (A i)]
    [∀ i, Module.IsTorsionFree 𝒪 (A i)]
    (χ : ∀ i, T →ₐ[𝒪] A i) (hker : ⨅ i, RingHom.ker (χ i) = ⊥)
    (a : 𝒪) (ha : a ≠ 0) (hsurj : ∀ y : ∀ i, A i, ∃ x : T, ∀ i, χ i x = a • y i)
    (d : ℕ)
    (hrank : ∀ i, Module.finrank 𝒪 ↥(Submodule.torsionBySet T M ↑(RingHom.ker (χ i))) =
      d * Module.finrank 𝒪 (T ⧸ RingHom.ker (χ i))) :
    ∃ (f : (Fin d → T) →ₗ[T] M) (c : 𝒪), c ≠ 0 ∧ Function.Injective f ∧
      ∀ m : M, c • m ∈ LinearMap.range f := by p2m_exact_reverting @_root_.P2MW.S_Module_exists_injective_linearMap_pi_and_smul_mem_range_of_finrank_torsionBySet_eq_mul.solution
