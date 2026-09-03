import Mathlib.Algebra.Module.Torsion.Basic
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.LinearAlgebra.Eigenspace.Basic
import Mathlib.LinearAlgebra.TensorProduct.Tower
import Mathlib.RingTheory.Finiteness.Basic
import Mathlib.RingTheory.PrincipalIdealDomain
import P2M.Util
import P2M.Sol.S_Module_finrank_torsionBySet_ker_eq_finrank_quotient_mul_finrank_iInf_eigenspace_baseChange

set_option autoImplicit false

open scoped TensorProduct

theorem Module.finrank_torsionBySet_ker_eq_finrank_quotient_mul_finrank_iInf_eigenspace_baseChange
    {𝒪 : Type*} [CommRing 𝒪] [IsDomain 𝒪] [IsPrincipalIdealRing 𝒪]
    {T : Type*} [CommRing T] [Algebra 𝒪 T] [Module.Finite 𝒪 T]
    {M : Type*} [AddCommGroup M] [Module T M] [Module 𝒪 M] [IsScalarTower 𝒪 T M]
    [Module.Finite 𝒪 M] [Module.IsTorsionFree 𝒪 M]
    {A : Type*} [CommRing A] [IsDomain A] [Algebra 𝒪 A] [Module.Finite 𝒪 A]
    [Module.IsTorsionFree 𝒪 A]
    (χ : T →ₐ[𝒪] A) :
    Module.finrank 𝒪 ↥(Submodule.torsionBySet T M ↑(RingHom.ker χ)) =
      Module.finrank 𝒪 (T ⧸ RingHom.ker χ) *
        Module.finrank A ↥(⨅ t : T, Module.End.eigenspace
          (((LinearMap.lsmul T M t).restrictScalars 𝒪).baseChange A) (χ t)) := by p2m_exact_reverting @_root_.P2MW.S_Module_finrank_torsionBySet_ker_eq_finrank_quotient_mul_finrank_iInf_eigenspace_baseChange.solution
