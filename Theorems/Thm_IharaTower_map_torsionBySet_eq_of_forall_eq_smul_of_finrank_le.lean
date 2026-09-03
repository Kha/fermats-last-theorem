import Mathlib.Algebra.Module.Torsion.Basic
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.LinearAlgebra.FreeModule.Basic
import Mathlib.RingTheory.DiscreteValuationRing.Basic
import P2M.Util
import P2M.Sol.S_IharaTower_map_torsionBySet_eq_of_forall_eq_smul_of_finrank_le

set_option autoImplicit false

theorem IharaTower.map_torsionBySet_eq_of_forall_eq_smul_of_finrank_le
    {𝒪 : Type} [CommRing 𝒪] [IsDomain 𝒪] [IsDiscreteValuationRing 𝒪]
    {T : Type} [CommRing T] [Algebra 𝒪 T] {T' : Type} [CommRing T'] [Algebra 𝒪 T']
    {M : Type} [AddCommGroup M] [Module T M] [Module 𝒪 M] [IsScalarTower 𝒪 T M]
    [Module.Finite 𝒪 M] [Module.Free 𝒪 M]
    {M' : Type} [AddCommGroup M'] [Module T' M'] [Module 𝒪 M'] [IsScalarTower 𝒪 T' M']
    [Module.Finite 𝒪 M'] [Module.Free 𝒪 M']
    (i : M →ₗ[𝒪] M') (πT : T →ₐ[𝒪] 𝒪) (πT' : T' →ₐ[𝒪] 𝒪)
    {ϖ : 𝒪} (hϖ : Irreducible ϖ)
    (hres : ∀ (v : M) (x : M'), i v = ϖ • x → ∃ v₁ : M, v = ϖ • v₁)
    (hincl : Submodule.map i ((Submodule.torsionBySet T M ↑(RingHom.ker πT)).restrictScalars 𝒪) ≤
      (Submodule.torsionBySet T' M' ↑(RingHom.ker πT')).restrictScalars 𝒪)
    (hrank : Module.finrank 𝒪
        ((Submodule.torsionBySet T' M' ↑(RingHom.ker πT')).restrictScalars 𝒪) ≤
      Module.finrank 𝒪 ((Submodule.torsionBySet T M ↑(RingHom.ker πT)).restrictScalars 𝒪)) :
    Function.Injective i ∧
    Submodule.map i ((Submodule.torsionBySet T M ↑(RingHom.ker πT)).restrictScalars 𝒪) =
      (Submodule.torsionBySet T' M' ↑(RingHom.ker πT')).restrictScalars 𝒪 := by p2m_exact_reverting @_root_.P2MW.S_IharaTower_map_torsionBySet_eq_of_forall_eq_smul_of_finrank_le.solution
