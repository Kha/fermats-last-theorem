import Mathlib
import Definitions.Def_CerednikDrinfeld_FormalUpperHalfPlaneFrame
import P2M.Util
import P2M.Sol.S_CerednikDrinfeld_FormalOmega_AdicPoint_inEdgeChart_iff_toOmega_mem

set_option autoImplicit false

open scoped TensorProduct MatrixGroups
open LT.LatticeTree CerednikDrinfeld CerednikDrinfeld.FormalOmega CerednikDrinfeld.Omega

theorem CerednikDrinfeld.FormalOmega.AdicPoint.inEdgeChart_iff_toOmega_mem
    {𝒪 : Type} [CommRing 𝒪] [IsDomain 𝒪] [IsDiscreteValuationRing 𝒪]
    {K : Type} [Field K] [Algebra 𝒪 K] [IsFractionRing 𝒪 K] {π : 𝒪}
    {C : Type} [Field C] [Algebra K C] [DecidableEq C] {Γ₀ : Type} [LinearOrderedCommGroupWithZero Γ₀] [Valued C Γ₀]
    {R : Type} [CommRing R] [Algebra 𝒪 R] [Algebra R C] [Algebra 𝒪 C] [IsScalarTower 𝒪 R C] [IsScalarTower 𝒪 K C]
    (ϖ : PseudoUniformizer K C) (hF : IsAdicFrame π ϖ R) (g : GL (Fin 2) K) (x : AdicPoint K π R) :
    (x.pt 0).InEdgeChart π (FullLattice.act (g * edgeFlip K ϖ) (stdFullLattice K)) (FullLattice.act g (stdFullLattice K)) ↔
      x.toOmega C ∈ Omega.vertexTube ϖ (Matrix.ProjGenLinGroup.mk g) ∪ Omega.edgeTube ϖ (Matrix.ProjGenLinGroup.mk g) ∪
        Omega.vertexTube ϖ (Matrix.ProjGenLinGroup.mk (g * edgeFlip K ϖ)) := by p2m_exact_reverting @_root_.P2MW.S_CerednikDrinfeld_FormalOmega_AdicPoint_inEdgeChart_iff_toOmega_mem.solution
