import Mathlib
import Definitions.Def_CerednikDrinfeld_FormalUpperHalfPlaneFrame
import P2M.Util
import P2M.Sol.S_CerednikDrinfeld_FormalOmega_AdicPoint_exists_toOmega_eq_of_mem_affinoid_zero_or_lt

set_option autoImplicit false

open scoped TensorProduct MatrixGroups
open LT.LatticeTree CerednikDrinfeld CerednikDrinfeld.FormalOmega CerednikDrinfeld.Omega

theorem CerednikDrinfeld.FormalOmega.AdicPoint.exists_toOmega_eq_of_mem_affinoid_zero_or_lt
    {𝒪 : Type} [CommRing 𝒪] [IsDomain 𝒪] [IsDiscreteValuationRing 𝒪]
    {K : Type} [Field K] [Algebra 𝒪 K] [IsFractionRing 𝒪 K] {π : 𝒪}
    {C : Type} [Field C] [Algebra K C] [DecidableEq C] {Γ₀ : Type} [LinearOrderedCommGroupWithZero Γ₀] [Valued C Γ₀]
    {R : Type} [CommRing R] [Algebra 𝒪 R] [Algebra R C] [Algebra 𝒪 C] [IsScalarTower 𝒪 R C] [IsScalarTower 𝒪 K C]
    (ϖ : PseudoUniformizer K C) (hF : IsAdicFrame π ϖ R) (w : C)
    (hw : w ∈ affinoid ϖ 0 ∨ (Valued.v (algebraMap K C ϖ.ϖ) < Valued.v w ∧ Valued.v w < 1)) :
    ∃ x : AdicPoint K π R, x.toOmega C = w := by p2m_exact_reverting @_root_.P2MW.S_CerednikDrinfeld_FormalOmega_AdicPoint_exists_toOmega_eq_of_mem_affinoid_zero_or_lt.solution
