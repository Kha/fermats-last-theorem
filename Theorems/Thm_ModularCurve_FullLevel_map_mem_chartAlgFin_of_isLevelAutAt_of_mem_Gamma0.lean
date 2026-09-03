import Mathlib
import Definitions.Def_AlgebraicCurve_TwoChartIntegralModel
import Definitions.Def_ModularCurve_X1
import Definitions.Def_ModularCurve_FullLevelJacobian
import Definitions.Def_ModularCurve_FullLevelLevelAutAt
import P2M.Util
import P2M.Sol.S_ModularCurve_FullLevel_map_mem_chartAlgFin_of_isLevelAutAt_of_mem_Gamma0
attribute [-instance] ModularCurve.PhiGen.instNeZeroPhiGenCosetA
attribute [-simp] ModularCurve.jqNModC_one ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL

set_option autoImplicit false

open scoped MatrixGroups

theorem ModularCurve.FullLevel.map_mem_chartAlgFin_of_isLevelAutAt_of_mem_Gamma0
    (m : ℕ) [NeZero m] (M' : ℕ) [NeZero M'] (hmM' : Nat.Coprime m M')
    (L : Type) [Field L] [CharZero L] (n : ℕ) (ξ : L)
    (hι : ∃ ι : L →+* ℂ, ι ξ = Complex.exp (2 * Real.pi * Complex.I / n))
    (K : IntermediateField L (LaurentSeries L))
    (A : Type) [CommRing A] [Algebra A L] [Algebra A ↥K] [IsScalarTower A L ↥K]
    (j : ↥K) (hj : ((j : LaurentSeries L)) = ModularCurve.coeffEmb L ModularCurve.jq) [Fact (j ≠ 0)]
    (γ : SL(2, ℤ)) (hγ : γ ∈ CongruenceSubgroup.Gamma0 M')
    (τ : ↥K ≃ₐ[L] ↥K)
    (hτ : ModularCurve.FullLevel.IsLevelAutAt L n ξ m (m ^ 2 * M') (ModularCurve.FullLevel.levelH m M') γ K τ)
    (a : ↥K) (ha : a ∈ AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j) :
    τ a ∈ AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_FullLevel_map_mem_chartAlgFin_of_isLevelAutAt_of_mem_Gamma0.solution
