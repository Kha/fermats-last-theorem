import Definitions.Def_ModularForm_HeckeOperatorForms
import P2M.Util
import P2M.Sol.S_CuspForm_exists_heckeULin_mul_aeval_eq_zero_isIntegral_of_sq_dvd_of_not_cube_dvd
attribute [-instance] instDecEqAlgebraicClosureRat WeierstrassCurve.Affine.Point.instDistribMulActionAlgEquiv WeierstrassCurve.Affine.Point.instModuleZModTorsionBy WeierstrassCurve.Affine.Point.instSMulTorsionBy WeierstrassCurve.Affine.Point.instDistribMulActionTorsionBy WeierstrassCurve.Affine.Point.instSMulAlgEquiv FLT.HyperbolicMeasure.instSMulInvariantMeasureSpecialLinearGroupFinOfNatNatIntUpperHalfPlaneVolume_definitions FLT.HyperbolicMeasure.instIsOpenPosMeasureUpperHalfPlaneVolume_definitions FLT.Gamma0FundamentalSet.instContinuousConstSMulSpecialLinearGroupFinOfNatNatIntUpperHalfPlane_definitions FLT.L2ProductionInstance.isFiniteMeasure_gamma0 FLT.L2ProductionInstance.countable_SL2Z FLT.L2ProductionInstance.countable_quotient FLT.L2ProductionInstance.nontrivial_gamma0L2 CuspForm.heckeAlgebra.instCommRing CuspForm.heckeAlgebra.instIsMulCommutative CuspForm.heckeAlgebra.instIsAddTorsionFree
attribute [-simp] FreyPackage.ModMCarrier.coe_rescaleLin_apply ModularForm.AtkinLehnerDatum.mk.injEq ModularForm.AtkinLehnerDatum.alGL_coe ModularForm.AtkinLehnerDatum.mk.sizeOf_spec ModularForm.AtkinLehnerDatum.sqUnitSL_coe ModularForm.AtkinLehnerDatum.det_sqUnit ModularForm.AtkinLehnerDatum.det_mat FreyPackage.mk.sizeOf_spec FreyPackage.mk.injEq FLT.TruncatedDomainPartition.unipotentDiagonalSum_zero CuspForm.coe_traceLin_apply ModularForm.coe_atkinLehnerLin_apply CuspForm.coe_atkinLehnerLin_apply CuspForm.coe_heckeULowerLin_apply CuspForm.heckeAlgebra.coe_U CuspForm.heckeAlgebra.coe_T PowerSeries.coeff_heckeV PowerSeries.coeff_heckeU

set_option autoImplicit false

theorem CuspForm.exists_heckeULin_mul_aeval_eq_zero_isIntegral_of_sq_dvd_of_not_cube_dvd
    (N : ℕ) [NeZero N] (q : ℕ) (hq : q.Prime) (hqN : q ∣ N) (hsq : q ^ 2 ∣ N) (hcube : ¬ q ^ 3 ∣ N) :
    ∃ Q : Polynomial ℂ,
      (∀ μ : ℂ, Q.IsRoot μ → IsIntegral ℤ μ ∧ ∃ ν : ℂ, IsIntegral ℤ ν ∧ μ * ν = q) ∧
      CuspForm.heckeULin 2 hqN * Polynomial.aeval (CuspForm.heckeULin (N := N) 2 hqN) Q = 0 := by p2m_exact_reverting @_root_.P2MW.S_CuspForm_exists_heckeULin_mul_aeval_eq_zero_isIntegral_of_sq_dvd_of_not_cube_dvd.solution
