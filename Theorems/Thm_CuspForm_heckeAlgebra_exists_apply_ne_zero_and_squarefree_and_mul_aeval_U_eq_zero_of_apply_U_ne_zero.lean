import Definitions.Def_CuspForm_HeckeAlgebra
import Definitions.Def_CuspForm_IntegralStructure
import Mathlib.Algebra.Squarefree.Basic
import P2M.Util
import P2M.Sol.S_CuspForm_heckeAlgebra_exists_apply_ne_zero_and_squarefree_and_mul_aeval_U_eq_zero_of_apply_U_ne_zero
attribute [-instance] instDecEqAlgebraicClosureRat WeierstrassCurve.Affine.Point.instDistribMulActionAlgEquiv WeierstrassCurve.Affine.Point.instModuleZModTorsionBy WeierstrassCurve.Affine.Point.instSMulTorsionBy WeierstrassCurve.Affine.Point.instDistribMulActionTorsionBy WeierstrassCurve.Affine.Point.instSMulAlgEquiv FLT.HyperbolicMeasure.instSMulInvariantMeasureSpecialLinearGroupFinOfNatNatIntUpperHalfPlaneVolume_definitions FLT.HyperbolicMeasure.instIsOpenPosMeasureUpperHalfPlaneVolume_definitions FLT.Gamma0FundamentalSet.instContinuousConstSMulSpecialLinearGroupFinOfNatNatIntUpperHalfPlane_definitions FLT.L2ProductionInstance.isFiniteMeasure_gamma0 FLT.L2ProductionInstance.countable_SL2Z FLT.L2ProductionInstance.countable_quotient FLT.L2ProductionInstance.nontrivial_gamma0L2
attribute [-simp] FreyPackage.mk.sizeOf_spec FreyPackage.mk.injEq FreyPackage.ModMCarrier.coe_rescaleLin_apply ModularForm.AtkinLehnerDatum.mk.injEq ModularForm.AtkinLehnerDatum.alGL_coe ModularForm.AtkinLehnerDatum.mk.sizeOf_spec ModularForm.AtkinLehnerDatum.sqUnitSL_coe ModularForm.AtkinLehnerDatum.det_sqUnit ModularForm.AtkinLehnerDatum.det_mat FLT.TruncatedDomainPartition.unipotentDiagonalSum_zero CuspForm.coe_traceLin_apply ModularForm.coe_atkinLehnerLin_apply CuspForm.coe_atkinLehnerLin_apply FreyPackage.ModMCarrier.coe_levelInclusionLin FreyPackage.ModMCarrier.atkinLehnerDatumOfPrimeNotDvd_R FreyPackage.ModMCarrier.latticeRed.mk_eq_tmul CuspForm.coe_heckeULowerLin_apply PowerSeries.coeff_heckeV PowerSeries.coeff_heckeU

set_option autoImplicit false

open Polynomial

theorem CuspForm.heckeAlgebra.exists_apply_ne_zero_and_squarefree_and_mul_aeval_U_eq_zero_of_apply_U_ne_zero
    (N : ℕ) [NeZero N] (S₀ : Set ℕ)
    {k : Type} [Field k] (θ' : CuspForm.heckeAlgebra N 2 S₀ →+* k)
    (p : ℕ) (hp : p.Prime) (hpk : (p : k) = 0) (hpN : p ∣ N) (hNp : ¬ p ^ 2 ∣ N) (hpS₀ : p ∉ S₀)
    (hUp : θ' (CuspForm.heckeAlgebra.U hp hpN hpS₀) ≠ 0) :
    ∃ (r : CuspForm.heckeAlgebra N 2 S₀) (P : ℤ[X]),
      θ' r ≠ 0 ∧ P.Monic ∧ Squarefree (P.map (Int.castRingHom ℚ)) ∧
      r * aeval (CuspForm.heckeAlgebra.U hp hpN hpS₀) P = 0 := by p2m_exact_reverting @_root_.P2MW.S_CuspForm_heckeAlgebra_exists_apply_ne_zero_and_squarefree_and_mul_aeval_U_eq_zero_of_apply_U_ne_zero.solution
