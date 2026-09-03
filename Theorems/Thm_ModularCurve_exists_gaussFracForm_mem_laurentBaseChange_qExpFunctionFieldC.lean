import Definitions.Def_ModularCurve_X1
import P2M.Util
import P2M.Sol.S_ModularCurve_exists_gaussFracForm_mem_laurentBaseChange_qExpFunctionFieldC
attribute [-instance] instDecEqAlgebraicClosureRat WeierstrassCurve.Affine.Point.instDistribMulActionAlgEquiv WeierstrassCurve.Affine.Point.instModuleZModTorsionBy WeierstrassCurve.Affine.Point.instSMulTorsionBy WeierstrassCurve.Affine.Point.instDistribMulActionTorsionBy WeierstrassCurve.Affine.Point.instSMulAlgEquiv
attribute [-simp] FreyPackage.mk.sizeOf_spec FreyPackage.mk.injEq

set_option autoImplicit false

p2m_open "ModularCurve~exists_mem_qExpFunctionFieldC_single_mul_intSeriesC_mul_eq_of_mem_intFormRatiosC"
open scoped MatrixGroups

theorem ModularCurve.exists_gaussFracForm_mem_laurentBaseChange_qExpFunctionFieldC
    (L : Type*) [Field L] [Algebra ℚ L] (A : ValuationSubring L)
    (Γ : Subgroup SL(2, ℤ)) (hT : ModularGroup.T ∈ Γ)
    (f : ↥(laurentBaseChange L (qExpFunctionFieldC ℚ Γ))) (hf : f ≠ 0) :
    ∃ (c : L) (x y : LaurentSeries ↥A), c ≠ 0 ∧
      coeffMap (IsLocalRing.residue ↥A) x ≠ 0 ∧ coeffMap (IsLocalRing.residue ↥A) y ≠ 0 ∧
      coeffMap A.subtype x ∈ laurentBaseChange L (qExpFunctionFieldC ℚ Γ) ∧
      coeffMap A.subtype y ∈ laurentBaseChange L (qExpFunctionFieldC ℚ Γ) ∧
      (f : LaurentSeries L) * coeffMap A.subtype y = algebraMap L (LaurentSeries L) c * coeffMap A.subtype x := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_exists_gaussFracForm_mem_laurentBaseChange_qExpFunctionFieldC.solution
