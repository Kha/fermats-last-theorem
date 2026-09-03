import Mathlib
import Definitions.Def_ModularCurve_X1
import Definitions.Def_ModularCurve_JqCoeff
import P2M.Util
import P2M.Sol.S_ModularCurve_isSeparable_adjoin_qExpFunctionFieldC_gamma1
attribute [-instance] instDecEqAlgebraicClosureRat WeierstrassCurve.Affine.Point.instDistribMulActionAlgEquiv WeierstrassCurve.Affine.Point.instModuleZModTorsionBy WeierstrassCurve.Affine.Point.instSMulTorsionBy WeierstrassCurve.Affine.Point.instDistribMulActionTorsionBy WeierstrassCurve.Affine.Point.instSMulAlgEquiv WeierstrassCurve.Affine.Point.instSMulCommClassAlgEquivZModTorsionBy
attribute [-simp] ModularCurve.qExpandAlgHomC_apply FreyPackage.mk.sizeOf_spec FreyPackage.mk.injEq WeierstrassCurve.reducePoint_zero WeierstrassCurve.Affine.Point.galoisRep_apply WeierstrassCurve.Affine.Point.galoisRepModuleEnd_apply

open ModularCurve

universe u in
set_option synthInstance.maxHeartbeats 400000 in

theorem ModularCurve.isSeparable_adjoin_qExpFunctionFieldC_gamma1
    (K : Type u) [Field K] [IsAlgClosed K] (M : ℕ) [NeZero M]
    (x : qExpFunctionFieldC K (CongruenceSubgroup.Gamma1 M))
    (hx : (x : LaurentSeries K) = jqModC K) :
    Algebra.IsSeparable
      (IntermediateField.adjoin K ({x} : Set (qExpFunctionFieldC K (CongruenceSubgroup.Gamma1 M))))
      (qExpFunctionFieldC K (CongruenceSubgroup.Gamma1 M)) := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_isSeparable_adjoin_qExpFunctionFieldC_gamma1.solution
