import Mathlib
import Definitions.Def_WeierstrassCurve_GenusOnePlaceGateCentred
import Definitions.Def_AlgebraicCurve_Correspondence
import Definitions.Def_WeierstrassCurve_VariableChangePointEquiv
import P2M.Util
import P2M.Sol.S_WeierstrassCurve_Affine_exists_variableChange_forall_restrictAlong_placeOfPoint_eq_of_algEquiv
attribute [-instance] WeierstrassCurve.Affine.instIsDiscreteValuationRingSubtypeFunctionFieldMemValuationSubringValuationSubringWithZeroMultiplicativeIntValuationInfty WeierstrassCurve.Affine.valuationInfty_isNontrivial WeierstrassCurve.Affine.instIsScalarTowerPolynomialRatFuncFunctionField_definitions WeierstrassCurve.Affine.instAlgebraRatFuncFunctionField_definitions WeierstrassCurve.Affine.instIsScalarTowerRatFuncFunctionField_definitions WeierstrassCurve.Affine.CoordinateRing.moduleFinite WeierstrassCurve.Affine.instDecidableEqFunctionField WeierstrassCurve.Affine.CoordinateRing.isIntegral
attribute [-simp] WeierstrassCurve.Affine.ratFuncToFunctionField_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_C WeierstrassCurve.Affine.Point.yc_some WeierstrassCurve.Affine.Point.xc_some WeierstrassCurve.Affine.pointPull_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_X WeierstrassCurve.Affine.pointHom_mk_Y WeierstrassCurve.Affine.placeOf_asIdeal

open AlgebraicCurve WeierstrassCurve WeierstrassCurve.Affine

universe u
theorem WeierstrassCurve.Affine.exists_variableChange_forall_restrictAlong_placeOfPoint_eq_of_algEquiv
    {F : Type u} [Field F] [DecidableEq F] [IsAlgClosed F]
    {W₁ W₂ : WeierstrassCurve.Affine F} [W₁.IsElliptic] [W₂.IsElliptic]
    [GenusOnePlaceGate W₁] [GenusOnePlaceGate.IsCentred W₁]
    [GenusOnePlaceGate W₂] [GenusOnePlaceGate.IsCentred W₂]
    (e : W₂.FunctionField ≃ₐ[F] W₁.FunctionField) (he : e.toAlgHom.toRingHom.IsIntegral)
    (hinf : (placeOfPoint (0 : W₁.Point)).restrictAlong e.toAlgHom he = placeOfPoint (0 : W₂.Point)) :
    ∃ (C : WeierstrassCurve.VariableChange F) (hC : C • W₂ = W₁),
      ∀ P : W₁.Point, (placeOfPoint P).restrictAlong e.toAlgHom he
        = placeOfPoint (Point.equivOfVariableChangeEq hC P) := by p2m_exact_reverting @_root_.P2MW.S_WeierstrassCurve_Affine_exists_variableChange_forall_restrictAlong_placeOfPoint_eq_of_algEquiv.solution
