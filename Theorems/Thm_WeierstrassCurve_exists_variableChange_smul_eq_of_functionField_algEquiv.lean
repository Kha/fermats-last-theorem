import Mathlib
import Definitions.Def_EllipticCurve_ValuationInfty
import P2M.Util
import P2M.Sol.S_WeierstrassCurve_exists_variableChange_smul_eq_of_functionField_algEquiv
attribute [-instance] WeierstrassCurve.Affine.instIsScalarTowerPolynomialRatFuncFunctionField_definitions WeierstrassCurve.Affine.instAlgebraRatFuncFunctionField_definitions WeierstrassCurve.Affine.instIsScalarTowerRatFuncFunctionField_definitions
attribute [-simp] WeierstrassCurve.Affine.ratFuncToFunctionField_algebraMap WeierstrassCurve.Affine.vcY_vcYInv WeierstrassCurve.Affine.vcXInv_vcX WeierstrassCurve.Affine.Point.vcFun_zero WeierstrassCurve.Affine.vcX_vcXInv WeierstrassCurve.Affine.vcYInv_vcY WeierstrassCurve.Affine.Point.vcInvFun_zero

set_option autoImplicit false
theorem WeierstrassCurve.exists_variableChange_smul_eq_of_functionField_algEquiv
    {F : Type*} [Field F] {W₁ W₂ : WeierstrassCurve F}
    [IsDedekindDomain W₁.toAffine.CoordinateRing]
    (e : W₂.toAffine.FunctionField ≃ₐ[F] W₁.toAffine.FunctionField)
    (hinf : ¬ WeierstrassCurve.Affine.valuationInfty W₁.toAffine
      (e (algebraMap W₂.toAffine.CoordinateRing W₂.toAffine.FunctionField
        (WeierstrassCurve.Affine.CoordinateRing.mk W₂.toAffine (Polynomial.C Polynomial.X)))) ≤ 1) :
    ∃ C : WeierstrassCurve.VariableChange F, C • W₂ = W₁ ∧
      e (algebraMap W₂.toAffine.CoordinateRing W₂.toAffine.FunctionField
          (WeierstrassCurve.Affine.CoordinateRing.mk W₂.toAffine (Polynomial.C Polynomial.X)))
        = algebraMap F W₁.toAffine.FunctionField ((C.u : F) ^ 2)
            * algebraMap W₁.toAffine.CoordinateRing W₁.toAffine.FunctionField
                (WeierstrassCurve.Affine.CoordinateRing.mk W₁.toAffine (Polynomial.C Polynomial.X))
          + algebraMap F W₁.toAffine.FunctionField C.r ∧
      e (algebraMap W₂.toAffine.CoordinateRing W₂.toAffine.FunctionField
          (WeierstrassCurve.Affine.CoordinateRing.mk W₂.toAffine Polynomial.X))
        = algebraMap F W₁.toAffine.FunctionField ((C.u : F) ^ 3)
            * algebraMap W₁.toAffine.CoordinateRing W₁.toAffine.FunctionField
                (WeierstrassCurve.Affine.CoordinateRing.mk W₁.toAffine Polynomial.X)
          + algebraMap F W₁.toAffine.FunctionField ((C.u : F) ^ 2 * C.s)
            * algebraMap W₁.toAffine.CoordinateRing W₁.toAffine.FunctionField
                (WeierstrassCurve.Affine.CoordinateRing.mk W₁.toAffine (Polynomial.C Polynomial.X))
          + algebraMap F W₁.toAffine.FunctionField C.t := by p2m_exact_reverting @_root_.P2MW.S_WeierstrassCurve_exists_variableChange_smul_eq_of_functionField_algEquiv.solution
