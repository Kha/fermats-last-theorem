import Mathlib
import Definitions.Def_ModularCurve_WeierstrassGamma0Pow
import P2M.Util
import P2M.Sol.S_ModularCurve_IsGamma0PowAt_isAddCyclic_closure_and_natCard_eq_pow
attribute [-instance] WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly instDecEqAlgebraicClosureRat WeierstrassCurve.Affine.Point.instDistribMulActionAlgEquiv WeierstrassCurve.Affine.Point.instModuleZModTorsionBy WeierstrassCurve.Affine.Point.instSMulTorsionBy WeierstrassCurve.Affine.Point.instDistribMulActionTorsionBy WeierstrassCurve.Affine.Point.instSMulAlgEquiv
attribute [-simp] compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two

set_option autoImplicit false

universe u

theorem ModularCurve.IsGamma0PowAt.isAddCyclic_closure_and_natCard_eq_pow
    {F : Type u} [Field F] [IsAlgClosed F] [DecidableEq F] (W : WeierstrassCurve F) [W.IsElliptic]
    (p : ℕ) [Fact p.Prime] (hp : (p : F) ≠ 0) (k : ℕ) (h : Polynomial F)
    (hh : ModularCurve.IsGamma0PowAt W p k h) :
    IsAddCyclic (AddSubgroup.closure {P : W.toAffine.Point |
        ∃ (x y : F) (hxy : W.toAffine.Nonsingular x y),
          P = WeierstrassCurve.Affine.Point.some x y hxy ∧ h.eval x = 0}) ∧
      Nat.card (AddSubgroup.closure {P : W.toAffine.Point |
        ∃ (x y : F) (hxy : W.toAffine.Nonsingular x y),
          P = WeierstrassCurve.Affine.Point.some x y hxy ∧ h.eval x = 0}) = p ^ k := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_IsGamma0PowAt_isAddCyclic_closure_and_natCard_eq_pow.solution
