module

public import Mathlib.NumberTheory.EllipticDivisibilitySequence
public import Mathlib.Algebra.Ring.NegOnePow
public import Mathlib.Data.Fin.VecNotation
public import Mathlib.Data.Fin.Tuple.Sort
public import Mathlib.Algebra.GroupWithZero.NonZeroDivisors
public import Mathlib.Algebra.MvPolynomial.CommRing
public import Mathlib.Algebra.MvPolynomial.Basic
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.Abel
public import Mathlib.Tactic.IntervalCases
public import Mathlib.Tactic.FieldSimp
public import Mathlib.GroupTheory.Perm.Basic
public import Mathlib.GroupTheory.Perm.Sign
public import Mathlib.Algebra.Polynomial.Bivariate
public import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point
public import Mathlib.AlgebraicGeometry.EllipticCurve.Jacobian.Point
public import Mathlib.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Basic
public import Definitions.Def_WeierstrassCurve_EDSEngine
import P2M.Util
public import Mathlib

namespace P2MW.S_WeierstrassCurve_Affine_Point_smul_some_eq_zero_iff

set_option autoImplicit false

theorem solution {F : Type*} [Field F] [DecidableEq F] (W : WeierstrassCurve F)
    {x y : F} (h : W.toAffine.Nonsingular x y) (n : ℤ) :
    n • (WeierstrassCurve.Affine.Point.some x y h) = 0 ↔ (W.ψ n).evalEval x y = 0 :=
  W.smul_eq_zero_iff_evalEval_ψ h n
end S_WeierstrassCurve_Affine_Point_smul_some_eq_zero_iff
end P2MW

public section
attribute [-instance] WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly
attribute [-simp] compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two

theorem WeierstrassCurve.Affine.Point.smul_some_eq_zero_iff
    {F : Type*} [Field F] [DecidableEq F] (W : WeierstrassCurve F)
    {x y : F} (h : W.toAffine.Nonsingular x y) (n : ℤ) :
    n • (WeierstrassCurve.Affine.Point.some x y h) = 0 ↔ (W.ψ n).evalEval x y = 0 := by p2m_exact_reverting @_root_.P2MW.S_WeierstrassCurve_Affine_Point_smul_some_eq_zero_iff.solution
end
