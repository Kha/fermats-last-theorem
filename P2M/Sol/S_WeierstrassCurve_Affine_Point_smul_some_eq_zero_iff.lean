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
public import P2M.Util

@[expose] public section
namespace P2MW.S_WeierstrassCurve_Affine_Point_smul_some_eq_zero_iff

set_option autoImplicit false

theorem solution {F : Type*} [Field F] [DecidableEq F] (W : WeierstrassCurve F)
    {x y : F} (h : W.toAffine.Nonsingular x y) (n : ℤ) :
    n • (WeierstrassCurve.Affine.Point.some x y h) = 0 ↔ (W.ψ n).evalEval x y = 0 :=
  W.smul_eq_zero_iff_evalEval_ψ h n
