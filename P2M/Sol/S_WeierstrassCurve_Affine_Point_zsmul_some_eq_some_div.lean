module

public import Definitions.Def_WeierstrassCurve_EDSEngine
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
public import Mathlib.GroupTheory.Perm.Cycle.Type
public import Mathlib.Algebra.Polynomial.Bivariate
public import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point
public import Mathlib.AlgebraicGeometry.EllipticCurve.Jacobian.Point
public import Mathlib.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Basic
public import Mathlib.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Degree
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.FieldTheory.Separable
public import Mathlib.Data.Nat.Factorization.Induction
public import Mathlib.Logic.Embedding.Set
public import Mathlib.SetTheory.Cardinal.Finite
public import Mathlib.Data.Set.Card
public import Mathlib.Algebra.Module.Torsion.Basic
import P2M.Util
public import Mathlib

namespace P2MW.S_WeierstrassCurve_Affine_Point_zsmul_some_eq_some_div

section PortCardMulX

namespace PortCard

open WeierstrassCurve WeierstrassCurve.Affine WeierstrassCurve.Affine.Point Polynomial
open scoped Polynomial.Bivariate

variable {F : Type*} [Field F] [DecidableEq F] (W : WeierstrassCurve F)

theorem zsmul_some_eq_some_of_evalEval_ψ_ne_zero {x y : F} (h : W.toAffine.Nonsingular x y)
    {n : ℤ} (hψ : (W.ψ n).evalEval x y ≠ 0) :
    ∃ (x' y' : F) (h' : W.toAffine.Nonsingular x' y'),
      n • Point.some x y h = Point.some x' y' h' ∧
        x' * (W.ψ n).evalEval x y ^ 2 = (W.φ n).evalEval x y ∧
        x' * (W.ΨSq n).eval x = (W.Φ n).eval x := by
  have heq : W.toAffine.Equation x y := h.left
  have hψsq := W.evalEval_ψ_sq heq n
  have key := zsmul_eq_smulEval W h n
  have hVz : smulEval W x y n 2 ≠ 0 := hψ
  have hV := key ▸ (n • Jacobian.Point.fromAffine (Point.some x y h)).nonsingular
  have hQeq : (n • Jacobian.Point.fromAffine (Point.some x y h)) =
      Jacobian.Point.mk hV := Jacobian.Point.ext key
  refine ⟨smulEval W x y n 0 / smulEval W x y n 2 ^ 2,
    smulEval W x y n 1 / smulEval W x y n 2 ^ 3,
    (Jacobian.nonsingular_of_Z_ne_zero hVz).mp hV, ?_, ?_, ?_⟩
  · calc n • Point.some x y h
        = Jacobian.Point.toAffineAddEquiv W
            (n • Jacobian.Point.fromAffine (Point.some x y h)) := by
          rw [map_zsmul, ← Jacobian.Point.toAffineAddEquiv_symm_apply,
            AddEquiv.apply_symm_apply]
      _ = _ := by
          rw [hQeq, Jacobian.Point.toAffineAddEquiv_apply]
          exact Jacobian.Point.toAffineLift_of_Z_ne_zero hVz
  · show (W.φ n).evalEval x y / (W.ψ n).evalEval x y ^ 2 * (W.ψ n).evalEval x y ^ 2 =
        (W.φ n).evalEval x y
    rw [div_mul_cancel₀ _ (pow_ne_zero 2 hψ)]
  · show (W.φ n).evalEval x y / (W.ψ n).evalEval x y ^ 2 * (W.ΨSq n).eval x = (W.Φ n).eval x
    rw [← hψsq, div_mul_cancel₀ _ (pow_ne_zero 2 hψ), W.evalEval_φ heq]

theorem zsmul_some_eq_some_of_eval_ΨSq_ne_zero {x y : F} (h : W.toAffine.Nonsingular x y)
    {n : ℤ} (hn : (W.ΨSq n).eval x ≠ 0) :
    ∃ (x' y' : F) (h' : W.toAffine.Nonsingular x' y'),
      n • Point.some x y h = Point.some x' y' h' ∧ x' * (W.ΨSq n).eval x = (W.Φ n).eval x := by
  have hψ : (W.ψ n).evalEval x y ≠ 0 := fun h0 =>
    hn (by rw [← W.evalEval_ψ_sq h.left n, h0]; exact zero_pow two_ne_zero)
  obtain ⟨x', y', h', hP, -, hx⟩ := zsmul_some_eq_some_of_evalEval_ψ_ne_zero W h hψ
  exact ⟨x', y', h', hP, hx⟩

theorem zsmul_some_eq_zero_iff_eval_ΨSq {x y : F} (h : W.toAffine.Nonsingular x y) (n : ℤ) :
    n • Point.some x y h = 0 ↔ (W.ΨSq n).eval x = 0 := by
  rw [W.smul_eq_zero_iff_evalEval_ψ h n, ← W.evalEval_ψ_sq h.left n]
  exact ⟨fun h0 => by rw [h0]; exact zero_pow two_ne_zero, fun h0 => (sq_eq_zero_iff).mp h0⟩

theorem zsmul_some_eq_some_div {x y : F} (h : W.toAffine.Nonsingular x y) {n : ℤ}
    (hψ : (W.ψ n).evalEval x y ≠ 0) :
    ∃ (y' : F) (h' : W.toAffine.Nonsingular ((W.Φ n).eval x / (W.ΨSq n).eval x) y'),
      n • Point.some x y h = Point.some ((W.Φ n).eval x / (W.ΨSq n).eval x) y' h' := by
  obtain ⟨x', y', h', hP, -, hx⟩ := zsmul_some_eq_some_of_evalEval_ψ_ne_zero W h hψ
  have hΨ : (W.ΨSq n).eval x ≠ 0 := by
    rw [← W.evalEval_ψ_sq h.left n]; exact pow_ne_zero 2 hψ
  obtain rfl : x' = (W.Φ n).eval x / (W.ΨSq n).eval x := by rw [eq_div_iff hΨ]; exact hx
  exact ⟨y', h', hP⟩

end PortCard

end PortCardMulX

theorem solution {F : Type*} [Field F] [DecidableEq F] (W : WeierstrassCurve F) {x y : F} (h : W.toAffine.Nonsingular x y) {n : ℤ} (hψ : (W.ψ n).evalEval x y ≠ 0) : ∃ (y' : F) (h' : W.toAffine.Nonsingular ((W.Φ n).eval x / (W.ΨSq n).eval x) y'), n • WeierstrassCurve.Affine.Point.some x y h = WeierstrassCurve.Affine.Point.some ((W.Φ n).eval x / (W.ΨSq n).eval x) y' h' :=
  PortCard.zsmul_some_eq_some_div W h hψ
end S_WeierstrassCurve_Affine_Point_zsmul_some_eq_some_div
end P2MW

public section
attribute [-instance] WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly
attribute [-simp] compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two

theorem WeierstrassCurve.Affine.Point.zsmul_some_eq_some_div {F : Type*} [Field F] [DecidableEq F] (W : WeierstrassCurve F) {x y : F} (h : W.toAffine.Nonsingular x y) {n : ℤ} (hψ : (W.ψ n).evalEval x y ≠ 0) : ∃ (y' : F) (h' : W.toAffine.Nonsingular ((W.Φ n).eval x / (W.ΨSq n).eval x) y'), n • WeierstrassCurve.Affine.Point.some x y h = WeierstrassCurve.Affine.Point.some ((W.Φ n).eval x / (W.ΨSq n).eval x) y' h' := by p2m_exact_reverting @_root_.P2MW.S_WeierstrassCurve_Affine_Point_zsmul_some_eq_some_div.solution
end
