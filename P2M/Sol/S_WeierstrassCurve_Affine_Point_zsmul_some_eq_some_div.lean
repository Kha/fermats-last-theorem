module

public import Mathlib.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Basic
import P2M.Util
import Definitions.Def_WeierstrassCurve_EDSEngine
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Altitude
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Topology.Sheaves.Init

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
