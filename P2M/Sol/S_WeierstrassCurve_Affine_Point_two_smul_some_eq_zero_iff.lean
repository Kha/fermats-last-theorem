module

public import Mathlib.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Basic
import P2M.Util
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
import Std.Tactic.BVDecide.Normalize.Prop

namespace P2MW.S_WeierstrassCurve_Affine_Point_two_smul_some_eq_zero_iff

open Polynomial

theorem PortCard.sub_negY_sq_eq_eval_Ψ₂Sq {R : Type*} [CommRing R] (W : WeierstrassCurve R)
    {x y : R} (e : W.toAffine.Equation x y) :
    (y - W.toAffine.negY x y) ^ 2 = W.Ψ₂Sq.eval x := by
  rw [WeierstrassCurve.Affine.equation_iff] at e
  simp only [WeierstrassCurve.Affine.negY, WeierstrassCurve.Ψ₂Sq, WeierstrassCurve.b₂,
    WeierstrassCurve.b₄, WeierstrassCurve.b₆, eval_add, eval_mul, eval_pow, eval_C, eval_X]
  linear_combination 4 * e

theorem PortCard.two_smul_some_eq_zero_iff {F : Type*} [Field F] [DecidableEq F]
    (W : WeierstrassCurve F) {x y : F} (h : W.toAffine.Nonsingular x y) :
    2 • WeierstrassCurve.Affine.Point.some x y h = 0 ↔ W.Ψ₂Sq.eval x = 0 := by
  have key : 2 • WeierstrassCurve.Affine.Point.some x y h = 0 ↔ y = W.toAffine.negY x y := by
    rw [two_nsmul, add_eq_zero_iff_eq_neg, WeierstrassCurve.Affine.Point.neg_some,
      WeierstrassCurve.Affine.Point.some.injEq]
    simp
  rw [key, ← PortCard.sub_negY_sq_eq_eval_Ψ₂Sq W h.left, pow_eq_zero_iff two_ne_zero, sub_eq_zero]

theorem PortCard.Ψ₂Sq_ne_zero_of_isElliptic {F : Type*} [Field F] (W : WeierstrassCurve F)
    [W.IsElliptic] : W.Ψ₂Sq ≠ 0 := by
  intro h0
  rw [WeierstrassCurve.Ψ₂Sq_eq, Cubic.toPoly_eq_zero_iff] at h0
  have h4 : (4 : F) = 0 := congrArg Cubic.a h0
  have hb₂ : W.b₂ = 0 := congrArg Cubic.b h0
  have hb₆ : W.b₆ = 0 := congrArg Cubic.d h0
  have h2 : (2 : F) = 0 := by
    have h22 : (2 : F) * 2 = 0 := by linear_combination h4
    rcases mul_eq_zero.mp h22 with h | h <;> exact h
  have hΔ : W.Δ = 0 := by
    rw [show W.Δ = -W.b₂ ^ 2 * W.b₈ - 8 * W.b₄ ^ 3 - 27 * W.b₆ ^ 2 + 9 * W.b₂ * W.b₄ * W.b₆
      from rfl]
    linear_combination (-W.b₂ * W.b₈ + 9 * W.b₄ * W.b₆) * hb₂ + (-27 * W.b₆) * hb₆ +
      (-4 * W.b₄ ^ 3) * h2
  exact W.isUnit_Δ.ne_zero hΔ

theorem solution {F : Type*} [Field F] [DecidableEq F] (W : WeierstrassCurve F) {x y : F} (h : W.toAffine.Nonsingular x y) : 2 • WeierstrassCurve.Affine.Point.some x y h = 0 ↔ W.Ψ₂Sq.eval x = 0 :=
  PortCard.two_smul_some_eq_zero_iff W h
end S_WeierstrassCurve_Affine_Point_two_smul_some_eq_zero_iff
end P2MW

public section
theorem WeierstrassCurve.Affine.Point.two_smul_some_eq_zero_iff {F : Type*} [Field F] [DecidableEq F] (W : WeierstrassCurve F) {x y : F} (h : W.toAffine.Nonsingular x y) : 2 • WeierstrassCurve.Affine.Point.some x y h = 0 ↔ W.Ψ₂Sq.eval x = 0 := by p2m_exact_reverting @_root_.P2MW.S_WeierstrassCurve_Affine_Point_two_smul_some_eq_zero_iff.solution
end
