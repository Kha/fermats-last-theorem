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
import Mathlib.RingTheory.Radical.NatInt
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

namespace P2MW.S_WeierstrassCurve_Affine_evalEval_psi_sq

open Polynomial
open scoped Polynomial.Bivariate

theorem PortCard.evalEval_ψ_sq {R : Type*} [CommRing R] (W : WeierstrassCurve R) {x y : R}
    (h : W.toAffine.Equation x y) (n : ℤ) : (W.ψ n).evalEval x y ^ 2 = (W.ΨSq n).eval x := by
  have hmk : WeierstrassCurve.Affine.CoordinateRing.mk W (W.ψ n ^ 2) =
      WeierstrassCurve.Affine.CoordinateRing.mk W (C (W.ΨSq n)) := by
    rw [map_pow, WeierstrassCurve.Affine.CoordinateRing.mk_ψ,
      WeierstrassCurve.Affine.CoordinateRing.mk_Ψ_sq]
  obtain ⟨p, hp⟩ := AdjoinRoot.mk_eq_mk.mp hmk
  have h0 : (W.toAffine.polynomial).evalEval x y = 0 := h
  have h1 := congrArg (evalEval x y) hp
  rw [evalEval_sub, evalEval_mul, h0, zero_mul, sub_eq_zero, evalEval_pow, evalEval_C] at h1
  exact h1

theorem PortCard.evalEval_φ {R : Type*} [CommRing R] (W : WeierstrassCurve R) {x y : R}
    (h : W.toAffine.Equation x y) (n : ℤ) : (W.φ n).evalEval x y = (W.Φ n).eval x := by
  obtain ⟨p, hp⟩ := AdjoinRoot.mk_eq_mk.mp (WeierstrassCurve.Affine.CoordinateRing.mk_φ W n)
  have h0 : (W.toAffine.polynomial).evalEval x y = 0 := h
  have h1 := congrArg (evalEval x y) hp
  rw [evalEval_sub, evalEval_mul, h0, zero_mul, sub_eq_zero, evalEval_C] at h1
  exact h1

theorem solution {R : Type*} [CommRing R] (W : WeierstrassCurve R) {x y : R} (h : W.toAffine.Equation x y) (n : ℤ) : (W.ψ n).evalEval x y ^ 2 = (W.ΨSq n).eval x :=
  PortCard.evalEval_ψ_sq W h n
end S_WeierstrassCurve_Affine_evalEval_psi_sq
end P2MW

public section
theorem WeierstrassCurve.Affine.evalEval_psi_sq {R : Type*} [CommRing R] (W : WeierstrassCurve R) {x y : R} (h : W.toAffine.Equation x y) (n : ℤ) : (W.ψ n).evalEval x y ^ 2 = (W.ΨSq n).eval x := by p2m_exact_reverting @_root_.P2MW.S_WeierstrassCurve_Affine_evalEval_psi_sq.solution
end
