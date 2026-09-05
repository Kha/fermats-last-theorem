module

import P2M.Sol.S_WeierstrassCurve_Affine_Point_smul_some_eq_zero_iff
public import Mathlib.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Basic
import P2M.Util
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar

namespace P2MW.S_WeierstrassCurve_Affine_Point_nsmul_some_eq_zero_iff_eval_prePsi

set_option autoImplicit false

open WeierstrassCurve WeierstrassCurve.Affine WeierstrassCurve.Affine.Point
open Polynomial
open scoped Polynomial.Bivariate

theorem solution {F : Type*} [Field F] [DecidableEq F] (W : WeierstrassCurve F) [W.IsElliptic]
    {n : ℕ} (hn : Odd n) {x y : F} (h : W.toAffine.Nonsingular x y) :
    n • Point.some x y h = 0 ↔ (W.preΨ' n).eval x = 0 := by
  rw [← natCast_zsmul, WeierstrassCurve.Affine.Point.smul_some_eq_zero_iff W h (n : ℤ)]

  obtain ⟨p, hp⟩ := AdjoinRoot.mk_eq_mk.mp (Affine.CoordinateRing.mk_ψ W (n : ℤ))
  have h0 : (W.toAffine.polynomial).evalEval x y = 0 := h.1
  have h1 := congrArg (evalEval x y) hp
  rw [evalEval_sub, evalEval_mul, h0, zero_mul, sub_eq_zero] at h1
  rw [h1, Ψ_ofNat, if_neg (Nat.not_even_iff_odd.mpr hn), mul_one, evalEval_C]
end S_WeierstrassCurve_Affine_Point_nsmul_some_eq_zero_iff_eval_prePsi
end P2MW

public section
open WeierstrassCurve WeierstrassCurve.Affine WeierstrassCurve.Affine.Point
theorem WeierstrassCurve.Affine.Point.nsmul_some_eq_zero_iff_eval_prePsi {F : Type*} [Field F] [DecidableEq F] (W : WeierstrassCurve F) [W.IsElliptic] {n : ℕ} (hn : Odd n) {x y : F} (h : W.toAffine.Nonsingular x y) : n • Point.some x y h = 0 ↔ (W.preΨ' n).eval x = 0 := by p2m_exact_reverting @_root_.P2MW.S_WeierstrassCurve_Affine_Point_nsmul_some_eq_zero_iff_eval_prePsi.solution
end
