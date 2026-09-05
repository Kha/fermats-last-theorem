module

public import Mathlib
import P2M.Util
import P2M.Sol.S_WeierstrassCurve_Affine_Point_nsmul_some_eq_zero_iff_eval_prePsi

@[expose] public section

open WeierstrassCurve WeierstrassCurve.Affine WeierstrassCurve.Affine.Point
theorem WeierstrassCurve.Affine.Point.nsmul_some_eq_zero_iff_eval_prePsi {F : Type*} [Field F] [DecidableEq F] (W : WeierstrassCurve F) [W.IsElliptic] {n : ℕ} (hn : Odd n) {x y : F} (h : W.toAffine.Nonsingular x y) : n • Point.some x y h = 0 ↔ (W.preΨ' n).eval x = 0 := by p2m_exact_reverting @_root_.P2MW.S_WeierstrassCurve_Affine_Point_nsmul_some_eq_zero_iff_eval_prePsi.solution
