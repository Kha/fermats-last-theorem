import Mathlib
import P2M.Util
import P2M.Sol.S_WeierstrassCurve_Affine_evalEval_phi

theorem WeierstrassCurve.Affine.evalEval_phi {R : Type*} [CommRing R] (W : WeierstrassCurve R) {x y : R} (h : W.toAffine.Equation x y) (n : ℤ) : (W.φ n).evalEval x y = (W.Φ n).eval x := by p2m_exact_reverting @_root_.P2MW.S_WeierstrassCurve_Affine_evalEval_phi.solution
