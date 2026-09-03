import Mathlib.AlgebraicGeometry.EllipticCurve.Weierstrass
import P2M.Util
import P2M.Sol.S_WeierstrassCurve_Delta_ne_one_and_Delta_ne_neg_one

open WeierstrassCurve
theorem WeierstrassCurve.Delta_ne_one_and_Delta_ne_neg_one (W : WeierstrassCurve ℤ) : W.Δ ≠ 1 ∧ W.Δ ≠ -1 := by p2m_exact_reverting @_root_.P2MW.S_WeierstrassCurve_Delta_ne_one_and_Delta_ne_neg_one.solution
