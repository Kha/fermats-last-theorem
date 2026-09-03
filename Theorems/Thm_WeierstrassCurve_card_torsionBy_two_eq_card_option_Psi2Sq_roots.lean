import Mathlib.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Degree
import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point
import Mathlib.Algebra.Module.Torsion.Basic
import P2M.Util
import P2M.Sol.S_WeierstrassCurve_card_torsionBy_two_eq_card_option_Psi2Sq_roots

namespace WeierstrassCurve
theorem card_torsionBy_two_eq_card_option_Psi2Sq_roots {K : Type*} [Field K] [DecidableEq K]
    {W : WeierstrassCurve K} [W.IsElliptic] (h2 : (2 : K) ≠ 0) :
    Nat.card (Submodule.torsionBy ℤ W.toAffine.Point 2) =
      Nat.card (Option {x : K // W.Ψ₂Sq.eval x = 0}) := by p2m_exact_reverting @_root_.P2MW.S_WeierstrassCurve_card_torsionBy_two_eq_card_option_Psi2Sq_roots.solution
end WeierstrassCurve
