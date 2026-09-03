import Mathlib.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Basic
import Mathlib.FieldTheory.Separable
import P2M.Util
import P2M.Sol.S_WeierstrassCurve_separable_Psi3

open WeierstrassCurve
theorem WeierstrassCurve.separable_Psi3 {K : Type*} [Field K] (W : WeierstrassCurve K) (hΔ : W.Δ ≠ 0) (h3 : (3 : K) ≠ 0) : W.Ψ₃.Separable := by p2m_exact_reverting @_root_.P2MW.S_WeierstrassCurve_separable_Psi3.solution
