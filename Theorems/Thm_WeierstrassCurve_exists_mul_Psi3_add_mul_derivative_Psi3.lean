import Mathlib.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Basic
import Mathlib.FieldTheory.Separable
import P2M.Util
import P2M.Sol.S_WeierstrassCurve_exists_mul_Psi3_add_mul_derivative_Psi3

open WeierstrassCurve Polynomial
theorem WeierstrassCurve.exists_mul_Psi3_add_mul_derivative_Psi3 {R : Type*} [CommRing R] (W : WeierstrassCurve R) : (-144 * X ^ 2 - 24 * C W.b₂ * X + 3 * C (W.b₂ ^ 2 - 32 * W.b₄)) * W.Ψ₃ + (36 * X ^ 3 + 9 * C W.b₂ * X ^ 2 + C (42 * W.b₄ - W.b₂ ^ 2) * X + C (27 * W.b₆ - W.b₂ * W.b₄)) * derivative W.Ψ₃ = C (-3 * W.Δ) := by p2m_exact_reverting @_root_.P2MW.S_WeierstrassCurve_exists_mul_Psi3_add_mul_derivative_Psi3.solution
