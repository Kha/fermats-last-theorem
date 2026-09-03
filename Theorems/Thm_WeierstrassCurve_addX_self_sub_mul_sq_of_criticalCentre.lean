import Mathlib
import Definitions.Def_FLTPrelim_FreyPackage
import Definitions.Def_FLTPrelim_GaloisRep
import Definitions.Def_FLTPrelim_Ramification
import P2M.Util
import P2M.Sol.S_WeierstrassCurve_addX_self_sub_mul_sq_of_criticalCentre

open WeierstrassCurve WeierstrassCurve.Affine WeierstrassCurve.Affine.Point
theorem WeierstrassCurve.addX_self_sub_mul_sq_of_criticalCentre
    (W : WeierstrassCurve ℤ) {x₀ y₀ : AlgebraicClosure ℚ}
    (hFy : 2 * y₀ + (W.a₁ : AlgebraicClosure ℚ) * x₀ + W.a₃ = 0)
    (hFx : (W.a₁ : AlgebraicClosure ℚ) * y₀ = 3 * x₀ ^ 2 + 2 * W.a₂ * x₀ + W.a₄)
    {x y : AlgebraicClosure ℚ}
    (h : ((W.map (Int.castRingHom ℚ))⁄(AlgebraicClosure ℚ)).toAffine.Nonsingular x y)
    (hΨ : 2 * y + (W.a₁ : AlgebraicClosure ℚ) * x + W.a₃ ≠ 0) :
    (((W.map (Int.castRingHom ℚ))⁄(AlgebraicClosure ℚ)).toAffine.addX x x
        (((W.map (Int.castRingHom ℚ))⁄(AlgebraicClosure ℚ)).toAffine.slope x x y y) - x₀)
      * (2 * y + (W.a₁ : AlgebraicClosure ℚ) * x + W.a₃) ^ 2 =
    (x - x₀) ^ 4
      + 8 * (y₀ ^ 2 + W.a₁ * x₀ * y₀ + W.a₃ * y₀ - (x₀ ^ 3 + W.a₂ * x₀ ^ 2 + W.a₄ * x₀ + W.a₆))
          * (x - x₀)
      + ((W.b₂ : AlgebraicClosure ℚ) + 12 * x₀)
          * (y₀ ^ 2 + W.a₁ * x₀ * y₀ + W.a₃ * y₀ - (x₀ ^ 3 + W.a₂ * x₀ ^ 2 + W.a₄ * x₀ + W.a₆)) := by p2m_exact_reverting @_root_.P2MW.S_WeierstrassCurve_addX_self_sub_mul_sq_of_criticalCentre.solution
