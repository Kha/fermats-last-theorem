import Mathlib
import Definitions.Def_FLTPrelim_FreyPackage
import Definitions.Def_FLTPrelim_GaloisRep
import Definitions.Def_FLTPrelim_Ramification
import P2M.Util
import P2M.Sol.S_WeierstrassCurve_addX_sub_mul_addX_neg_sub_mul_sq_of_criticalCentre

open WeierstrassCurve WeierstrassCurve.Affine WeierstrassCurve.Affine.Point
theorem WeierstrassCurve.addX_sub_mul_addX_neg_sub_mul_sq_of_criticalCentre
    (W : WeierstrassCurve ℤ) {x₀ y₀ : AlgebraicClosure ℚ}
    (hFy : 2 * y₀ + (W.a₁ : AlgebraicClosure ℚ) * x₀ + W.a₃ = 0)
    (hFx : (W.a₁ : AlgebraicClosure ℚ) * y₀ = 3 * x₀ ^ 2 + 2 * W.a₂ * x₀ + W.a₄)
    {x₁ y₁ x₂ y₂ : AlgebraicClosure ℚ}
    (h₁ : ((W.map (Int.castRingHom ℚ))⁄(AlgebraicClosure ℚ)).toAffine.Nonsingular x₁ y₁)
    (h₂ : ((W.map (Int.castRingHom ℚ))⁄(AlgebraicClosure ℚ)).toAffine.Nonsingular x₂ y₂)
    (hx : x₁ ≠ x₂) :
    (((W.map (Int.castRingHom ℚ))⁄(AlgebraicClosure ℚ)).toAffine.addX x₁ x₂
        (((W.map (Int.castRingHom ℚ))⁄(AlgebraicClosure ℚ)).toAffine.slope x₁ x₂ y₁ y₂) - x₀)
      * (((W.map (Int.castRingHom ℚ))⁄(AlgebraicClosure ℚ)).toAffine.addX x₁ x₂
          (((W.map (Int.castRingHom ℚ))⁄(AlgebraicClosure ℚ)).toAffine.slope x₁ x₂ y₁
            (((W.map (Int.castRingHom ℚ))⁄(AlgebraicClosure ℚ)).toAffine.negY x₂ y₂)) - x₀)
      * (x₁ - x₂) ^ 2 =
    ((x₁ - x₀) * (x₂ - x₀)) ^ 2
      + (y₀ ^ 2 + W.a₁ * x₀ * y₀ + W.a₃ * y₀ - (x₀ ^ 3 + W.a₂ * x₀ ^ 2 + W.a₄ * x₀ + W.a₆))
          * (4 * (x₁ - x₀) + 4 * (x₂ - x₀) + ((W.b₂ : AlgebraicClosure ℚ) + 12 * x₀)) := by p2m_exact_reverting @_root_.P2MW.S_WeierstrassCurve_addX_sub_mul_addX_neg_sub_mul_sq_of_criticalCentre.solution
