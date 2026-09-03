import Mathlib
import Definitions.Def_FLTPrelim_FreyPackage
import Definitions.Def_FLTPrelim_GaloisRep
import Definitions.Def_FLTPrelim_Ramification
import P2M.Util
import P2M.Sol.S_WeierstrassCurve_slope_mem_of_shallow

open WeierstrassCurve WeierstrassCurve.Affine WeierstrassCurve.Affine.Point
theorem WeierstrassCurve.slope_mem_of_shallow
    (W : WeierstrassCurve ℤ) (A : ValuationSubring (AlgebraicClosure ℚ))
    {x₀ y₀ : AlgebraicClosure ℚ} (hx₀ : x₀ ∈ A) (hy₀ : y₀ ∈ A)
    (hFy : 2 * y₀ + (W.a₁ : AlgebraicClosure ℚ) * x₀ + W.a₃ = 0)
    (hFx : (W.a₁ : AlgebraicClosure ℚ) * y₀ = 3 * x₀ ^ 2 + 2 * W.a₂ * x₀ + W.a₄)
    {x y : AlgebraicClosure ℚ}
    (h : ((W.map (Int.castRingHom ℚ))⁄(AlgebraicClosure ℚ)).toAffine.Nonsingular x y)
    (hX : A.valuation (x - x₀) < 1)
    (hsh : A.valuation (y₀ ^ 2 + W.a₁ * x₀ * y₀ + W.a₃ * y₀
      - (x₀ ^ 3 + W.a₂ * x₀ ^ 2 + W.a₄ * x₀ + W.a₆)) < A.valuation (x - x₀) ^ 2) :
    (y - y₀) / (x - x₀) ∈ A ∧ A.valuation (y - y₀) < 1 ∧
      A.valuation (((y - y₀) / (x - x₀)) ^ 2 + (W.a₁ : AlgebraicClosure ℚ) * ((y - y₀) / (x - x₀))
        - ((W.a₂ : AlgebraicClosure ℚ) + 3 * x₀)) < 1 := by p2m_exact_reverting @_root_.P2MW.S_WeierstrassCurve_slope_mem_of_shallow.solution
