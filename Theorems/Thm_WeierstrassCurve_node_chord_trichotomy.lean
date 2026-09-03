import Mathlib
import Definitions.Def_FLTPrelim_FreyPackage
import Definitions.Def_FLTPrelim_GaloisRep
import Definitions.Def_FLTPrelim_Ramification
import P2M.Util
import P2M.Sol.S_WeierstrassCurve_node_chord_trichotomy

open WeierstrassCurve WeierstrassCurve.Affine WeierstrassCurve.Affine.Point
theorem WeierstrassCurve.node_chord_trichotomy
    (W : WeierstrassCurve ℤ) (A : ValuationSubring (AlgebraicClosure ℚ))
    {x₀ α β : AlgebraicClosure ℚ} (hx₀ : x₀ ∈ A) (hα : α ∈ A)
    (hsum : α + β = -(W.a₁ : AlgebraicClosure ℚ))
    (hprod : α * β = -((W.a₂ : AlgebraicClosure ℚ) + 3 * x₀))
    (hαβ : A.valuation (α - β) = 1)
    {x₁ y₁ x₂ y₂ : AlgebraicClosure ℚ}
    (h₁ : ((W.map (Int.castRingHom ℚ))⁄(AlgebraicClosure ℚ)).toAffine.Nonsingular x₁ y₁)
    (h₂ : ((W.map (Int.castRingHom ℚ))⁄(AlgebraicClosure ℚ)).toAffine.Nonsingular x₂ y₂)
    (hX₁ : A.valuation (x₁ - x₀) < 1) (hX₂ : A.valuation (x₂ - x₀) < 1) (hy₁ : y₁ ∈ A)
    (hΔ : A.valuation ((y₁ - y₂) - α * (x₁ - x₂)) = A.valuation ((y₁ - y₂) - β * (x₁ - x₂)))
    (hne : (y₁ - y₂) - α * (x₁ - x₂) ≠ 0) :
    Point.some x₁ y₁ h₁ + Point.some x₂ y₂ h₂ = 0 ∨
      ∃ (x₃ y₃ : AlgebraicClosure ℚ) (h₃ : ((W.map (Int.castRingHom ℚ))⁄(AlgebraicClosure ℚ)).toAffine.Nonsingular x₃ y₃),
        Point.some x₁ y₁ h₁ + Point.some x₂ y₂ h₂ = .some x₃ y₃ h₃ ∧
          (x₃ ∉ A ∨ (x₃ ∈ A ∧ y₃ ∈ A ∧ A.valuation (x₃ - x₀) = 1 ∧
            A.valuation (x₁ - x₂) = A.valuation ((y₁ - y₂) - α * (x₁ - x₂)))) := by p2m_exact_reverting @_root_.P2MW.S_WeierstrassCurve_node_chord_trichotomy.solution
