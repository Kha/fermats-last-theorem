import Mathlib
import Definitions.Def_FLTPrelim_FreyPackage
import Definitions.Def_FLTPrelim_GaloisRep
import Definitions.Def_FLTPrelim_Ramification
import P2M.Util
import P2M.Sol.S_WeierstrassCurve_valuation_pow_eq_of_torsion_of_not_inZeroComponentAt
attribute [-instance] WeierstrassCurve.Affine.Point.instFinite

open WeierstrassCurve WeierstrassCurve.Affine WeierstrassCurve.Affine.Point
theorem WeierstrassCurve.valuation_pow_eq_of_torsion_of_not_inZeroComponentAt
    (W : WeierstrassCurve ℤ) {q : ℕ} (hq : q.Prime) (hΔ : W.Δ ≠ 0)
    (hqΔ : (q : ℤ) ∣ W.Δ) (hqc₄ : ¬ (q : ℤ) ∣ W.c₄)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime q)
    {x₀ y₀ : AlgebraicClosure ℚ} (hx₀ : x₀ ∈ A) (hy₀ : y₀ ∈ A)
    (hFy : 2 * y₀ + (W.a₁ : AlgebraicClosure ℚ) * x₀ + W.a₃ = 0)
    (hFx : (W.a₁ : AlgebraicClosure ℚ) * y₀ = 3 * x₀ ^ 2 + 2 * W.a₂ * x₀ + W.a₄)
    (hnode : A.valuation ((W.b₂ : AlgebraicClosure ℚ) + 12 * x₀) = 1)
    (hbad : A.valuation (y₀ ^ 2 + W.a₁ * x₀ * y₀ + W.a₃ * y₀
      - (x₀ ^ 3 + W.a₂ * x₀ ^ 2 + W.a₄ * x₀ + W.a₆)) < 1)
    {ℓ : ℕ} (hℓ : ℓ.Prime) (hℓ2 : ℓ ≠ 2) (hℓq : ℓ ≠ q)
    {x y : AlgebraicClosure ℚ}
    (h : ((W.map (Int.castRingHom ℚ))⁄(AlgebraicClosure ℚ)).toAffine.Nonsingular x y)
    (htor : ℓ • (Point.some x y h) = 0) (hX : A.valuation (x - x₀) < 1) :
    A.valuation (W.Δ : AlgebraicClosure ℚ) < A.valuation (x - x₀) ^ 2 ∧
      ∃ j : ℕ, 1 ≤ j ∧ 2 * j < ℓ ∧
        A.valuation (x - x₀) ^ ℓ = A.valuation (W.Δ : AlgebraicClosure ℚ) ^ j := by p2m_exact_reverting @_root_.P2MW.S_WeierstrassCurve_valuation_pow_eq_of_torsion_of_not_inZeroComponentAt.solution
