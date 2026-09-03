import Mathlib
import Definitions.Def_FLTPrelim_FreyPackage
import Definitions.Def_FLTPrelim_GaloisRep
import Definitions.Def_FLTPrelim_Ramification
import P2M.Util
import P2M.Sol.S_WeierstrassCurve_Affine_Point_smul_eq_self_of_two_torsion_of_mem_inertiaSubgroupIn_of_level

open WeierstrassCurve WeierstrassCurve.Affine WeierstrassCurve.Affine.Point
theorem WeierstrassCurve.Affine.Point.smul_eq_self_of_two_torsion_of_mem_inertiaSubgroupIn_of_level
    (W : WeierstrassCurve ℤ) {q : ℕ} (hq : q.Prime) (hq2 : q ≠ 2)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime q)
    {x₀ y₀ : AlgebraicClosure ℚ} (hx₀ : x₀ ∈ A) (hy₀ : y₀ ∈ A)
    (hFy : 2 * y₀ + (W.a₁ : AlgebraicClosure ℚ) * x₀ + W.a₃ = 0)
    (hFx : (W.a₁ : AlgebraicClosure ℚ) * y₀ = 3 * x₀ ^ 2 + 2 * W.a₂ * x₀ + W.a₄)
    (hnode : A.valuation ((W.b₂ : AlgebraicClosure ℚ) + 12 * x₀) = 1)
    (hbad : A.valuation (y₀ ^ 2 + W.a₁ * x₀ * y₀ + W.a₃ * y₀
      - (x₀ ^ 3 + W.a₂ * x₀ ^ 2 + W.a₄ * x₀ + W.a₆)) < 1)
    {σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ} (hσ : σ ∈ A.inertiaSubgroupIn ℚ)
    (hσx₀ : σ x₀ = x₀)
    {x y : AlgebraicClosure ℚ}
    (h : ((W.map (Int.castRingHom ℚ))⁄(AlgebraicClosure ℚ)).toAffine.Nonsingular x y)
    (htor : 2 • (Point.some x y h) = 0) (hX : A.valuation (x - x₀) < 1)
    (k : ℕ) (hlev : A.valuation (x - x₀) = A.valuation (q : AlgebraicClosure ℚ) ^ k) :
    σ • Point.some x y h = Point.some x y h := by p2m_exact_reverting @_root_.P2MW.S_WeierstrassCurve_Affine_Point_smul_eq_self_of_two_torsion_of_mem_inertiaSubgroupIn_of_level.solution
