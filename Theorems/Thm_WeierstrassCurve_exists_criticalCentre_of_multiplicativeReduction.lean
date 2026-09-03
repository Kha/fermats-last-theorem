import Mathlib
import Definitions.Def_FLTPrelim_FreyPackage
import Definitions.Def_FLTPrelim_GaloisRep
import Definitions.Def_FLTPrelim_Ramification
import P2M.Util
import P2M.Sol.S_WeierstrassCurve_exists_criticalCentre_of_multiplicativeReduction

open WeierstrassCurve WeierstrassCurve.Affine WeierstrassCurve.Affine.Point
theorem WeierstrassCurve.exists_criticalCentre_of_multiplicativeReduction
    (W : WeierstrassCurve ℤ) {q : ℕ} (hq : q.Prime) (hΔ : W.Δ ≠ 0)
    (hqΔ : (q : ℤ) ∣ W.Δ) (hqc₄ : ¬ (q : ℤ) ∣ W.c₄)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime q) :
    ∃ x₀ y₀ : AlgebraicClosure ℚ, x₀ ∈ A ∧ y₀ ∈ A ∧
      2 * y₀ + (W.a₁ : AlgebraicClosure ℚ) * x₀ + W.a₃ = 0 ∧
      (W.a₁ : AlgebraicClosure ℚ) * y₀ = 3 * x₀ ^ 2 + 2 * W.a₂ * x₀ + W.a₄ ∧
      A.valuation ((W.b₂ : AlgebraicClosure ℚ) + 12 * x₀) = 1 ∧
      A.valuation (y₀ ^ 2 + W.a₁ * x₀ * y₀ + W.a₃ * y₀
        - (x₀ ^ 3 + W.a₂ * x₀ ^ 2 + W.a₄ * x₀ + W.a₆)) < 1 ∧
      (∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, σ ∈ A.inertiaSubgroupIn ℚ →
        σ x₀ = x₀ ∧ σ y₀ = y₀) := by p2m_exact_reverting @_root_.P2MW.S_WeierstrassCurve_exists_criticalCentre_of_multiplicativeReduction.solution
