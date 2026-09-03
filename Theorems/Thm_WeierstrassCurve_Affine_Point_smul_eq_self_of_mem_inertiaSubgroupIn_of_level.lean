import Mathlib
import Definitions.Def_FLTPrelim_GaloisRep
import Definitions.Def_FLTPrelim_Ramification
import P2M.Util
import P2M.Sol.S_WeierstrassCurve_Affine_Point_smul_eq_self_of_mem_inertiaSubgroupIn_of_level

open WeierstrassCurve WeierstrassCurve.Affine WeierstrassCurve.Affine.Point
theorem WeierstrassCurve.Affine.Point.smul_eq_self_of_mem_inertiaSubgroupIn_of_level (W : WeierstrassCurve ℚ) (A : ValuationSubring (AlgebraicClosure ℚ)) {q : ℕ} (hq : q.Prime) {σ : (AlgebraicClosure ℚ) ≃ₐ[ℚ] (AlgebraicClosure ℚ)} (hσ : σ ∈ A.inertiaSubgroupIn ℚ) (x₀ y₀ α β : AlgebraicClosure ℚ) (hσx₀ : σ x₀ = x₀) (hσy₀ : σ y₀ = y₀) (hα : α ∈ A) (hαβ : A.valuation (α - β) = 1) (hsum : A.valuation (α + β + (W⁄(AlgebraicClosure ℚ)).a₁) < 1) (hFy : 2 * y₀ + (W⁄(AlgebraicClosure ℚ)).a₁ * x₀ + (W⁄(AlgebraicClosure ℚ)).a₃ = 0) {ℓ : ℕ} {x y : AlgebraicClosure ℚ} (h : (W⁄(AlgebraicClosure ℚ)).Nonsingular x y) (hP : ℓ • (Point.some x y h) = 0) (k : ℕ) (hlev : A.valuation (x - x₀) = A.valuation (q : AlgebraicClosure ℚ) ^ k) (hbr : A.valuation (y - y₀ - α * (x - x₀)) < A.valuation (x - x₀)) (htrans : ∀ (x' y' : AlgebraicClosure ℚ) (h' : (W⁄(AlgebraicClosure ℚ)).Nonsingular x' y'), ℓ • (Point.some x' y' h') = 0 → A.valuation (x' - x₀) = A.valuation (x - x₀) → Point.some x' y' h' ≠ Point.some x y h → Point.some x' y' h' ≠ -Point.some x y h → A.valuation (x' - x) = A.valuation (x - x₀)) : σ • Point.some x y h = Point.some x y h := by p2m_exact_reverting @_root_.P2MW.S_WeierstrassCurve_Affine_Point_smul_eq_self_of_mem_inertiaSubgroupIn_of_level.solution
