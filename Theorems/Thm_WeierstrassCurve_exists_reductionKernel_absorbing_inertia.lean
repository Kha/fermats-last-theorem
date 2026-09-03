import Mathlib
import Definitions.Def_FLTPrelim_GaloisRep
import Definitions.Def_FLTPrelim_Ramification
import P2M.Util
import P2M.Sol.S_WeierstrassCurve_exists_reductionKernel_absorbing_inertia

open WeierstrassCurve WeierstrassCurve.Affine WeierstrassCurve.Affine.Point
theorem WeierstrassCurve.exists_reductionKernel_absorbing_inertia (W : WeierstrassCurve ℚ) [W.IsElliptic] (A : ValuationSubring (AlgebraicClosure ℚ)) (h₁ : algebraMap ℚ (AlgebraicClosure ℚ) W.a₁ ∈ A) (h₂ : algebraMap ℚ (AlgebraicClosure ℚ) W.a₂ ∈ A) (h₃ : algebraMap ℚ (AlgebraicClosure ℚ) W.a₃ ∈ A) (h₄ : algebraMap ℚ (AlgebraicClosure ℚ) W.a₄ ∈ A) (h₆ : algebraMap ℚ (AlgebraicClosure ℚ) W.a₆ ∈ A) (hΔ : (algebraMap ℚ (AlgebraicClosure ℚ) W.Δ)⁻¹ ∈ A) : ∃ H : AddSubgroup (W⁄(AlgebraicClosure ℚ)).Point, (∀ Q : (W⁄(AlgebraicClosure ℚ)).Point, Q ∈ H ↔ ∀ (x y : AlgebraicClosure ℚ) (h : (W⁄(AlgebraicClosure ℚ)).toAffine.Nonsingular x y), Q = Point.some x y h → x ∉ A) ∧ ∀ σ ∈ A.inertiaSubgroupIn ℚ, ∀ Q : (W⁄(AlgebraicClosure ℚ)).Point, σ • Q - Q ∈ H := by p2m_exact_reverting @_root_.P2MW.S_WeierstrassCurve_exists_reductionKernel_absorbing_inertia.solution
