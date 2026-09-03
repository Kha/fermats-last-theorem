import Definitions.Def_GaloisRep_Adic
import P2M.Util
import P2M.Sol.S_GaloisAction_isUnramifiedAt_of_eq_mul

set_option autoImplicit false

open scoped TensorProduct

theorem GaloisAction.isUnramifiedAt_of_eq_mul
    (A : Type) [CommRing A] (V : Type) [AddCommGroup V] [Module A V]
    (ρ₁ ρ₂ ρ : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) →* Module.End A V)
    (hρ : ∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, ρ σ = ρ₁ σ * ρ₂ σ)
    (ℓ : ℕ)
    (h₁ : ∀ P : ValuationSubring (AlgebraicClosure ℚ), P.LiesOverPrime ℓ →
      ∀ σ ∈ P.inertiaSubgroupIn ℚ, ρ₁ σ = 1)
    (h₂ : ∀ P : ValuationSubring (AlgebraicClosure ℚ), P.LiesOverPrime ℓ →
      ∀ σ ∈ P.inertiaSubgroupIn ℚ, ρ₂ σ = 1) :
    ∀ P : ValuationSubring (AlgebraicClosure ℚ), P.LiesOverPrime ℓ →
      ∀ σ ∈ P.inertiaSubgroupIn ℚ, ρ σ = 1 := by p2m_exact_reverting @_root_.P2MW.S_GaloisAction_isUnramifiedAt_of_eq_mul.solution
