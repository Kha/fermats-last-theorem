import Definitions.Def_GaloisRep_Adic
import P2M.Util
import P2M.Sol.S_GaloisAction_isUnramifiedAt_of_injective_of_map_apply

set_option autoImplicit false

open scoped TensorProduct

theorem GaloisAction.isUnramifiedAt_of_injective_of_map_apply
    (A : Type) [CommRing A]
    (V : Type) [AddCommGroup V] [Module A V] (W : Type) [AddCommGroup W] [Module A W]
    (ρ : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) →* Module.End A V)
    (ρW : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) →* Module.End A W)
    (f : W →ₗ[A] V) (hf : Function.Injective f)
    (hfρ : ∀ (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (w : W), f (ρW σ w) = ρ σ (f w))
    (ℓ : ℕ)
    (hρ : ∀ P : ValuationSubring (AlgebraicClosure ℚ), P.LiesOverPrime ℓ →
      ∀ σ ∈ P.inertiaSubgroupIn ℚ, ρ σ = 1) :
    ∀ P : ValuationSubring (AlgebraicClosure ℚ), P.LiesOverPrime ℓ →
      ∀ σ ∈ P.inertiaSubgroupIn ℚ, ρW σ = 1 := by p2m_exact_reverting @_root_.P2MW.S_GaloisAction_isUnramifiedAt_of_injective_of_map_apply.solution
