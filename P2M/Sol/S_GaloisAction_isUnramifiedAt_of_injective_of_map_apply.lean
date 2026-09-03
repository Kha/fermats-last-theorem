import Definitions.Def_GaloisRep_Adic
import P2M.Util
namespace P2MW.S_GaloisAction_isUnramifiedAt_of_injective_of_map_apply

set_option autoImplicit false

open scoped TensorProduct

theorem solution
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
      ∀ σ ∈ P.inertiaSubgroupIn ℚ, ρW σ = 1 := by
  intro P hP σ hσ
  refine LinearMap.ext fun w => hf ?_
  rw [hfρ, hρ P hP σ hσ, Module.End.one_apply, Module.End.one_apply]
