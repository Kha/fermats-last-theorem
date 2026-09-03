import Definitions.Def_GaloisRep_Adic
import P2M.Util
namespace P2MW.S_GaloisAction_isUnramifiedAt_pi

set_option autoImplicit false

open scoped TensorProduct

theorem solution
    (A : Type) [CommRing A] (ι : Type)
    (V : ι → Type) [∀ i, AddCommGroup (V i)] [∀ i, Module A (V i)]
    (ρ : ∀ i, (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) →* Module.End A (V i))
    (ρpi : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) →* Module.End A (∀ i, V i))
    (hρpi : ∀ (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (f : ∀ i, V i) (i : ι),
      ρpi σ f i = ρ i σ (f i))
    (ℓ : ℕ)
    (hρ : ∀ i, ∀ P : ValuationSubring (AlgebraicClosure ℚ), P.LiesOverPrime ℓ →
      ∀ σ ∈ P.inertiaSubgroupIn ℚ, ρ i σ = 1) :
    ∀ P : ValuationSubring (AlgebraicClosure ℚ), P.LiesOverPrime ℓ →
      ∀ σ ∈ P.inertiaSubgroupIn ℚ, ρpi σ = 1 := by
  intro P hP σ hσ
  refine LinearMap.ext fun f => funext fun i => ?_
  rw [hρpi, hρ i P hP σ hσ, Module.End.one_apply, Module.End.one_apply]
