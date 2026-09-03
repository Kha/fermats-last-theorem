import Definitions.Def_GaloisRep_LocalConditions
import Theorems.Thm_GaloisRepAdic_charpoly_eq_of_charpoly_frobenius_eq
import P2M.Util
namespace P2MW.S_GaloisRepAdic_localType_congr_of_charpoly_frobenius_eq
attribute [-instance] FrobeniusDensity.isMaximal_ratPrimeIdeal FrobeniusDensity.liesOver_ratBelow AlgebraicClosure.Rat.isGalois
attribute [-simp] TaylorWiles.Seed.mk.injEq TaylorWiles.Seed.mk.sizeOf_spec

set_option autoImplicit false

theorem solution
    {A : Type} [CommRing A] [IsLocalRing A] [IsNoetherianRing A] (ρ₁ ρ₂ : GaloisRepAdic A)
    (S : Finset ℕ)
    (hfrob : ∀ ℓ : ℕ, ℓ.Prime → ℓ ∉ S → ∀ (B : ValuationSubring (AlgebraicClosure ℚ))
      (τ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ), B.LiesOverPrime ℓ → B.IsFrobeniusAt τ ℓ →
        LinearMap.charpoly (ρ₁.ρ τ) = LinearMap.charpoly (ρ₂.ρ τ)) :
    (∀ q : ℕ, ρ₁.IsUnipotentOnInertiaAt q ↔ ρ₂.IsUnipotentOnInertiaAt q) ∧
    (∀ (q : ℕ) (B : ValuationSubring (AlgebraicClosure ℚ))
      (τ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ), B.LiesOverPrime q → B.IsFrobeniusAt τ q →
        LinearMap.charpoly (ρ₁.ρ τ) = LinearMap.charpoly (ρ₂.ρ τ)) := by
  have hall : ∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ,
      LinearMap.charpoly (ρ₁.ρ σ) = LinearMap.charpoly (ρ₂.ρ σ) :=
    GaloisRepAdic.charpoly_eq_of_charpoly_frobenius_eq ρ₁ ρ₂ S hfrob
  refine ⟨fun q => ?_, fun _ _ τ _ _ => hall τ⟩
  constructor
  · intro h P hP σ hσ
    rw [← hall σ]
    exact h P hP σ hσ
  · intro h P hP σ hσ
    rw [hall σ]
    exact h P hP σ hσ
