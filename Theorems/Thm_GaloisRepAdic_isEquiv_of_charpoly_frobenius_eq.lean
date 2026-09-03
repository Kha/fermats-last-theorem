import Mathlib
import Definitions.Def_GaloisRep_Adic
import P2M.Util
import P2M.Sol.S_GaloisRepAdic_isEquiv_of_charpoly_frobenius_eq
attribute [-instance] FrobeniusDensity.isMaximal_ratPrimeIdeal FrobeniusDensity.liesOver_ratBelow AlgebraicClosure.Rat.isGalois
attribute [-simp] TaylorWiles.Seed.mk.injEq TaylorWiles.Seed.mk.sizeOf_spec

set_option autoImplicit false
theorem GaloisRepAdic.isEquiv_of_charpoly_frobenius_eq
    {A : Type} [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
    [IsAdicComplete (IsLocalRing.maximalIdeal A) A] [Finite (IsLocalRing.ResidueField A)]
    (ρ₁ ρ₂ : GaloisRepAdic A)
    (h₁ : ρ₁.residual.IsAbsolutelyIrreducible) (h₂ : ρ₂.residual.IsAbsolutelyIrreducible)
    (S : Finset ℕ)
    (h : ∀ ℓ : ℕ, ℓ.Prime → ℓ ∉ S →
      ∀ P : ValuationSubring (AlgebraicClosure ℚ), P.LiesOverPrime ℓ →
        ∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, P.IsFrobeniusAt σ ℓ →
          LinearMap.charpoly (ρ₁.ρ σ) = LinearMap.charpoly (ρ₂.ρ σ)) :
    ρ₁.IsEquiv ρ₂ := by p2m_exact_reverting @_root_.P2MW.S_GaloisRepAdic_isEquiv_of_charpoly_frobenius_eq.solution
