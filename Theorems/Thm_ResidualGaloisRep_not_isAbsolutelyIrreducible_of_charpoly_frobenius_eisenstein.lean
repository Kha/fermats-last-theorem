import Mathlib
import Definitions.Def_GaloisRep_Adic
import P2M.Util
import P2M.Sol.S_ResidualGaloisRep_not_isAbsolutelyIrreducible_of_charpoly_frobenius_eisenstein
attribute [-instance] FrobeniusDensity.liesOver_ratBelow FrobeniusDensity.isMaximal_ratPrimeIdeal Deep.NTSupply.instNormalRayClassSubgroup NumberField.NormResidueChar.fintype_G NumberField.NormResidueChar.finite_G AlgebraicClosure.Rat.isGalois
attribute [-simp] TaylorWiles.Seed.mk.injEq TaylorWiles.Seed.mk.sizeOf_spec ExtCitation.archimedeanLoc_archimedeanGen complexConjAlgEquiv_apply

set_option autoImplicit false

open Polynomial IsLocalRing

theorem ResidualGaloisRep.not_isAbsolutelyIrreducible_of_charpoly_frobenius_eisenstein
    {k k' : Type} [Field k] [Field k'] (p : ℕ) [Fact p.Prime] [CharP k' p]
    (ρbar : ResidualGaloisRep k) (ψ : k →+* k')
    (L : ℕ) [NeZero L] (κ : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) →* (ZMod L)ˣ)
    (hκ : ∀ (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (μ : AlgebraicClosure ℚ),
      μ ^ L = 1 → σ μ = μ ^ ((κ σ : ZMod L)).val)
    (c₁ c₂ : (ZMod L)ˣ →* k'ˣ) (h2 : p ≠ 2 ∨ c₁ * c₂ = 1)
    (S₀ : Finset ℕ) (abar : ∀ ℓ : ℕ, ℓ.Prime → ℓ ∉ S₀ → k)
    (hρbar : ∀ (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓS : ℓ ∉ S₀),
      ∀ A : ValuationSubring (AlgebraicClosure ℚ), A.LiesOverPrime ℓ →
        ∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, A.IsFrobeniusAt σ ℓ →
          LinearMap.charpoly (ρbar.ρ σ) = X ^ 2 - C (abar ℓ hℓ hℓS) * X + C (ℓ : k))
    (heis : ∀ (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓS : ℓ ∉ S₀),
      ∀ A : ValuationSubring (AlgebraicClosure ℚ), A.LiesOverPrime ℓ →
        ∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, A.IsFrobeniusAt σ ℓ →
          ψ (abar ℓ hℓ hℓS) = (c₁ (κ σ) : k') + (ℓ : k') * (c₂ (κ σ) : k')) :
    ¬ ρbar.IsAbsolutelyIrreducible := by p2m_exact_reverting @_root_.P2MW.S_ResidualGaloisRep_not_isAbsolutelyIrreducible_of_charpoly_frobenius_eisenstein.solution
