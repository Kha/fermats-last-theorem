import Mathlib
import Definitions.Def_GaloisRep_Adic
import P2M.Util
import P2M.Sol.S_GaloisRepAdic_residual_isEquiv_and_det_sub_mem_of_charpoly_frobenius_eq
attribute [-instance] FrobeniusDensity.liesOver_ratBelow FrobeniusDensity.isMaximal_ratPrimeIdeal Deep.NTSupply.instNormalRayClassSubgroup NumberField.NormResidueChar.fintype_G NumberField.NormResidueChar.finite_G AlgebraicClosure.Rat.isGalois
attribute [-simp] TaylorWiles.Seed.mk.injEq TaylorWiles.Seed.mk.sizeOf_spec

set_option autoImplicit false

open Polynomial IsLocalRing

theorem GaloisRepAdic.residual_isEquiv_and_det_sub_mem_of_charpoly_frobenius_eq
    {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [CharZero O]
    (p : ℕ) [Fact p.Prime] (hpO : (p : O) ∈ maximalIdeal O)
    (ρ : GaloisRepAdic O)
    {k : Type} [Field k] (ρbar : ResidualGaloisRep k) (habs : ρbar.IsAbsolutelyIrreducible)
    (ψ : k →+* ResidueField O)
    (L : ℕ) [NeZero L] (κ : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) →* (ZMod L)ˣ)
    (hκ : ∀ (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (μ : AlgebraicClosure ℚ),
      μ ^ L = 1 → σ μ = μ ^ ((κ σ : ZMod L)).val)
    (χ : (ZMod L)ˣ →* Oˣ)
    (h2 : p ≠ 2 ∨ ∀ u : (ZMod L)ˣ, residue O (χ u) = 1)
    (S₀ : Finset ℕ) (a : ∀ ℓ : ℕ, ℓ.Prime → ℓ ∉ S₀ → O) (abar : ∀ ℓ : ℕ, ℓ.Prime → ℓ ∉ S₀ → k)
    (hred : ∀ (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓS : ℓ ∉ S₀), residue O (a ℓ hℓ hℓS) = ψ (abar ℓ hℓ hℓS))
    (hρ : ∀ (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓS : ℓ ∉ S₀),
      ∀ A : ValuationSubring (AlgebraicClosure ℚ), A.LiesOverPrime ℓ →
        ∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, A.IsFrobeniusAt σ ℓ →
          LinearMap.charpoly (ρ.ρ σ) =
            X ^ 2 - C (a ℓ hℓ hℓS) * X + C ((χ (κ σ) : O) * (ℓ : O)))
    (hρbar : ∀ (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓS : ℓ ∉ S₀),
      ∀ A : ValuationSubring (AlgebraicClosure ℚ), A.LiesOverPrime ℓ →
        ∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, A.IsFrobeniusAt σ ℓ →
          LinearMap.charpoly (ρbar.ρ σ) = X ^ 2 - C (abar ℓ hℓ hℓS) * X + C (ℓ : k)) :
    ρ.residual.IsEquiv (ρbar.baseChangeAlong ψ) ∧
    (∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, residue O (χ (κ σ)) = 1) ∧
    (∀ (n : ℕ) (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (b : ℕ),
      (∀ μ : AlgebraicClosure ℚ, μ ^ p ^ n = 1 → σ μ = μ ^ b) →
        LinearMap.det (ρ.ρ σ) - (b : O) * (χ (κ σ) : O) ∈ Ideal.span {((p ^ n : ℕ) : O)}) := by p2m_exact_reverting @_root_.P2MW.S_GaloisRepAdic_residual_isEquiv_and_det_sub_mem_of_charpoly_frobenius_eq.solution
