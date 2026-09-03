import Mathlib
import Definitions.Def_GaloisRep_Residual
import P2M.Util
import P2M.Sol.S_GaloisRep_charpoly_eq_map_charpoly_of_frobenius_trace_eq_of_det_eq
attribute [-instance] FrobeniusDensity.isMaximal_ratPrimeIdeal AlgebraicClosure.Rat.isGalois FrobeniusDensity.liesOver_ratBelow
attribute [-simp] TaylorWiles.Seed.mk.injEq TaylorWiles.Seed.mk.sizeOf_spec

set_option autoImplicit false

open Polynomial
open scoped MatrixGroups

theorem GaloisRep.charpoly_eq_map_charpoly_of_frobenius_trace_eq_of_det_eq
    {k κ : Type} [Field k] [Field κ] (ι : k →+* κ)
    (ρbar : ResidualGaloisRep k) (S : Finset ℕ) (a : ℕ → k)
    (hρbar : ∀ ℓ : ℕ, ℓ.Prime → ℓ ∉ S →
      ∀ A : ValuationSubring (AlgebraicClosure ℚ), A.LiesOverPrime ℓ →
        ∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, A.IsFrobeniusAt σ ℓ →
          LinearMap.charpoly (ρbar.ρ σ) = X ^ 2 - C (a ℓ) * X + C (ℓ : k))
    (ρ : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) →* GL (Fin 2) κ)
    (hρ : GaloisFactorsThroughFiniteLevel ρ)
    (htr : ∀ ℓ : ℕ, ℓ.Prime → ℓ ∉ S →
      ∀ A : ValuationSubring (AlgebraicClosure ℚ), A.LiesOverPrime ℓ →
        ∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, A.IsFrobeniusAt σ ℓ →
          Matrix.trace (ρ σ).val = ι (a ℓ))
    (hdet : ∀ ℓ : ℕ, ℓ.Prime → ℓ ∉ S →
      ∀ A : ValuationSubring (AlgebraicClosure ℚ), A.LiesOverPrime ℓ →
        ∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, A.IsFrobeniusAt σ ℓ →
          Matrix.det (ρ σ).val = (ℓ : κ))
    (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) :
    (ρ σ).val.charpoly = (LinearMap.charpoly (ρbar.ρ σ)).map ι := by p2m_exact_reverting @_root_.P2MW.S_GaloisRep_charpoly_eq_map_charpoly_of_frobenius_trace_eq_of_det_eq.solution
