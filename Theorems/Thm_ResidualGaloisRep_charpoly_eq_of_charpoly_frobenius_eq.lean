import Definitions.Def_TaylorWiles_Primes
import Definitions.Def_EllipticCurve_FrobeniusTrace
import Definitions.Def_GaloisRep_Residual
import Mathlib.LinearAlgebra.Charpoly.Basic
import P2M.Util
import P2M.Sol.S_ResidualGaloisRep_charpoly_eq_of_charpoly_frobenius_eq
attribute [-instance] AlgebraicClosure.Rat.isGalois

open scoped NumberField Pointwise
theorem ResidualGaloisRep.charpoly_eq_of_charpoly_frobenius_eq
    (hFD : ∀ (M : Type) [Field M] [NumberField M] [IsGalois ℚ M], FrobeniusDensity.Statement M)
    {k : Type} [Field k] (ρ₁ ρ₂ : ResidualGaloisRep k) (S : Finset ℕ)
    (hfrob : ∀ ℓ : ℕ, ℓ.Prime → ℓ ∉ S → ∀ (A : ValuationSubring (AlgebraicClosure ℚ))
      (τ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ), A.LiesOverPrime ℓ → A.IsFrobeniusAt τ ℓ →
        (ρ₁.ρ τ).charpoly = (ρ₂.ρ τ).charpoly)
    (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) :
    (ρ₁.ρ σ).charpoly = (ρ₂.ρ σ).charpoly := by p2m_exact_reverting @_root_.P2MW.S_ResidualGaloisRep_charpoly_eq_of_charpoly_frobenius_eq.solution
