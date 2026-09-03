import Mathlib
import Definitions.Def_TaylorWiles_Primes
import Definitions.Def_EllipticCurve_FrobeniusTrace
import Definitions.Def_FLTPrelim_Ramification
import P2M.Util
import P2M.Sol.S_FrobeniusDensity_exists_frobenius_conj_of_mul_self_eq_one_of_statement
attribute [-instance] AlgebraicClosure.Rat.isGalois

theorem FrobeniusDensity.exists_frobenius_conj_of_mul_self_eq_one_of_statement
    (hFD : ∀ (M : Type) [Field M] [NumberField M] [IsGalois ℚ M], FrobeniusDensity.Statement M)
    (L : IntermediateField ℚ (AlgebraicClosure ℚ)) [FiniteDimensional ℚ L]
    (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (hσ : σ * σ = 1) (S : Finset ℕ) :
    ∃ ℓ : ℕ, ℓ.Prime ∧ ℓ ∉ S ∧
      ∃ (A : ValuationSubring (AlgebraicClosure ℚ)) (τ γ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ),
        A.LiesOverPrime ℓ ∧ A.IsFrobeniusAt τ ℓ ∧ ∀ x ∈ L, σ x = (γ * τ * γ⁻¹) x := by p2m_exact_reverting @_root_.P2MW.S_FrobeniusDensity_exists_frobenius_conj_of_mul_self_eq_one_of_statement.solution
