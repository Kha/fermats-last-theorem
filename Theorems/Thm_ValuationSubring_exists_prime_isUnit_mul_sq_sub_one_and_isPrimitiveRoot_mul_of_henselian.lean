import Mathlib
import Definitions.Def_FLTPrelim_Ramification
import P2M.Util
import P2M.Sol.S_ValuationSubring_exists_prime_isUnit_mul_sq_sub_one_and_isPrimitiveRoot_mul_of_henselian

set_option autoImplicit false

open IsLocalRing

theorem ValuationSubring.exists_prime_isUnit_mul_sq_sub_one_and_isPrimitiveRoot_mul_of_henselian
    (q : ℕ) [Fact q.Prime] (hq : 5 ≤ q) (M' : ℕ) [NeZero M']
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime q)
    (k₀ : IntermediateField ℚ (AlgebraicClosure ℚ))
    (hhens : HenselianLocalRing ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))))
    (hres : IsAlgClosed (ResidueField ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))))
    (ζq : ↥k₀) (hζq : IsPrimitiveRoot ((ζq : ↥k₀) : AlgebraicClosure ℚ) q)

    (ϖt : ↥k₀) (hϖtA : (ϖt : AlgebraicClosure ℚ) ∈ A)
    (hϖt : ∃ u : ↥A, IsUnit u ∧ (ϖt : AlgebraicClosure ℚ) ^ (q ^ 2 - 1) = (q : AlgebraicClosure ℚ) * (u : AlgebraicClosure ℚ)) :

    (∃ u : ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))), IsUnit u ∧
      (⟨ϖt, hϖtA⟩ : ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ^ (q ^ 2 - 1) = (q : _) * u) ∧
    ∃ (ℓ : ℕ), ℓ.Prime ∧ 3 ≤ ℓ ∧ ℓ ≠ q ∧ ¬ ℓ ∣ M' ∧
      IsUnit ((ℓ * (ℓ ^ 2 - 1) : ℕ) : ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ∧
      ∃ ξ : ↥k₀, IsPrimitiveRoot ξ (q * ℓ) ∧ ((ξ : ↥k₀) : AlgebraicClosure ℚ) ∈ A ∧
        ∃ ι : ↥k₀ →+* ℂ, ι ξ = Complex.exp (2 * Real.pi * Complex.I / (q * ℓ)) := by p2m_exact_reverting @_root_.P2MW.S_ValuationSubring_exists_prime_isUnit_mul_sq_sub_one_and_isPrimitiveRoot_mul_of_henselian.solution
