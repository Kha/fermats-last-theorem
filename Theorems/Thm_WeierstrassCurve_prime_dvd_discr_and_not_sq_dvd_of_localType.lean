import Definitions.Def_GaloisRep_LocalConditions
import Definitions.Def_FLTPrelim_Modularity
import P2M.Util
import P2M.Sol.S_WeierstrassCurve_prime_dvd_discr_and_not_sq_dvd_of_localType

set_option autoImplicit false
open Polynomial
theorem WeierstrassCurve.prime_dvd_discr_and_not_sq_dvd_of_localType
    (W : WeierstrassCurve ℤ) {M : ℕ} [NeZero M] (lam : ℕ) (hlamM : ¬ lam ∣ M)
    (O' : Type) [CommRing O'] [IsLocalRing O'] [CharZero O'] (ρ : GaloisRepAdic O')
    (h5a : ∀ q : ℕ, q.Prime → W.IsGoodPrimeFor q → q ≠ lam → ρ.IsUnramifiedAt q)
    (h5b : ∀ q : ℕ, q.Prime → ¬ W.IsGoodPrimeFor q → q ≠ lam → ρ.IsUnipotentOnInertiaAt q)
    (h5c : ∀ q : ℕ, q.Prime → W.IsGoodPrimeFor q → q ≠ lam →
      ∀ A : ValuationSubring (AlgebraicClosure ℚ), A.LiesOverPrime q →
        ∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, A.IsFrobeniusAt σ q →
          LinearMap.charpoly (ρ.ρ σ) = X ^ 2 - C ((W.apOfModel q : O')) * X + C ((q : O')))
    (hc : ∀ q : ℕ, q.Prime → q ≠ lam → q ^ 2 ∣ M → ¬ ρ.IsUnipotentOnInertiaAt q)
    (hd : ∀ q : ℕ, q.Prime → q ≠ lam → q ∣ M → ¬ q ^ 2 ∣ M →
      ∀ A : ValuationSubring (AlgebraicClosure ℚ), A.LiesOverPrime q →
        ∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, A.IsFrobeniusAt σ q →
          LinearMap.charpoly (ρ.ρ σ) = X ^ 2 - C ((q : O') + 1) * X + C ((q : O')) ∨
          LinearMap.charpoly (ρ.ρ σ) = X ^ 2 + C ((q : O') + 1) * X + C ((q : O'))) :
    ∀ q : ℕ, q.Prime → q ∣ M → (q : ℤ) ∣ W.Δ ∧ ¬ q ^ 2 ∣ M := by p2m_exact_reverting @_root_.P2MW.S_WeierstrassCurve_prime_dvd_discr_and_not_sq_dvd_of_localType.solution
