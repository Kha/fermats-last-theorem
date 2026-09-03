import Definitions.Def_GaloisRep_Adic
import P2M.Util
import P2M.Sol.S_GaloisRepAdic_exists_charpoly_eq_twist

set_option autoImplicit false
open Polynomial

theorem GaloisRepAdic.exists_charpoly_eq_twist
    {A : Type} [CommRing A] [IsLocalRing A] (ρ : GaloisRepAdic A)
    (θ : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) →* Aˣ)
    (hθ : ∃ L : IntermediateField ℚ (AlgebraicClosure ℚ), FiniteDimensional ℚ L ∧
      ∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, (∀ x ∈ L, σ x = x) → θ σ = 1) :
    ∃ ρ' : GaloisRepAdic A, ∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ,
      LinearMap.charpoly (ρ'.ρ σ) =
        X ^ 2 - C (((θ σ : Aˣ) : A) * LinearMap.trace A ρ.V (ρ.ρ σ)) * X
          + C (((θ σ : Aˣ) : A) ^ 2 * LinearMap.det (ρ.ρ σ)) := by p2m_exact_reverting @_root_.P2MW.S_GaloisRepAdic_exists_charpoly_eq_twist.solution
