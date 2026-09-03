import Mathlib.RingTheory.Polynomial.ScaleRoots
import Definitions.Def_GaloisRep_Adic
import P2M.Util
import P2M.Sol.S_GaloisRepAdic_exists_charpoly_eq_scaleRoots_of_character

set_option autoImplicit false
open Polynomial
set_option synthInstance.maxHeartbeats 400000 in
set_option maxHeartbeats 1600000 in

theorem GaloisRepAdic.exists_charpoly_eq_scaleRoots_of_character
    {A : Type} [CommRing A] [IsLocalRing A] (ρ : GaloisRepAdic A)
    (ε : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) →* Aˣ)
    (hε : ∃ L : IntermediateField ℚ (AlgebraicClosure ℚ), FiniteDimensional ℚ L ∧
      ∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, (∀ x ∈ L, σ x = x) → ε σ = 1) :
    ∃ ρ' : GaloisRepAdic A, ∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ,
      LinearMap.charpoly (ρ'.ρ σ) = (LinearMap.charpoly (ρ.ρ σ)).scaleRoots ((ε σ : Aˣ) : A) := by p2m_exact_reverting @_root_.P2MW.S_GaloisRepAdic_exists_charpoly_eq_scaleRoots_of_character.solution
