import Mathlib
import Definitions.Def_GaloisRep_FrobeniusPowerDense
import P2M.Util
import P2M.Sol.S_Representation_cayleyHamilton_of_frobeniusPowerDense

theorem Representation.cayleyHamilton_of_frobeniusPowerDense {k : Type*} [CommRing k] {V : Type*} [AddCommGroup V] [Module k V]
    (ρV : Representation k (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) V)
    (ρ : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) →* Matrix (Fin 2) (Fin 2) k)
    {S : Finset ℕ}
    (hCH : ∀ ℓ : ℕ, ℓ.Prime → ℓ ∉ S →
      ∀ A : ValuationSubring (AlgebraicClosure ℚ), A.LiesOverPrime ℓ →
        ∀ τ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, A.IsFrobeniusAt τ ℓ →
          ρV τ * ρV τ - (ρ τ).trace • ρV τ + (ρ τ).det • (1 : Module.End k V) = 0)
    (hdense : FrobeniusPowerDense S (ρ.ker ⊓ ρV.ker))
    (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) :
    ρV σ * ρV σ - (ρ σ).trace • ρV σ + (ρ σ).det • (1 : Module.End k V) = 0 := by p2m_exact_reverting @_root_.P2MW.S_Representation_cayleyHamilton_of_frobeniusPowerDense.solution
