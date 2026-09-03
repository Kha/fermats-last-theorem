import Definitions.Def_GaloisRep_Adic
import P2M.Util
import P2M.Sol.S_GaloisRepAdic_charpoly_residual

open Polynomial
theorem GaloisRepAdic.charpoly_residual {A : Type} [CommRing A] [IsLocalRing A] (ρ : GaloisRepAdic A) (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) : LinearMap.charpoly (ρ.residual.ρ σ) = (LinearMap.charpoly (ρ.ρ σ)).map (IsLocalRing.residue A) := by p2m_exact_reverting @_root_.P2MW.S_GaloisRepAdic_charpoly_residual.solution
