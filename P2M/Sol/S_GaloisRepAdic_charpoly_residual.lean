import Definitions.Def_GaloisRep_Adic
import P2M.Util
namespace P2MW.S_GaloisRepAdic_charpoly_residual

open Polynomial

theorem solution {A : Type} [CommRing A] [IsLocalRing A] (ρ : GaloisRepAdic A) (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) : LinearMap.charpoly (ρ.residual.ρ σ) = (LinearMap.charpoly (ρ.ρ σ)).map (IsLocalRing.residue A) := LinearMap.charpoly_baseChange (ρ.ρ σ) (IsLocalRing.ResidueField A)
