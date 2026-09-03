import Definitions.Def_GaloisRep_Adic
import P2M.Util
namespace P2MW.S_GaloisRepAdic_det_residual

theorem solution {A : Type} [CommRing A] [IsLocalRing A] (ρ : GaloisRepAdic A) (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) : LinearMap.det (ρ.residual.ρ σ) = IsLocalRing.residue A (ρ.det σ : A) := LinearMap.det_baseChange (ρ.ρ σ)
