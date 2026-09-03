import Definitions.Def_GaloisRep_Adic
import P2M.Util
import P2M.Sol.S_GaloisRepAdic_det_residual

theorem GaloisRepAdic.det_residual {A : Type} [CommRing A] [IsLocalRing A] (ρ : GaloisRepAdic A) (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) : LinearMap.det (ρ.residual.ρ σ) = IsLocalRing.residue A (ρ.det σ : A) := by p2m_exact_reverting @_root_.P2MW.S_GaloisRepAdic_det_residual.solution
