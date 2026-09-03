import Definitions.Def_GaloisRep_Adic
import P2M.Util
import P2M.Sol.S_GaloisRepAdic_charpoly_baseChangeAlong

open Polynomial
theorem GaloisRepAdic.charpoly_baseChangeAlong {A : Type} [CommRing A] [IsLocalRing A] {B : Type} [CommRing B] [IsLocalRing B] (φ : A →+* B) (hφ : IsLocalHom φ) (ρ : GaloisRepAdic A) (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) : LinearMap.charpoly ((ρ.baseChangeAlong φ hφ).ρ σ) = (LinearMap.charpoly (ρ.ρ σ)).map φ := by p2m_exact_reverting @_root_.P2MW.S_GaloisRepAdic_charpoly_baseChangeAlong.solution
