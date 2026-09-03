import Definitions.Def_GaloisRep_Adic
import P2M.Util
import P2M.Sol.S_GaloisRepAdic_charpoly_eq_of_isEquiv

theorem GaloisRepAdic.charpoly_eq_of_isEquiv {A : Type} [CommRing A] [IsLocalRing A] {ρ₁ ρ₂ : GaloisRepAdic A} (h : ρ₁.IsEquiv ρ₂) (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) : LinearMap.charpoly (ρ₁.ρ σ) = LinearMap.charpoly (ρ₂.ρ σ) := by p2m_exact_reverting @_root_.P2MW.S_GaloisRepAdic_charpoly_eq_of_isEquiv.solution
