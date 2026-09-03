import Definitions.Def_GaloisRep_Residual
import P2M.Util
import P2M.Sol.S_ResidualGaloisRep_charpoly_baseChangeAlong

open Polynomial

theorem ResidualGaloisRep.charpoly_baseChangeAlong {k : Type} [Field k] {k' : Type} [Field k'] (ψ : k →+* k') (ρ : ResidualGaloisRep k) (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) : LinearMap.charpoly ((ρ.baseChangeAlong ψ).ρ σ) = (LinearMap.charpoly (ρ.ρ σ)).map ψ := by p2m_exact_reverting @_root_.P2MW.S_ResidualGaloisRep_charpoly_baseChangeAlong.solution
