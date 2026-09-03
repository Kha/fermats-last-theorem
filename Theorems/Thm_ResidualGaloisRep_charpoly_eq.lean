import Definitions.Def_GaloisRep_Residual
import P2M.Util
import P2M.Sol.S_ResidualGaloisRep_charpoly_eq

open Polynomial

theorem ResidualGaloisRep.charpoly_eq {k : Type} [Field k] (ρ : ResidualGaloisRep k) (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) : LinearMap.charpoly (ρ.ρ σ) = X ^ 2 - C (LinearMap.trace k ρ.V (ρ.ρ σ)) * X + C (LinearMap.det (ρ.ρ σ)) := by p2m_exact_reverting @_root_.P2MW.S_ResidualGaloisRep_charpoly_eq.solution
