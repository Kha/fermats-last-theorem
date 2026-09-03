import Definitions.Def_GaloisRep_Residual
import Theorems.Thm_LinearMap_charpoly_of_finrank_eq_two
import P2M.Util
namespace P2MW.S_ResidualGaloisRep_charpoly_eq

open Polynomial

theorem solution {k : Type} [Field k] (ρ : ResidualGaloisRep k) (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) : LinearMap.charpoly (ρ.ρ σ) = X ^ 2 - C (LinearMap.trace k ρ.V (ρ.ρ σ)) * X + C (LinearMap.det (ρ.ρ σ)) :=
  LinearMap.charpoly_of_finrank_eq_two ρ.finrank_eq _
