import Definitions.Def_GaloisRep_Residual
import Mathlib.LinearAlgebra.Charpoly.BaseChange
import P2M.Util
namespace P2MW.S_ResidualGaloisRep_charpoly_baseChangeAlong

theorem solution {k : Type} [Field k] {k' : Type} [Field k'] (ψ : k →+* k') (ρ : ResidualGaloisRep k) (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) : LinearMap.charpoly ((ρ.baseChangeAlong ψ).ρ σ) = (LinearMap.charpoly (ρ.ρ σ)).map ψ := by
  letI : Algebra k k' := ψ.toAlgebra
  exact LinearMap.charpoly_baseChange (ρ.ρ σ) (A := k')
