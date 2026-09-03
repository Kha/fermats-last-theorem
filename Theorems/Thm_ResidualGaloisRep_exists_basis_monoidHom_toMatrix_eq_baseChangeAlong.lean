import Mathlib
import Definitions.Def_GaloisRep_Residual
import P2M.Util
import P2M.Sol.S_ResidualGaloisRep_exists_basis_monoidHom_toMatrix_eq_baseChangeAlong

set_option autoImplicit false
theorem ResidualGaloisRep.exists_basis_monoidHom_toMatrix_eq_baseChangeAlong
    {k L : Type} [Field k] [Field L] (ψ : k →+* L) (R : ResidualGaloisRep k) :
    ∃ (b : Module.Basis (Fin 2) L (R.baseChangeAlong ψ).V)
      (ρM : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) →* GL (Fin 2) L),
      GaloisFactorsThroughFiniteLevel ρM ∧
      (∀ σ, (ρM σ).val = LinearMap.toMatrix b b ((R.baseChangeAlong ψ).ρ σ)) ∧
      (∀ σ, (ρM σ).val.charpoly = (LinearMap.charpoly (R.ρ σ)).map ψ) := by p2m_exact_reverting @_root_.P2MW.S_ResidualGaloisRep_exists_basis_monoidHom_toMatrix_eq_baseChangeAlong.solution
