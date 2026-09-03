import Mathlib
import Definitions.Def_GaloisRep_AdZeroMatrixGlue
import P2M.Util
import P2M.Sol.S_ResidualGaloisRep_finrank_ker_adZeroRep_sub_one_eq

universe u
theorem ResidualGaloisRep.finrank_ker_adZeroRep_sub_one_eq {k : Type} [Field k] (ρbar : ResidualGaloisRep k) (b : Module.Basis (Fin 2) k ρbar.V)
    (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) :
    Module.finrank k (LinearMap.ker (ρbar.adZeroRep σ - 1))
      = Module.finrank k ((LinearMap.ker (TaylorWiles.adAction (LinearMap.toMatrix b b (ρbar.ρ σ)))).comap (TaylorWiles.traceZero k).subtype) := by p2m_exact_reverting @_root_.P2MW.S_ResidualGaloisRep_finrank_ker_adZeroRep_sub_one_eq.solution
