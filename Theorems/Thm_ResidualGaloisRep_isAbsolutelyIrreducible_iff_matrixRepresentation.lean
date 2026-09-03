import Mathlib
import Definitions.Def_GaloisRep_Residual
import Definitions.Def_Representation_AbsolutelyIrreducible
import Definitions.Def_Deformations_MatrixRepresentation
import P2M.Util
import P2M.Sol.S_ResidualGaloisRep_isAbsolutelyIrreducible_iff_matrixRepresentation
attribute [-simp] ResidualGaloisRep.Equiv.mk.sizeOf_spec ResidualGaloisRep.Equiv.mk.injEq

set_option autoImplicit false
theorem ResidualGaloisRep.isAbsolutelyIrreducible_iff_matrixRepresentation
    {k : Type} [Field k] (ρbar : ResidualGaloisRep k) (b : Module.Basis (Fin 2) k ρbar.V)
    (ρ₀ : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) →* GL (Fin 2) k)
    (hρ₀ : ∀ σ, ((ρ₀ σ : GL (Fin 2) k) : Matrix (Fin 2) (Fin 2) k) = LinearMap.toMatrix b b (ρbar.ρ σ)) :
    ρbar.IsAbsolutelyIrreducible ↔
      Representation.IsAbsolutelyIrreducible.{0} (Deformation.matrixRepresentation ρ₀) := by p2m_exact_reverting @_root_.P2MW.S_ResidualGaloisRep_isAbsolutelyIrreducible_iff_matrixRepresentation.solution
