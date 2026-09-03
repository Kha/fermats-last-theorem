import Definitions.Def_GaloisRep_Residual
import P2M.Util
import P2M.Sol.S_ResidualGaloisRep_isAbsolutelyIrreducible_of_isAbsolutelyIrreducible_of_trace_eq
attribute [-simp] ResidualGaloisRep.Equiv.mk.sizeOf_spec ResidualGaloisRep.Equiv.mk.injEq

open Module LinearMap

theorem ResidualGaloisRep.isAbsolutelyIrreducible_of_isAbsolutelyIrreducible_of_trace_eq
    {k : Type} [Field k] (ρ₁ ρ₂ : ResidualGaloisRep k) (h₁ : ρ₁.IsAbsolutelyIrreducible)
    (htr : ∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ,
      trace k ρ₁.V (ρ₁.ρ σ) = trace k ρ₂.V (ρ₂.ρ σ)) :
    ρ₂.IsAbsolutelyIrreducible := by p2m_exact_reverting @_root_.P2MW.S_ResidualGaloisRep_isAbsolutelyIrreducible_of_isAbsolutelyIrreducible_of_trace_eq.solution
