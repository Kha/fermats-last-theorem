import Definitions.Def_GaloisRep_ResidualEquiv
import P2M.Util
import P2M.Sol.S_ResidualGaloisRep_isEquiv_of_isAbsolutelyIrreducible_of_trace_eq

open Module LinearMap
theorem ResidualGaloisRep.isEquiv_of_isAbsolutelyIrreducible_of_trace_eq
    {k : Type} [Field k] (ρ₁ ρ₂ : ResidualGaloisRep k)
    (h₁ : ρ₁.IsAbsolutelyIrreducible) (h₂ : ρ₂.IsAbsolutelyIrreducible)
    (htr : ∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ,
      trace k ρ₁.V (ρ₁.ρ σ) = trace k ρ₂.V (ρ₂.ρ σ)) :
    ρ₁.IsEquiv ρ₂ := by p2m_exact_reverting @_root_.P2MW.S_ResidualGaloisRep_isEquiv_of_isAbsolutelyIrreducible_of_trace_eq.solution
