import Definitions.Def_GaloisRep_Adic
import P2M.Util
import P2M.Sol.S_GaloisRepAdic_isEquiv_of_residual_isAbsolutelyIrreducible_of_trace_eq

theorem GaloisRepAdic.isEquiv_of_residual_isAbsolutelyIrreducible_of_trace_eq
    {A : Type} [CommRing A] [IsLocalRing A] (ρ₁ ρ₂ : GaloisRepAdic A)
    (h₁ : ρ₁.residual.IsAbsolutelyIrreducible) (h₂ : ρ₂.residual.IsAbsolutelyIrreducible)
    (htr : ∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, ρ₁.trace σ = ρ₂.trace σ) :
    ρ₁.IsEquiv ρ₂ := by p2m_exact_reverting @_root_.P2MW.S_GaloisRepAdic_isEquiv_of_residual_isAbsolutelyIrreducible_of_trace_eq.solution
