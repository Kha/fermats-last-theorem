import Definitions.Def_GaloisRep_Adic
import Theorems.Thm_Representation_exists_linearEquiv_of_span_range_eq_top_of_trace_eq_of_isLocalRing
import Theorems.Thm_GaloisRepAdic_span_range_eq_top_of_residual_isAbsolutelyIrreducible
import P2M.Util
namespace P2MW.S_GaloisRepAdic_isEquiv_of_residual_isAbsolutelyIrreducible_of_trace_eq

set_option autoImplicit false

theorem solution
    {A : Type} [CommRing A] [IsLocalRing A] (ρ₁ ρ₂ : GaloisRepAdic A)
    (h₁ : ρ₁.residual.IsAbsolutelyIrreducible) (h₂ : ρ₂.residual.IsAbsolutelyIrreducible)
    (htr : ∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, ρ₁.trace σ = ρ₂.trace σ) :
    ρ₁.IsEquiv ρ₂ := by
  obtain ⟨e, he⟩ :=
    Representation.exists_linearEquiv_of_span_range_eq_top_of_trace_eq_of_isLocalRing
      ρ₁.ρ ρ₂.ρ (ρ₁.finrank_eq.trans ρ₂.finrank_eq.symm)
      (GaloisRepAdic.span_range_eq_top_of_residual_isAbsolutelyIrreducible ρ₁ h₁)
      (GaloisRepAdic.span_range_eq_top_of_residual_isAbsolutelyIrreducible ρ₂ h₂)
      htr
  exact ⟨⟨e, he⟩⟩
