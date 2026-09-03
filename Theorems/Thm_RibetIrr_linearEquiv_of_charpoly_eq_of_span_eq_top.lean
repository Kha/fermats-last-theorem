import Mathlib.LinearAlgebra.Charpoly.Basic
import Mathlib.LinearAlgebra.Span.Basic
import Mathlib.LinearAlgebra.FreeModule.Finite.Basic
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import P2M.Util
import P2M.Sol.S_RibetIrr_linearEquiv_of_charpoly_eq_of_span_eq_top

theorem RibetIrr.linearEquiv_of_charpoly_eq_of_span_eq_top
    {K : Type} [Field K]
    {V₁ V₂ : Type} [AddCommGroup V₁] [Module K V₁] [Module.Finite K V₁]
    [AddCommGroup V₂] [Module K V₂] [Module.Finite K V₂]
    (ρ₁ : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) →* Module.End K V₁)
    (ρ₂ : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) →* Module.End K V₂)
    (hfr₁ : Module.finrank K V₁ = 2) (hfr₂ : Module.finrank K V₂ = 2)
    (hspan₁ : Submodule.span K (Set.range ⇑ρ₁) = ⊤)
    (hspan₂ : Submodule.span K (Set.range ⇑ρ₂) = ⊤)
    (hcharpoly : ∀ σ, LinearMap.charpoly (ρ₁ σ) = LinearMap.charpoly (ρ₂ σ)) :
    ∃ e : V₁ ≃ₗ[K] V₂,
      ∀ (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (v : V₁),
        e (ρ₁ σ v) = ρ₂ σ (e v) := by p2m_exact_reverting @_root_.P2MW.S_RibetIrr_linearEquiv_of_charpoly_eq_of_span_eq_top.solution
