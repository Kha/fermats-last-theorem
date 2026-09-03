import Mathlib.LinearAlgebra.Trace
import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.RingTheory.LocalRing.MaximalIdeal.Basic
import P2M.Util
import P2M.Sol.S_Representation_exists_linearEquiv_of_span_range_eq_top_of_trace_eq_of_isLocalRing

theorem Representation.exists_linearEquiv_of_span_range_eq_top_of_trace_eq_of_isLocalRing
    {A : Type} [CommRing A] [IsLocalRing A] {G : Type} [Monoid G]
    {V₁ V₂ : Type} [AddCommGroup V₁] [Module A V₁] [Module.Free A V₁] [Module.Finite A V₁]
    [AddCommGroup V₂] [Module A V₂] [Module.Free A V₂] [Module.Finite A V₂]
    (ρ₁ : G →* Module.End A V₁) (ρ₂ : G →* Module.End A V₂)
    (hrank : Module.finrank A V₁ = Module.finrank A V₂)
    (hspan₁ : Submodule.span A (Set.range ⇑ρ₁) = ⊤)
    (hspan₂ : Submodule.span A (Set.range ⇑ρ₂) = ⊤)
    (htr : ∀ g : G, LinearMap.trace A V₁ (ρ₁ g) = LinearMap.trace A V₂ (ρ₂ g)) :
    ∃ e : V₁ ≃ₗ[A] V₂, ∀ (g : G) (v : V₁), e (ρ₁ g v) = ρ₂ g (e v) := by p2m_exact_reverting @_root_.P2MW.S_Representation_exists_linearEquiv_of_span_range_eq_top_of_trace_eq_of_isLocalRing.solution
