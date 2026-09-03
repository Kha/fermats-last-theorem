import Mathlib.LinearAlgebra.Trace
import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import P2M.Util
import P2M.Sol.S_Representation_span_range_eq_top_of_span_range_eq_top_of_trace_eq

set_option autoImplicit false

theorem Representation.span_range_eq_top_of_span_range_eq_top_of_trace_eq
    {k : Type} [Field k] {G : Type} [Monoid G]
    {V₁ V₂ : Type} [AddCommGroup V₁] [Module k V₁] [FiniteDimensional k V₁]
    [AddCommGroup V₂] [Module k V₂] [FiniteDimensional k V₂]
    (ρ₁ : G →* Module.End k V₁) (ρ₂ : G →* Module.End k V₂)
    (hrank : Module.finrank k V₁ = Module.finrank k V₂)
    (hspan₁ : Submodule.span k (Set.range ⇑ρ₁) = ⊤)
    (htr : ∀ g : G, LinearMap.trace k V₁ (ρ₁ g) = LinearMap.trace k V₂ (ρ₂ g)) :
    Submodule.span k (Set.range ⇑ρ₂) = ⊤ := by p2m_exact_reverting @_root_.P2MW.S_Representation_span_range_eq_top_of_span_range_eq_top_of_trace_eq.solution
