import Mathlib.RepresentationTheory.Irreducible
import P2M.Util
import P2M.Sol.S_Representation_span_range_eq_top_of_isIrreducible

open Module LinearMap
theorem Representation.span_range_eq_top_of_isIrreducible
    {k G V : Type*} [Field k] [IsAlgClosed k] [Monoid G] [AddCommGroup V] [Module k V]
    [FiniteDimensional k V] (ρ : Representation k G V) [ρ.IsIrreducible] :
    Submodule.span k (Set.range ⇑ρ) = ⊤ := by p2m_exact_reverting @_root_.P2MW.S_Representation_span_range_eq_top_of_isIrreducible.solution
