import Mathlib.RepresentationTheory.Irreducible
import Mathlib.RepresentationTheory.Intertwining
import P2M.Util
import P2M.Sol.S_Representation_isIrreducible_of_span_range_eq_top

theorem Representation.isIrreducible_of_span_range_eq_top
    {k : Type*} [Field k] {G : Type*} [Monoid G]
    {V : Type*} [AddCommGroup V] [Module k V]
    (ρ : Representation k G V) [Nontrivial V]
    (hspan : Submodule.span k (Set.range ⇑ρ) = ⊤) : ρ.IsIrreducible := by p2m_exact_reverting @_root_.P2MW.S_Representation_isIrreducible_of_span_range_eq_top.solution
