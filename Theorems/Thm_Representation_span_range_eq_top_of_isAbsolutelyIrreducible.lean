import Mathlib
import Definitions.Def_Representation_AbsolutelyIrreducible
import P2M.Util
import P2M.Sol.S_Representation_span_range_eq_top_of_isAbsolutelyIrreducible

open CategoryTheory IsLocalRing

universe u v
theorem Representation.span_range_eq_top_of_isAbsolutelyIrreducible {k G V : Type u} [Field k] [Group G] [AddCommGroup V]
  [Module k V] [FiniteDimensional k V] (ρ : Representation k G V) [Representation.IsAbsolutelyIrreducible.{u} ρ] :
  Submodule.span k (Set.range ρ) = ⊤ := by p2m_exact_reverting @_root_.P2MW.S_Representation_span_range_eq_top_of_isAbsolutelyIrreducible.solution
