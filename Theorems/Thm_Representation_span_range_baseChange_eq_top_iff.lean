import Mathlib.RepresentationTheory.Basic
import Mathlib.LinearAlgebra.TensorProduct.Tower
import P2M.Util
import P2M.Sol.S_Representation_span_range_baseChange_eq_top_iff

open Module LinearMap
theorem Representation.span_range_baseChange_eq_top_iff
    {k K G V : Type*} [Field k] [Field K] [Algebra k K] [Monoid G] [AddCommGroup V] [Module k V]
    [FiniteDimensional k V] (ρ : Representation k G V) :
    Submodule.span K (Set.range fun g => (ρ g).baseChange K) = ⊤ ↔
      Submodule.span k (Set.range ⇑ρ) = ⊤ := by p2m_exact_reverting @_root_.P2MW.S_Representation_span_range_baseChange_eq_top_iff.solution
