import Mathlib
import Definitions.Def_Representation_AbsolutelyIrreducible
import Theorems.Thm_Representation_span_range_eq_top_of_isIrreducible
import Theorems.Thm_Representation_span_range_baseChange_eq_top_iff
import P2M.Util
namespace P2MW.S_Representation_span_range_eq_top_of_isAbsolutelyIrreducible

open scoped TensorProduct

universe u v

theorem solution {k G V : Type u} [Field k] [Group G] [AddCommGroup V]
  [Module k V] [FiniteDimensional k V] (ρ : Representation k G V) [Representation.IsAbsolutelyIrreducible.{u} ρ] :
  Submodule.span k (Set.range ρ) = ⊤ := by
  let K := AlgebraicClosure k
  haveI : (Representation.baseChange K ρ).IsIrreducible :=
    Representation.IsAbsolutelyIrreducible.absolutelyIrreducible K inferInstance inferInstance
  have hK : Submodule.span K (Set.range fun g => (ρ g).baseChange K) = ⊤ :=
    Representation.span_range_eq_top_of_isIrreducible (Representation.baseChange K ρ)
  exact (Representation.span_range_baseChange_eq_top_iff (K := K) ρ).mp hK
