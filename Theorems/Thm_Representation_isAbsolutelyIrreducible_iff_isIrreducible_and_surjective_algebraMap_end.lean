import Mathlib
import Definitions.Def_Representation_AbsolutelyIrreducible
import P2M.Util
import P2M.Sol.S_Representation_isAbsolutelyIrreducible_iff_isIrreducible_and_surjective_algebraMap_end
attribute [-simp] Deformation.matrixRepresentation_apply

open CategoryTheory IsLocalRing

universe u v
theorem Representation.isAbsolutelyIrreducible_iff_isIrreducible_and_surjective_algebraMap_end {k G V : Type u} [Field k]
  [Group G] [AddCommGroup V] [Module k V] [FiniteDimensional k V] (ρ : Representation k G V) :
  Representation.IsAbsolutelyIrreducible.{u} ρ ↔
    ρ.IsIrreducible ∧ Function.Surjective (algebraMap k (Module.End (MonoidAlgebra k G) ρ.asModule)) := by p2m_exact_reverting @_root_.P2MW.S_Representation_isAbsolutelyIrreducible_iff_isIrreducible_and_surjective_algebraMap_end.solution
