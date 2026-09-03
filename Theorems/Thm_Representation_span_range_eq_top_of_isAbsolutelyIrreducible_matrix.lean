import Mathlib
import Definitions.Def_Deformations_MatrixRepresentation
import Definitions.Def_Representation_AbsolutelyIrreducible
import P2M.Util
import P2M.Sol.S_Representation_span_range_eq_top_of_isAbsolutelyIrreducible_matrix

open CategoryTheory IsLocalRing

universe u v
theorem Representation.span_range_eq_top_of_isAbsolutelyIrreducible_matrix
    {n : Type} [Fintype n] [DecidableEq n] {G : Type u} [Group G] {k : Type u} [Field k]
    (ρ : G →* GL n k) [Representation.IsAbsolutelyIrreducible.{u} (Deformation.matrixRepresentation ρ)] :
    Submodule.span k (Set.range fun g => (ρ g).val) = ⊤ := by p2m_exact_reverting @_root_.P2MW.S_Representation_span_range_eq_top_of_isAbsolutelyIrreducible_matrix.solution
