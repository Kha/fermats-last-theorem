import Mathlib
import Definitions.Def_Deformations_MatrixRepresentation
import Definitions.Def_Representation_AbsolutelyIrreducible
import P2M.Util
import P2M.Sol.S_Representation_isAbsolutelyIrreducible_matrix_iff_span_range_eq_top

open CategoryTheory IsLocalRing

universe u v
theorem Representation.isAbsolutelyIrreducible_matrix_iff_span_range_eq_top {n : Type} [Fintype n] [DecidableEq n] {G : Type u}
    [Group G] {k : Type u} [Field k] [Nonempty n] (φ : G →* GL n k) :
    Representation.IsAbsolutelyIrreducible.{u} (Deformation.matrixRepresentation φ) ↔
      Submodule.span k (Set.range fun g => (φ g).val) = ⊤ := by p2m_exact_reverting @_root_.P2MW.S_Representation_isAbsolutelyIrreducible_matrix_iff_span_range_eq_top.solution
