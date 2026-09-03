import Mathlib
import Definitions.Def_AlgebraicGeometry_OrderedAffineCoverCech
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_Scheme_nonempty_orderedAffineCover_of_compactSpace

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry

theorem AlgebraicGeometry.Scheme.nonempty_orderedAffineCover_of_compactSpace
    (X : Scheme.{0}) [CompactSpace X] : Nonempty X.OrderedAffineCover := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_Scheme_nonempty_orderedAffineCover_of_compactSpace.solution
