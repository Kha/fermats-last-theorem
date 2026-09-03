import Mathlib
import Definitions.Def_AlgebraicGeometry_OrderedAffineCoverCech
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_Scheme_nonempty_orderedAffineCover_of_compactSpace_univ

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry

universe u

theorem AlgebraicGeometry.Scheme.nonempty_orderedAffineCover_of_compactSpace_univ
    (X : Scheme.{u}) [CompactSpace X] : Nonempty X.OrderedAffineCover := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_Scheme_nonempty_orderedAffineCover_of_compactSpace_univ.solution
