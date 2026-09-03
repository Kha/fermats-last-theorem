import Mathlib
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_surjective_of_closedPoints_subset_range

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Topology

universe u

theorem AlgebraicGeometry.surjective_of_closedPoints_subset_range {X Y : Scheme.{u}} (f : X ⟶ Y)
    [LocallyOfFinitePresentation f] [QuasiCompact f] [JacobsonSpace Y]
    (h : closedPoints Y ⊆ Set.range f.base) : Surjective f := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_surjective_of_closedPoints_subset_range.solution
