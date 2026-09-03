import Mathlib
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_IsClosedImmersion_isIso_stalkMap_of_mem_interior_range

set_option autoImplicit false

universe u

open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite

theorem AlgebraicGeometry.IsClosedImmersion.isIso_stalkMap_of_mem_interior_range
    {C X : Scheme.{u}} (i : C ⟶ X) [IsClosedImmersion i] [IsReduced X]
    (c : C) (hc : i c ∈ interior (Set.range i)) : IsIso (i.stalkMap c) := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_IsClosedImmersion_isIso_stalkMap_of_mem_interior_range.solution
