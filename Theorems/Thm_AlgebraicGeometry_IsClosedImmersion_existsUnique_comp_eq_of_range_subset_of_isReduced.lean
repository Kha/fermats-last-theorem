import Mathlib
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_IsClosedImmersion_existsUnique_comp_eq_of_range_subset_of_isReduced
set_option autoImplicit false

universe u

open CategoryTheory AlgebraicGeometry

theorem AlgebraicGeometry.IsClosedImmersion.existsUnique_comp_eq_of_range_subset_of_isReduced
    {X Y T : Scheme.{u}} (i : Y ⟶ X) [IsClosedImmersion i] (f : T ⟶ X) [IsReduced T]
    (H : Set.range f.base ⊆ Set.range i.base) :
    ∃! g : T ⟶ Y, g ≫ i = f := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_IsClosedImmersion_existsUnique_comp_eq_of_range_subset_of_isReduced.solution
