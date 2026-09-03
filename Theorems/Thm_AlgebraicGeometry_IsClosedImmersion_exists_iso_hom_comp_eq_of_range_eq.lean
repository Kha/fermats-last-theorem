import Mathlib
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_IsClosedImmersion_exists_iso_hom_comp_eq_of_range_eq

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

theorem AlgebraicGeometry.IsClosedImmersion.exists_iso_hom_comp_eq_of_range_eq
    {A B X : Scheme.{u}} (f : A ⟶ X) (g : B ⟶ X) [IsClosedImmersion f] [IsClosedImmersion g]
    [IsReduced A] [IsReduced B] (h : Set.range f.base = Set.range g.base) :
    ∃ e : A ≅ B, e.hom ≫ g = f := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_IsClosedImmersion_exists_iso_hom_comp_eq_of_range_eq.solution
