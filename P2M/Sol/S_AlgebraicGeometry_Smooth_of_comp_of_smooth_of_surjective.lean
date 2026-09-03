import Mathlib
import Theorems.Thm_AlgebraicGeometry_LocallyOfFinitePresentation_of_comp_of_flat_of_surjective
import Theorems.Thm_AlgebraicGeometry_Smooth_of_comp_of_smooth_of_surjective_of_locallyOfFinitePresentation
import P2M.Util
namespace P2MW.S_AlgebraicGeometry_Smooth_of_comp_of_smooth_of_surjective

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

theorem solution
    {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) [Smooth f] [Surjective f] [QuasiCompact f]
    [Smooth (f ≫ g)] : Smooth g := by
  haveI : LocallyOfFinitePresentation g :=
    AlgebraicGeometry.LocallyOfFinitePresentation.of_comp_of_flat_of_surjective f g
  exact AlgebraicGeometry.Smooth.of_comp_of_smooth_of_surjective_of_locallyOfFinitePresentation f g

#print axioms solution
