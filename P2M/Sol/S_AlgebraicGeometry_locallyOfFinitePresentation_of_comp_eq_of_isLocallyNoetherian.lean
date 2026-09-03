import Mathlib
import P2M.Util
namespace P2MW.S_AlgebraicGeometry_locallyOfFinitePresentation_of_comp_eq_of_isLocallyNoetherian

set_option maxHeartbeats 1600000

open AlgebraicGeometry CategoryTheory

universe u

theorem solution
    {X Y S : Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ S) (h : X ⟶ Y) (w : h ≫ g = f)
    [LocallyOfFiniteType f] [LocallyOfFiniteType g] [IsLocallyNoetherian S] :
    LocallyOfFinitePresentation h := by
  haveI : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian g
  haveI : LocallyOfFiniteType (h ≫ g) := by rw [w]; infer_instance
  haveI : LocallyOfFiniteType h := locallyOfFiniteType_of_comp h g
  infer_instance
