import Mathlib
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_FormallyUnramified_eq_of_comp_eq_of_surjective_of_locallyOfFiniteType

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry

universe u

theorem AlgebraicGeometry.FormallyUnramified.eq_of_comp_eq_of_surjective_of_locallyOfFiniteType
    {X Y T T₀ : Scheme.{u}} (f : X ⟶ Y) [FormallyUnramified f] [LocallyOfFiniteType f]
    (j : T₀ ⟶ T) [Surjective j] (u u' : T ⟶ X) (hf : u ≫ f = u' ≫ f) (hj : j ≫ u = j ≫ u') :
    u = u' := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_FormallyUnramified_eq_of_comp_eq_of_surjective_of_locallyOfFiniteType.solution
