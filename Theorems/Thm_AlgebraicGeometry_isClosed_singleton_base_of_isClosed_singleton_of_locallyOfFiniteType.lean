import Mathlib
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_isClosed_singleton_base_of_isClosed_singleton_of_locallyOfFiniteType

set_option autoImplicit false

universe u

open CategoryTheory AlgebraicGeometry

theorem AlgebraicGeometry.isClosed_singleton_base_of_isClosed_singleton_of_locallyOfFiniteType
    {X Y S : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ S) [LocallyOfFiniteType f] [LocallyOfFiniteType g]
    {x : X} (hx : IsClosed ({x} : Set X)) (hs : IsClosed ({(f ≫ g).base x} : Set S)) :
    IsClosed ({f.base x} : Set Y) := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_isClosed_singleton_base_of_isClosed_singleton_of_locallyOfFiniteType.solution
