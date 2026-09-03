import Mathlib
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_isClosedImmersion_of_universallyClosed_of_universallyInjective_of_formallyUnramified

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

theorem AlgebraicGeometry.isClosedImmersion_of_universallyClosed_of_universallyInjective_of_formallyUnramified
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    [UniversallyClosed f] [UniversallyInjective f] [LocallyOfFiniteType f] [FormallyUnramified f] :
    IsClosedImmersion f := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_isClosedImmersion_of_universallyClosed_of_universallyInjective_of_formallyUnramified.solution
