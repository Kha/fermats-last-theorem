import Mathlib
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_isOpenImmersion_of_etale_of_universallyInjective

set_option autoImplicit false

universe u

open CategoryTheory AlgebraicGeometry

theorem AlgebraicGeometry.isOpenImmersion_of_etale_of_universallyInjective
    {X Y : Scheme.{u}} (f : X ⟶ Y) [Etale f] [UniversallyInjective f] :
    IsOpenImmersion f := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_isOpenImmersion_of_etale_of_universallyInjective.solution
