import Mathlib
import Definitions.Def_AlgebraicGeometry_PolarisationRosati
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_Polarisation_nonempty_iso_of_locIsoOnBase_of_isLocalRing

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Polarisation

universe u

theorem AlgebraicGeometry.Polarisation.nonempty_iso_of_locIsoOnBase_of_isLocalRing
    {S : Type u} [CommRing S] [IsLocalRing S] {X : Scheme.{u}} (g : X ⟶ Spec (CommRingCat.of S))
    (M M' : X.Modules) (h : LocIsoOnBase g M M') :
    Nonempty (M ≅ M') := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_Polarisation_nonempty_iso_of_locIsoOnBase_of_isLocalRing.solution
