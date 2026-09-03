import Definitions.Def_AlgebraicGeometry_PolarisationRosati
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_Polarisation_LocIsoOnBase_equivalence

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Polarisation

universe u

theorem AlgebraicGeometry.Polarisation.LocIsoOnBase.equivalence
    {S : Type u} [CommRing S] {X : Scheme.{u}} (g : X ⟶ Spec (CommRingCat.of S)) :
    Equivalence (LocIsoOnBase g) := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_Polarisation_LocIsoOnBase_equivalence.solution
