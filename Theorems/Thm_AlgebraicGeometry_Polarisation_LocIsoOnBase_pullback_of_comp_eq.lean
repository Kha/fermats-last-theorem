import Definitions.Def_AlgebraicGeometry_PolarisationRosati
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_Polarisation_LocIsoOnBase_pullback_of_comp_eq

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Polarisation

universe u

theorem AlgebraicGeometry.Polarisation.LocIsoOnBase.pullback_of_comp_eq
    {S S' : Type u} [CommRing S] [CommRing S'] {X Y : Scheme.{u}}
    {g : X ⟶ Spec (CommRingCat.of S)} (g' : Y ⟶ Spec (CommRingCat.of S')) (h : Y ⟶ X)
    (φ : Spec (CommRingCat.of S') ⟶ Spec (CommRingCat.of S)) (comm : h ≫ g = g' ≫ φ)
    {M M' : X.Modules} (hM : LocIsoOnBase g M M') :
    LocIsoOnBase g' ((Scheme.Modules.pullback h).obj M) ((Scheme.Modules.pullback h).obj M') := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_Polarisation_LocIsoOnBase_pullback_of_comp_eq.solution
