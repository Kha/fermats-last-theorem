import Definitions.Def_AlgebraicGeometry_PolarisationRosati
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_Polarisation_LocIsoOnBase_pullback_of_isPullback

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry NeronModelInfra GoodReductionJacobian
  AlgebraicGeometry.Polarisation

universe u

theorem AlgebraicGeometry.Polarisation.LocIsoOnBase.pullback_of_isPullback
    {S S' : Type u} [CommRing S] [CommRing S'] (φ : S →+* S')
    {A A' : Scheme.{u}} {f : A ⟶ Spec (CommRingCat.of S)} {f' : A' ⟶ Spec (CommRingCat.of S')} {g : A' ⟶ A}
    (hg : IsPullback g f' f (Spec.map (CommRingCat.ofHom φ)))
    {M M' : A.Modules} (h : LocIsoOnBase f M M') :
    LocIsoOnBase f' ((Scheme.Modules.pullback g).obj M) ((Scheme.Modules.pullback g).obj M') := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_Polarisation_LocIsoOnBase_pullback_of_isPullback.solution
