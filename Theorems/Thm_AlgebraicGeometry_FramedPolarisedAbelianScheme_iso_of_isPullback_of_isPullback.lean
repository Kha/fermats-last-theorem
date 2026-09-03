import Definitions.Def_AlgebraicGeometry_FramedPolarisedAbelianScheme
import Definitions.Def_AlgebraicGeometry_ProjSpace
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_FramedPolarisedAbelianScheme_iso_of_isPullback_of_isPullback

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian

attribute [local instance] MvPolynomial.gradedAlgebra

theorem AlgebraicGeometry.FramedPolarisedAbelianScheme.iso_of_isPullback_of_isPullback
    {g N n : ℕ} {S S' : Type} [CommRing S] [CommRing S'] (φ : S →+* S')
    (X : FramedPolarisedAbelianScheme g N n S) (Y Y' : FramedPolarisedAbelianScheme g N n S')
    (h : FramedPolarisedAbelianScheme.IsPullback φ X Y) (h' : FramedPolarisedAbelianScheme.IsPullback φ X Y') :
    FramedPolarisedAbelianScheme.Iso Y Y' := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_FramedPolarisedAbelianScheme_iso_of_isPullback_of_isPullback.solution
