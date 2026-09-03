import Definitions.Def_AlgebraicGeometry_PolarisedAbelianScheme
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_PolarisedAbelianScheme_iso_of_isPullback_of_isPullback

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian
open scoped TensorProduct

theorem AlgebraicGeometry.PolarisedAbelianScheme.iso_of_isPullback_of_isPullback
    {g d n : ℕ} {S S' : Type} [CommRing S] [CommRing S'] (φ : S →+* S')
    (u : PolarisedAbelianScheme g d n S) (v v' : PolarisedAbelianScheme g d n S')
    (h : PolarisedAbelianScheme.IsPullback φ u v) (h' : PolarisedAbelianScheme.IsPullback φ u v') :
    PolarisedAbelianScheme.Iso v v' := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_PolarisedAbelianScheme_iso_of_isPullback_of_isPullback.solution
