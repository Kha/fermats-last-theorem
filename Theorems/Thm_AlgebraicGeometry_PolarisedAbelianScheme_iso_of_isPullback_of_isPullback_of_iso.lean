import Definitions.Def_AlgebraicGeometry_PolarisedAbelianScheme
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_PolarisedAbelianScheme_iso_of_isPullback_of_isPullback_of_iso

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian AlgebraicGeometry.PolarisedAbelianScheme

universe u

theorem AlgebraicGeometry.PolarisedAbelianScheme.iso_of_isPullback_of_isPullback_of_iso {g d n : ℕ}
    {S S' : Type u} [CommRing S] [CommRing S'] (φ : S →+* S')
    {u₁ u₂ : PolarisedAbelianScheme g d n S} {u₁' u₂' : PolarisedAbelianScheme g d n S'}
    (h₁ : PolarisedAbelianScheme.IsPullback φ u₁ u₁') (h₂ : PolarisedAbelianScheme.IsPullback φ u₂ u₂')
    (h : PolarisedAbelianScheme.Iso u₁ u₂) : PolarisedAbelianScheme.Iso u₁' u₂' := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_PolarisedAbelianScheme_iso_of_isPullback_of_isPullback_of_iso.solution
