import Definitions.Def_AlgebraicGeometry_PolarisedAbelianScheme
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_PolarisedAbelianScheme_Iso_baseChange

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian
open scoped TensorProduct

theorem AlgebraicGeometry.PolarisedAbelianScheme.Iso.baseChange
    {g d n : ℕ} {S S' : Type} [CommRing S] [CommRing S'] (φ : S →+* S')
    (u₁ u₂ : PolarisedAbelianScheme g d n S) (v₁ v₂ : PolarisedAbelianScheme g d n S')
    (h : PolarisedAbelianScheme.Iso u₁ u₂)
    (h₁ : PolarisedAbelianScheme.IsPullback φ u₁ v₁) (h₂ : PolarisedAbelianScheme.IsPullback φ u₂ v₂) :
    PolarisedAbelianScheme.Iso v₁ v₂ := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_PolarisedAbelianScheme_Iso_baseChange.solution
