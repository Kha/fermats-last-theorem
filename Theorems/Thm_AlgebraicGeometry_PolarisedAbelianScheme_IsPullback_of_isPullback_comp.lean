import Definitions.Def_AlgebraicGeometry_PolarisedAbelianScheme
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_PolarisedAbelianScheme_IsPullback_of_isPullback_comp

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian
open scoped TensorProduct

theorem AlgebraicGeometry.PolarisedAbelianScheme.IsPullback.of_isPullback_comp
    {g d n : ℕ} {S S' S'' : Type} [CommRing S] [CommRing S'] [CommRing S''] (φ : S →+* S') (ψ : S' →+* S'')
    (u : PolarisedAbelianScheme g d n S) (v : PolarisedAbelianScheme g d n S') (w : PolarisedAbelianScheme g d n S'')
    (h : PolarisedAbelianScheme.IsPullback (ψ.comp φ) u w) (h₁ : PolarisedAbelianScheme.IsPullback φ u v) :
    PolarisedAbelianScheme.IsPullback ψ v w := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_PolarisedAbelianScheme_IsPullback_of_isPullback_comp.solution
