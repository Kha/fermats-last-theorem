import Definitions.Def_AlgebraicGeometry_PolarisedAbelianScheme
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_PolarisedAbelianScheme_IsPullback_trans

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian
open scoped TensorProduct

theorem AlgebraicGeometry.PolarisedAbelianScheme.IsPullback.trans
    {g d n : ℕ} {S S' S'' : Type} [CommRing S] [CommRing S'] [CommRing S''] (φ : S →+* S') (ψ : S' →+* S'')
    (u : PolarisedAbelianScheme g d n S) (v : PolarisedAbelianScheme g d n S') (w : PolarisedAbelianScheme g d n S'')
    (h₁ : PolarisedAbelianScheme.IsPullback φ u v) (h₂ : PolarisedAbelianScheme.IsPullback ψ v w) :
    PolarisedAbelianScheme.IsPullback (ψ.comp φ) u w := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_PolarisedAbelianScheme_IsPullback_trans.solution
