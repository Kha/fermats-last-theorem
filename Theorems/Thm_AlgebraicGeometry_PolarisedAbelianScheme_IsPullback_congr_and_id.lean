import Definitions.Def_AlgebraicGeometry_PolarisedAbelianScheme
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_PolarisedAbelianScheme_IsPullback_congr_and_id

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian
open scoped TensorProduct

theorem AlgebraicGeometry.PolarisedAbelianScheme.IsPullback.congr_and_id
    {g d n : ℕ} {S S' : Type} [CommRing S] [CommRing S'] :
    (∀ (φ ψ : S →+* S') (u : PolarisedAbelianScheme g d n S) (v : PolarisedAbelianScheme g d n S'),
      φ = ψ → PolarisedAbelianScheme.IsPullback φ u v → PolarisedAbelianScheme.IsPullback ψ u v) ∧
    (∀ u : PolarisedAbelianScheme g d n S, PolarisedAbelianScheme.IsPullback (RingHom.id S) u u) := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_PolarisedAbelianScheme_IsPullback_congr_and_id.solution
