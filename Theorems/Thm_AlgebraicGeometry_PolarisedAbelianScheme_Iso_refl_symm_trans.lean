import Definitions.Def_AlgebraicGeometry_PolarisedAbelianScheme
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_PolarisedAbelianScheme_Iso_refl_symm_trans

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian
open scoped TensorProduct

theorem AlgebraicGeometry.PolarisedAbelianScheme.Iso.refl_symm_trans
    {g d n : ℕ} {S : Type} [CommRing S] :
    (∀ u : PolarisedAbelianScheme g d n S, PolarisedAbelianScheme.Iso u u) ∧
    (∀ u v : PolarisedAbelianScheme g d n S, PolarisedAbelianScheme.Iso u v → PolarisedAbelianScheme.Iso v u) ∧
    (∀ u v w : PolarisedAbelianScheme g d n S,
      PolarisedAbelianScheme.Iso u v → PolarisedAbelianScheme.Iso v w → PolarisedAbelianScheme.Iso u w) := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_PolarisedAbelianScheme_Iso_refl_symm_trans.solution
