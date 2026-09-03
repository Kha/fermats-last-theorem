import Definitions.Def_AlgebraicGeometry_FramedPolarisedAbelianScheme
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_FramedPolarisedAbelianScheme_nonempty_of_subsingleton

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian

theorem AlgebraicGeometry.FramedPolarisedAbelianScheme.nonempty_of_subsingleton
    (g N n : ℕ) (S : Type) [CommRing S] [Subsingleton S] :
    Nonempty (FramedPolarisedAbelianScheme g N n S) := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_FramedPolarisedAbelianScheme_nonempty_of_subsingleton.solution
