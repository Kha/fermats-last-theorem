import Definitions.Def_AlgebraicGeometry_ThetaReframe
import Definitions.Def_AlgebraicGeometry_ProjSpace
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_FramedPolarisedAbelianScheme_IsReframe_isUnit

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian
open scoped BigOperators

attribute [local instance] MvPolynomial.gradedAlgebra

theorem AlgebraicGeometry.FramedPolarisedAbelianScheme.IsReframe.isUnit
    {g N n : ℕ} {S : Type} [CommRing S] {X X' : FramedPolarisedAbelianScheme g N n S}
    {U : Matrix (Fin (N + 1)) (Fin (N + 1)) S} (h : X.IsReframe U X') : IsUnit U := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_FramedPolarisedAbelianScheme_IsReframe_isUnit.solution
