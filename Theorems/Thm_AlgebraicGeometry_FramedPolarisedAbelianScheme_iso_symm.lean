import Definitions.Def_AlgebraicGeometry_ThetaAdaptedFrame
import Definitions.Def_AlgebraicGeometry_ProjSpace
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_FramedPolarisedAbelianScheme_iso_symm

set_option autoImplicit false

attribute [local instance] MvPolynomial.gradedAlgebra

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian AlgebraicGeometry.Polarisation
open scoped BigOperators TensorProduct

theorem AlgebraicGeometry.FramedPolarisedAbelianScheme.iso_symm
    {g N n : ℕ} {S : Type} [CommRing S] (X X' : FramedPolarisedAbelianScheme g N n S)
    (h : FramedPolarisedAbelianScheme.Iso X X') : FramedPolarisedAbelianScheme.Iso X' X := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_FramedPolarisedAbelianScheme_iso_symm.solution
