import Definitions.Def_AlgebraicGeometry_ThetaAdaptedFrame
import Definitions.Def_AlgebraicGeometry_ProjSpace
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_PolarisedAbelianScheme_thetaTypeLocally_of_isPullback_of_faithfullyFlat_etale

set_option autoImplicit false

attribute [local instance] MvPolynomial.gradedAlgebra

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian AlgebraicGeometry.Polarisation
open scoped BigOperators TensorProduct

theorem AlgebraicGeometry.PolarisedAbelianScheme.thetaTypeLocally_of_isPullback_of_faithfullyFlat_etale
    {g N n : ℕ} (δ : Fin g → ℕ) [hδ : ∀ i, NeZero (δ i)]
    {S : Type} [CommRing S] (S' : Type) [CommRing S'] [Algebra S S'] [Module.FaithfullyFlat S S'] [Algebra.Etale S S']
    (u : PolarisedAbelianScheme g (N + 1) n S) (u' : PolarisedAbelianScheme g (N + 1) n S')
    (h : PolarisedAbelianScheme.IsPullback (algebraMap S S') u u') (hu' : PolarisedAbelianScheme.ThetaTypeLocally δ S' u') :
    PolarisedAbelianScheme.ThetaTypeLocally δ S u := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_PolarisedAbelianScheme_thetaTypeLocally_of_isPullback_of_faithfullyFlat_etale.solution
