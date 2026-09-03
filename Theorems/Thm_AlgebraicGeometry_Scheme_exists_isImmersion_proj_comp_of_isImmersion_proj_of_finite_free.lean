import Mathlib
import Definitions.Def_AlgebraicGeometry_ThetaAdaptedFrame
import Definitions.Def_AlgebraicGeometry_ProjSpace
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_Scheme_exists_isImmersion_proj_comp_of_isImmersion_proj_of_finite_free

set_option autoImplicit false

attribute [local instance] MvPolynomial.gradedAlgebra

open CategoryTheory CategoryTheory.Limits open AlgebraicGeometry hiding exists_isClosedImmersion_projSpace_pullback_of_isClosedImmersion open NeronModelInfra GoodReductionJacobian AlgebraicGeometry.Polarisation
open scoped BigOperators TensorProduct

theorem AlgebraicGeometry.Scheme.exists_isImmersion_proj_comp_of_isImmersion_proj_of_finite_free
    (S : Type) [CommRing S] (S' : Type) [CommRing S'] [Algebra S S'] [Module.Finite S S'] [Module.Free S S']
    (X : Scheme.{0}) (πX : X ⟶ Spec (CommRingCat.of S'))
    (hQP : ∃ (qpa : ℕ) (qpι : X ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (qpa + 1)) S')),
      IsImmersion qpι ∧ qpι ≫ ProjSpace.π S' qpa = πX) :
    ∃ (qpn : ℕ) (qpι : X ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (qpn + 1)) S)),
      IsImmersion qpι ∧ qpι ≫ ProjSpace.π S qpn = πX ≫ Spec.map (CommRingCat.ofHom (algebraMap S S')) := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_Scheme_exists_isImmersion_proj_comp_of_isImmersion_proj_of_finite_free.solution
