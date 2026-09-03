import Mathlib
import Definitions.Def_WeierstrassCurve_ProjModel
import P2M.Util
import P2M.Sol.S_WeierstrassProjModel_bijective_appTop_pullback_snd_projModelStrCR
attribute [-instance] WeierstrassProjModel.quotGradingSubmoduleDegreeZeroFiniteType WeierstrassProjModel.kw_lrChart_tensorCommRing WeierstrassProjModel.kw_lrChart_biGrading_gradedAlgebra WeierstrassProjModel.projModel_isIso_spec_mapCR WeierstrassProjModel.kw_lrSymOC_isDomain_ℬ₀ WeierstrassProjModel.isProper_projModelStrCR WeierstrassProjModel.homogeneousSubmoduleDegreeZeroFiniteType
attribute [-simp] WeierstrassProjModel.kw_lrAdd_substHom_X WeierstrassProjModel.kw_lrSym_substHom_X

set_option autoImplicit false

universe u

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits NeronModelInfra WeierstrassProjModel

attribute [local instance] MvPolynomial.gradedAlgebra

theorem WeierstrassProjModel.bijective_appTop_pullback_snd_projModelStrCR
    {R : Type u} [CommRing R] (V : WeierstrassCurve.Projective R) (S : Type u) [CommRing S] [Algebra R S] :
    Function.Bijective
      (pullback.snd (projModelStrCR V) (Spec.map (CommRingCat.ofHom (algebraMap R S)))).appTop := by p2m_exact_reverting @_root_.P2MW.S_WeierstrassProjModel_bijective_appTop_pullback_snd_projModelStrCR.solution
