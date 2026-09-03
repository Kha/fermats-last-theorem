import Definitions.Def_WeierstrassCurve_ProjModel
import Mathlib.AlgebraicGeometry.Geometrically.Integral
import P2M.Util
import P2M.Sol.S_WeierstrassProjModel_kw_hgi_geometricallyIntegral_of_baseChangeIso
attribute [-instance] WeierstrassProjModel.quotGradingSubmoduleDegreeZeroFiniteType WeierstrassProjModel.kw_lrChart_tensorCommRing WeierstrassProjModel.kw_lrChart_biGrading_gradedAlgebra WeierstrassProjModel.projModel_isIso_spec_mapCR WeierstrassProjModel.kw_lrSymOC_isDomain_ℬ₀ WeierstrassProjModel.isProper_projModelStrCR WeierstrassProjModel.homogeneousSubmoduleDegreeZeroFiniteType
attribute [-simp] WeierstrassProjModel.kw_lrAdd_substHom_X WeierstrassProjModel.kw_lrSym_substHom_X

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra WeierstrassProjModel

theorem WeierstrassProjModel.kw_hgi_geometricallyIntegral_of_baseChangeIso.{u} {R : Type u}
    [CommRing R] (W : WeierstrassCurve R)
    (hbc : ∀ (K : Type u) [Field K] [Algebra R K],
      Nonempty (pullback (projModelStrCR W.toProjective)
          (Spec.map (CommRingCat.ofHom (algebraMap R K)))
        ≅ projModelCR (W.toProjective.baseChange K))) :
    GeometricallyIntegral (projModelStrCR W.toProjective) := by p2m_exact_reverting @_root_.P2MW.S_WeierstrassProjModel_kw_hgi_geometricallyIntegral_of_baseChangeIso.solution
