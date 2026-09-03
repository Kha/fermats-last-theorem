import Definitions.Def_WeierstrassCurve_ProjModel
import P2M.Util
import P2M.Sol.S_WeierstrassProjModel_projModel_isPullback_baseChange
attribute [-instance] WeierstrassProjModel.quotGradingSubmoduleDegreeZeroFiniteType WeierstrassProjModel.kw_lrChart_tensorCommRing WeierstrassProjModel.kw_lrChart_biGrading_gradedAlgebra WeierstrassProjModel.projModel_isIso_spec_mapCR WeierstrassProjModel.kw_lrSymOC_isDomain_ℬ₀ WeierstrassProjModel.isProper_projModelStrCR WeierstrassProjModel.homogeneousSubmoduleDegreeZeroFiniteType
attribute [-simp] WeierstrassProjModel.kw_lrAdd_substHom_X WeierstrassProjModel.kw_lrSym_substHom_X

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits NeronModelInfra WeierstrassProjModel

universe u
theorem WeierstrassProjModel.projModel_isPullback_baseChange
    {R : Type u} [CommRing R] (V : WeierstrassCurve.Projective R)
    (K : Type u) [Field K] [Algebra R K] :
    ∃ (α : projModelCR (V.baseChange K) ⟶ projModelCR V),
      IsPullback α (projModelStrCR (V.baseChange K)) (projModelStrCR V)
        (Spec.map (CommRingCat.ofHom (algebraMap R K))) := by p2m_exact_reverting @_root_.P2MW.S_WeierstrassProjModel_projModel_isPullback_baseChange.solution
