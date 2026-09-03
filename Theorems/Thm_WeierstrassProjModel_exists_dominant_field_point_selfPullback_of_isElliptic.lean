import Mathlib
import Definitions.Def_WeierstrassCurve_ProjModel
import P2M.Util
import P2M.Sol.S_WeierstrassProjModel_exists_dominant_field_point_selfPullback_of_isElliptic
attribute [-instance] WeierstrassProjModel.quotGradingSubmoduleDegreeZeroFiniteType WeierstrassProjModel.kw_lrChart_tensorCommRing WeierstrassProjModel.kw_lrChart_biGrading_gradedAlgebra WeierstrassProjModel.projModel_isIso_spec_mapCR WeierstrassProjModel.kw_lrSymOC_isDomain_ℬ₀ WeierstrassProjModel.isProper_projModelStrCR WeierstrassProjModel.homogeneousSubmoduleDegreeZeroFiniteType
attribute [-simp] WeierstrassProjModel.kw_lrAdd_substHom_X WeierstrassProjModel.kw_lrSym_substHom_X

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits NeronModelInfra WeierstrassProjModel

theorem WeierstrassProjModel.exists_dominant_field_point_selfPullback_of_isElliptic
    (K : Type) [Field K] (W : WeierstrassCurve K) [W.IsElliptic] :
    let π := projModelStrCR W.toProjective
    ∃ (F : Type) (_ : Field F) (_ : Algebra K F)
      (ι : Spec (CommRingCat.of F) ⟶ pullback π π),
      IsSchemeTheoreticallyDominant ι ∧
      ι ≫ pullback.fst π π ≫ π = Spec.map (CommRingCat.ofHom (algebraMap K F)) := by p2m_exact_reverting @_root_.P2MW.S_WeierstrassProjModel_exists_dominant_field_point_selfPullback_of_isElliptic.solution
