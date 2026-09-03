import Definitions.Def_WeierstrassCurve_ProjModel
import P2M.Util
import P2M.Sol.S_WeierstrassProjModel_mul_comm_of_isPointsEval
attribute [-instance] WeierstrassProjModel.quotGradingSubmoduleDegreeZeroFiniteType WeierstrassProjModel.kw_lrChart_tensorCommRing WeierstrassProjModel.kw_lrChart_biGrading_gradedAlgebra WeierstrassProjModel.projModel_isIso_spec_mapCR WeierstrassProjModel.kw_lrSymOC_isDomain_ℬ₀ WeierstrassProjModel.isProper_projModelStrCR WeierstrassProjModel.homogeneousSubmoduleDegreeZeroFiniteType
attribute [-simp] WeierstrassProjModel.kw_lrAdd_substHom_X WeierstrassProjModel.kw_lrSym_substHom_X

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra WeierstrassProjModel

theorem WeierstrassProjModel.mul_comm_of_isPointsEval
    (K : Type) [Field K] (W : WeierstrassCurve K) [W.IsElliptic]
    (G : RelativeGroupLaw K (projModelStrCR W.toProjective))
    (ev : ∀ (F : Type) [Field F] [DecidableEq F] [Algebra K F],
      SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap K F)))
          (projModelStrCR W.toProjective) ≃
        (W.toProjective.baseChange F).toAffine.Point)
    (hev : IsPointsEval W.toProjective G ev)
    {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of K))
    (x y : SchemeHomOver t (projModelStrCR W.toProjective)) :
    G.mul t x y = G.mul t y x := by p2m_exact_reverting @_root_.P2MW.S_WeierstrassProjModel_mul_comm_of_isPointsEval.solution
