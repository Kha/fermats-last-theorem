import Definitions.Def_WeierstrassCurve_ProjModel
import P2M.Util
import P2M.Sol.S_WeierstrassProjModel_isProper_and_isIntegral_and_isReduced_selfPullback_pullback_snd_of_baseChangeIso
attribute [-instance] WeierstrassProjModel.quotGradingSubmoduleDegreeZeroFiniteType WeierstrassProjModel.kw_lrChart_tensorCommRing WeierstrassProjModel.kw_lrChart_biGrading_gradedAlgebra WeierstrassProjModel.projModel_isIso_spec_mapCR WeierstrassProjModel.kw_lrSymOC_isDomain_ℬ₀ WeierstrassProjModel.isProper_projModelStrCR WeierstrassProjModel.homogeneousSubmoduleDegreeZeroFiniteType
attribute [-simp] WeierstrassProjModel.kw_lrAdd_substHom_X WeierstrassProjModel.kw_lrSym_substHom_X

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits NeronModelInfra WeierstrassProjModel

universe u
theorem WeierstrassProjModel.isProper_and_isIntegral_and_isReduced_selfPullback_pullback_snd_of_baseChangeIso
    {R : Type u} [CommRing R] (V : WeierstrassCurve.Projective R) [V.toAffine.IsElliptic]
    (F : Type u) [Field F] [Algebra R F]
    (hbc : Nonempty (pullback (projModelStrCR V)
            (Spec.map (CommRingCat.ofHom (algebraMap R F)))
          ≅ projModelCR (V.baseChange F))) :
    IsProper (pullback.snd (projModelStrCR V)
        (Spec.map (CommRingCat.ofHom (algebraMap R F))))
    ∧ IsIntegral ↑(pullback (projModelStrCR V)
        (Spec.map (CommRingCat.ofHom (algebraMap R F))))
    ∧ IsReduced ↑(pullback
        (pullback.snd (projModelStrCR V) (Spec.map (CommRingCat.ofHom (algebraMap R F))))
        (pullback.snd (projModelStrCR V) (Spec.map (CommRingCat.ofHom (algebraMap R F))))) := by p2m_exact_reverting @_root_.P2MW.S_WeierstrassProjModel_isProper_and_isIntegral_and_isReduced_selfPullback_pullback_snd_of_baseChangeIso.solution
