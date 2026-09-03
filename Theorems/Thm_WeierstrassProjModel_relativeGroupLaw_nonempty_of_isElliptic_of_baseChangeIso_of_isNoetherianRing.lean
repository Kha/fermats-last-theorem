import Definitions.Def_WeierstrassCurve_ProjModel
import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point
import Mathlib.RingTheory.Noetherian.Defs
import P2M.Util
import P2M.Sol.S_WeierstrassProjModel_relativeGroupLaw_nonempty_of_isElliptic_of_baseChangeIso_of_isNoetherianRing
attribute [-instance] WeierstrassProjModel.quotGradingSubmoduleDegreeZeroFiniteType WeierstrassProjModel.kw_lrChart_tensorCommRing WeierstrassProjModel.kw_lrChart_biGrading_gradedAlgebra WeierstrassProjModel.projModel_isIso_spec_mapCR WeierstrassProjModel.kw_lrSymOC_isDomain_ℬ₀ WeierstrassProjModel.isProper_projModelStrCR WeierstrassProjModel.homogeneousSubmoduleDegreeZeroFiniteType
attribute [-simp] WeierstrassProjModel.kw_lrAdd_substHom_X WeierstrassProjModel.kw_lrSym_substHom_X WeierstrassProjModel.kw_lrThird_substHom_X

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits NeronModelInfra WeierstrassProjModel

universe u
theorem WeierstrassProjModel.relativeGroupLaw_nonempty_of_isElliptic_of_baseChangeIso_of_isNoetherianRing
    {R : Type u} [CommRing R] [IsDomain R] [IsNoetherianRing R]
    (V : WeierstrassCurve.Projective R)
    [V.toAffine.IsElliptic]
    (hbc : ∀ (K : Type u) [Field K] [Algebra R K],
        Nonempty (pullback (projModelStrCR V)
            (Spec.map (CommRingCat.ofHom (algebraMap R K)))
          ≅ projModelCR (V.baseChange K))) :
    Nonempty (RelativeGroupLaw R (projModelStrCR V)) := by p2m_exact_reverting @_root_.P2MW.S_WeierstrassProjModel_relativeGroupLaw_nonempty_of_isElliptic_of_baseChangeIso_of_isNoetherianRing.solution
