import Mathlib
import Definitions.Def_WeierstrassCurve_ProjModel
import Theorems.Thm_WeierstrassProjModel_kw_r0_isIntegral_pullbacks
import Theorems.Thm_WeierstrassProjModel_kw_hgi_geometricallyIntegral_of_baseChangeIso
import Theorems.Thm_WeierstrassProjModel_kw_bc_baseChangeIso
import Theorems.Thm_WeierstrassProjModel_projModelStrCR_smooth
import P2M.Util
namespace P2MW.S_WeierstrassProjModel_isIntegral_selfPullback_of_isElliptic_field
attribute [-instance] WeierstrassProjModel.quotGradingSubmoduleDegreeZeroFiniteType WeierstrassProjModel.kw_lrChart_tensorCommRing WeierstrassProjModel.kw_lrChart_biGrading_gradedAlgebra WeierstrassProjModel.projModel_isIso_spec_mapCR WeierstrassProjModel.kw_lrSymOC_isDomain_ℬ₀ WeierstrassProjModel.isProper_projModelStrCR WeierstrassProjModel.homogeneousSubmoduleDegreeZeroFiniteType
attribute [-simp] WeierstrassProjModel.kw_lrAdd_substHom_X WeierstrassProjModel.kw_lrSym_substHom_X

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits NeronModelInfra WeierstrassProjModel

set_option maxHeartbeats 12800000 in
theorem solution
    (K : Type) [Field K] (W : WeierstrassCurve K) [W.IsElliptic] :
    IsIntegral
      ↑(pullback (projModelStrCR W.toProjective) (projModelStrCR W.toProjective)) := by
  haveI : IsDomain K := inferInstance
  haveI : IsNoetherianRing K := by first | infer_instance | exact inferInstance
  haveI hell : W.toProjective.IsElliptic := by
    infer_instance
  have hsm : Smooth (projModelStrCR W.toProjective) := by
    exact projModelStrCR_smooth W.toProjective
  have hbc := kw_bc_baseChangeIso W
  have hgi : GeometricallyIntegral (projModelStrCR W.toProjective) := by
    exact kw_hgi_geometricallyIntegral_of_baseChangeIso W hbc
  exact (kw_r0_isIntegral_pullbacks W hsm hgi).2.1
