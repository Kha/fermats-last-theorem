import Definitions.Def_FormalGroup_NSeries
import Definitions.Def_WeierstrassCurve_FormalGroupLaw
import Definitions.Def_WeierstrassCurve_ProjModel
import Definitions.Def_WeierstrassCurve_DrinfeldBasisGlobal
import Definitions.Def_WeierstrassCurve_SectionAtOrigin
import Definitions.Def_WeierstrassCurve_DrinfeldLevelFunctor
import P2M.Util
import P2M.Sol.S_WeierstrassProjModel_exists_ne_forall_exists_eq_specMap_map_smul_comp_of_specMap_fstHom_comp_eq
attribute [-instance] WeierstrassProjModel.quotGradingSubmoduleDegreeZeroFiniteType WeierstrassProjModel.kw_lrChart_tensorCommRing WeierstrassProjModel.kw_lrChart_biGrading_gradedAlgebra WeierstrassProjModel.projModel_isIso_spec_mapCR WeierstrassProjModel.kw_lrSymOC_isDomain_ℬ₀ WeierstrassProjModel.isProper_projModelStrCR WeierstrassProjModel.homogeneousSubmoduleDegreeZeroFiniteType
attribute [-simp] WeierstrassProjModel.kw_lrAdd_substHom_X WeierstrassProjModel.kw_lrSym_substHom_X

set_option autoImplicit false
open AlgebraicGeometry CategoryTheory NeronModelInfra WeierstrassProjModel WeierstrassCurve.DrinfeldGlobal IsLocalRing FormalGroup
attribute [local instance] MvPolynomial.gradedAlgebra

theorem WeierstrassProjModel.exists_ne_forall_exists_eq_specMap_map_smul_comp_of_specMap_fstHom_comp_eq
    (B : Type) [CommRing B] (V : WeierstrassCurve B) (hΔ : IsUnit V.Δ) (k : Type) [Field k] (f : B →+* k)
    (Q₀ : SchemeHomOver (Spec.map (CommRingCat.ofHom f)) (projModelStrCR V)) :
    ∃ Q₁ : SchemeHomOver (Spec.map (CommRingCat.ofHom ((algebraMap k (DualNumber k)).comp f))) (projModelStrCR V),
      Spec.map (CommRingCat.ofHom (TrivSqZeroExt.fstHom k k k).toRingHom) ≫ Q₁.1 = Q₀.1 ∧
      Q₁.1 ≠ Spec.map (CommRingCat.ofHom (algebraMap k (DualNumber k))) ≫ Q₀.1 ∧
      ∀ Q : SchemeHomOver (Spec.map (CommRingCat.ofHom ((algebraMap k (DualNumber k)).comp f))) (projModelStrCR V),
        Spec.map (CommRingCat.ofHom (TrivSqZeroExt.fstHom k k k).toRingHom) ≫ Q.1 = Q₀.1 →
        ∃ c : k, Q.1 = Spec.map (CommRingCat.ofHom
          (TrivSqZeroExt.map (c • (LinearMap.id : k →ₗ[k] k))).toRingHom) ≫ Q₁.1 := by p2m_exact_reverting @_root_.P2MW.S_WeierstrassProjModel_exists_ne_forall_exists_eq_specMap_map_smul_comp_of_specMap_fstHom_comp_eq.solution
