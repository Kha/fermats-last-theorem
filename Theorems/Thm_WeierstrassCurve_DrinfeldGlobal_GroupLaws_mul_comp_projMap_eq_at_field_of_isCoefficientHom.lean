import Definitions.Def_WeierstrassCurve_ProjModel
import Definitions.Def_WeierstrassCurve_DrinfeldBasisGlobal
import Definitions.Def_WeierstrassCurve_DrinfeldTransportPin
import Definitions.Def_WeierstrassCurve_SectionAtOrigin
import Definitions.Def_WeierstrassCurve_DrinfeldLevelFunctor
import P2M.Util
import P2M.Sol.S_WeierstrassCurve_DrinfeldGlobal_GroupLaws_mul_comp_projMap_eq_at_field_of_isCoefficientHom
attribute [-instance] WeierstrassProjModel.quotGradingSubmoduleDegreeZeroFiniteType WeierstrassProjModel.kw_lrChart_tensorCommRing WeierstrassProjModel.kw_lrChart_biGrading_gradedAlgebra WeierstrassProjModel.projModel_isIso_spec_mapCR WeierstrassProjModel.kw_lrSymOC_isDomain_ℬ₀ WeierstrassProjModel.isProper_projModelStrCR WeierstrassProjModel.homogeneousSubmoduleDegreeZeroFiniteType
attribute [-simp] WeierstrassProjModel.kw_lrAdd_substHom_X WeierstrassProjModel.kw_lrSym_substHom_X GoodReductionJacobian.schemeHomOverComp_coe NeronModelInfra.schemeHomOverEquivOverHom_apply GoodReductionJacobian.RelativeGroupLaw.mk.sizeOf_spec NeronModelInfra.schemeHomOverEquivOverHom_symm_apply NeronModelInfra.overHomToSchemeHomOver_coe GoodReductionJacobian.RelativeGroupLaw.mk.injEq NeronModelInfra.overHomToSchemeHomOver_schemeHomOverToOverHom NeronModelInfra.schemeHomOverToOverHom_left NeronModelInfra.schemeHomOverToOverHom_overHomToSchemeHomOver GoodReductionJacobian.relativeGroupLawOfGrpObj_inv GoodReductionJacobian.relativeGroupLawOfGrpObj_mul GoodReductionJacobian.overHomEquivSchemeHomOver_apply_coe GoodReductionJacobian.relativeGroupLawOfGrpObj_one GoodReductionJacobian.overHomEquivSchemeHomOver_symm_apply_left

set_option autoImplicit false

universe u

open AlgebraicGeometry CategoryTheory WeierstrassProjModel WeierstrassCurve.DrinfeldGlobal NeronModelInfra

theorem WeierstrassCurve.DrinfeldGlobal.GroupLaws.mul_comp_projMap_eq_at_field_of_isCoefficientHom
    (A : Type u) [CommRing A] (𝒢 : GroupLaws A) (h𝒢 : 𝒢.IsChordTangent) (h𝒢O : 𝒢.IsOriginIdentity)
    (T : Type u) [CommRing T] [Algebra A T] (K : Type u) [Field K] [Algebra A K] (f : T →ₐ[A] K)
    (W : WeierstrassCurve T) (hΔ : IsUnit W.Δ) (hΔ' : IsUnit (W.map f.toRingHom).Δ)
    (φ : projModelGradingCR W →+*ᵍ projModelGradingCR (W.map f.toRingHom))
    (hφ : HomogeneousIdeal.irrelevant (projModelGradingCR (W.map f.toRingHom)) ≤
      (HomogeneousIdeal.irrelevant (projModelGradingCR W)).map φ)
    (hφc : IsCoefficientHom W f.toRingHom φ)
    (F : Type u) [Field F] [Algebra K F]
    (x y : SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap K F))) (projModelStrCR (W.map f.toRingHom)))
    (x' y' : SchemeHomOver
      (Spec.map (CommRingCat.ofHom (algebraMap K F)) ≫ Spec.map (CommRingCat.ofHom f.toRingHom)) (projModelStrCR W))
    (hx : x'.1 = x.1 ≫ Proj.map φ hφ) (hy : y'.1 = y.1 ≫ Proj.map φ hφ) :
    ((𝒢 K (W.map f.toRingHom) hΔ').mul (Spec.map (CommRingCat.ofHom (algebraMap K F))) x y).1 ≫ Proj.map φ hφ =
      ((𝒢 T W hΔ).mul
        (Spec.map (CommRingCat.ofHom (algebraMap K F)) ≫ Spec.map (CommRingCat.ofHom f.toRingHom)) x' y').1 := by p2m_exact_reverting @_root_.P2MW.S_WeierstrassCurve_DrinfeldGlobal_GroupLaws_mul_comp_projMap_eq_at_field_of_isCoefficientHom.solution
