import Definitions.Def_WeierstrassCurve_ProjModel
import Definitions.Def_WeierstrassCurve_DrinfeldBasisGlobal
import Definitions.Def_WeierstrassCurve_DrinfeldTransportPin
import Definitions.Def_WeierstrassCurve_SectionAtOrigin
import Definitions.Def_WeierstrassCurve_DrinfeldLevelFunctor
import P2M.Util
import P2M.Sol.S_WeierstrassCurve_DrinfeldGlobal_torsionIdeal_comap_fst_eq_torsionIdeal_comap_theta
attribute [-instance] WeierstrassProjModel.quotGradingSubmoduleDegreeZeroFiniteType WeierstrassProjModel.kw_lrChart_tensorCommRing WeierstrassProjModel.kw_lrChart_biGrading_gradedAlgebra WeierstrassProjModel.projModel_isIso_spec_mapCR WeierstrassProjModel.kw_lrSymOC_isDomain_ℬ₀ WeierstrassProjModel.isProper_projModelStrCR WeierstrassProjModel.homogeneousSubmoduleDegreeZeroFiniteType
attribute [-simp] WeierstrassProjModel.kw_lrAdd_substHom_X WeierstrassProjModel.kw_lrSym_substHom_X GoodReductionJacobian.schemeHomOverComp_coe NeronModelInfra.schemeHomOverEquivOverHom_apply GoodReductionJacobian.RelativeGroupLaw.mk.sizeOf_spec NeronModelInfra.schemeHomOverEquivOverHom_symm_apply NeronModelInfra.overHomToSchemeHomOver_coe GoodReductionJacobian.RelativeGroupLaw.mk.injEq NeronModelInfra.overHomToSchemeHomOver_schemeHomOverToOverHom NeronModelInfra.schemeHomOverToOverHom_left NeronModelInfra.schemeHomOverToOverHom_overHomToSchemeHomOver GoodReductionJacobian.relativeGroupLawOfGrpObj_inv GoodReductionJacobian.relativeGroupLawOfGrpObj_mul GoodReductionJacobian.overHomEquivSchemeHomOver_apply_coe GoodReductionJacobian.relativeGroupLawOfGrpObj_one GoodReductionJacobian.overHomEquivSchemeHomOver_symm_apply_left

set_option autoImplicit false

universe u

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits WeierstrassProjModel WeierstrassCurve.DrinfeldGlobal NeronModelInfra

theorem WeierstrassCurve.DrinfeldGlobal.torsionIdeal_comap_fst_eq_torsionIdeal_comap_theta
    (A : Type u) [CommRing A] (𝒢 : GroupLaws A) (h𝒢 : 𝒢.IsChordTangent) (h𝒢O : 𝒢.IsOriginIdentity)
    (T : Type u) [CommRing T] [Algebra A T] (K : Type u) [Field K] [Algebra A K] (ι : T →ₐ[A] K)
    (W₀ : WeierstrassCurve T) (hΔ₀ : IsUnit W₀.Δ) (hΔ' : IsUnit (W₀.map ι.toRingHom).Δ) (n : ℕ)
    (φ : projModelGradingCR W₀ →+*ᵍ projModelGradingCR (W₀.map ι.toRingHom))
    (hφ : HomogeneousIdeal.irrelevant (projModelGradingCR (W₀.map ι.toRingHom)) ≤
      (HomogeneousIdeal.irrelevant (projModelGradingCR W₀)).map φ)
    (hφc : IsCoefficientHom W₀ ι.toRingHom φ)
    (θ : pullback (pullback.snd (projModelStrCR W₀) (𝟙 (Spec (CommRingCat.of T))))
          (Spec.map (CommRingCat.ofHom ι.toRingHom)) ⟶
        pullback (projModelStrCR (W₀.map ι.toRingHom)) (𝟙 (Spec (CommRingCat.of K))))
    (hθ₁ : θ ≫ pullback.fst _ _ ≫ Proj.map φ hφ =
      pullback.fst (pullback.snd (projModelStrCR W₀) (𝟙 _)) (Spec.map (CommRingCat.ofHom ι.toRingHom)) ≫
        pullback.fst _ _)
    (hθ₂ : θ ≫ pullback.snd _ _ =
      pullback.snd (pullback.snd (projModelStrCR W₀) (𝟙 _)) (Spec.map (CommRingCat.ofHom ι.toRingHom))) :
    (torsionIdeal (𝒢 T W₀ hΔ₀) n).comap
        (pullback.fst (pullback.snd (projModelStrCR W₀) (𝟙 _)) (Spec.map (CommRingCat.ofHom ι.toRingHom))) =
      (torsionIdeal (𝒢 K (W₀.map ι.toRingHom) hΔ') n).comap θ := by p2m_exact_reverting @_root_.P2MW.S_WeierstrassCurve_DrinfeldGlobal_torsionIdeal_comap_fst_eq_torsionIdeal_comap_theta.solution
