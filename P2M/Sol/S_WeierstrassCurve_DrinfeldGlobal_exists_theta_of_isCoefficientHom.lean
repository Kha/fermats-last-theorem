import Definitions.Def_WeierstrassCurve_ProjModel
import Definitions.Def_WeierstrassCurve_DrinfeldBasisGlobal
import Definitions.Def_WeierstrassCurve_DrinfeldTransportPin
import Theorems.Thm_WeierstrassCurve_DrinfeldGlobal_isPullback_projMap_of_isCoefficientHom
import P2M.Util
namespace P2MW.S_WeierstrassCurve_DrinfeldGlobal_exists_theta_of_isCoefficientHom
attribute [-instance] WeierstrassProjModel.quotGradingSubmoduleDegreeZeroFiniteType WeierstrassProjModel.kw_lrChart_tensorCommRing WeierstrassProjModel.kw_lrChart_biGrading_gradedAlgebra WeierstrassProjModel.projModel_isIso_spec_mapCR WeierstrassProjModel.kw_lrSymOC_isDomain_ℬ₀ WeierstrassProjModel.isProper_projModelStrCR WeierstrassProjModel.homogeneousSubmoduleDegreeZeroFiniteType
attribute [-simp] WeierstrassProjModel.kw_lrAdd_substHom_X WeierstrassProjModel.kw_lrSym_substHom_X

set_option autoImplicit false

universe u

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits WeierstrassProjModel WeierstrassCurve.DrinfeldGlobal NeronModelInfra

theorem solution
    {T K : Type u} [CommRing T] [CommRing K] (W₀ : WeierstrassCurve T) (f : T →+* K)
    (φ : projModelGradingCR W₀ →+*ᵍ projModelGradingCR (W₀.map f))
    (hφ : HomogeneousIdeal.irrelevant (projModelGradingCR (W₀.map f)) ≤
      (HomogeneousIdeal.irrelevant (projModelGradingCR W₀)).map φ)
    (hφc : IsCoefficientHom W₀ f φ) :
    ∃ θ : pullback (pullback.snd (projModelStrCR W₀) (𝟙 (Spec (CommRingCat.of T)))) (Spec.map (CommRingCat.ofHom f)) ⟶
        pullback (projModelStrCR (W₀.map f)) (𝟙 (Spec (CommRingCat.of K))),
      θ ≫ pullback.fst _ _ ≫ Proj.map φ hφ =
        pullback.fst (pullback.snd (projModelStrCR W₀) (𝟙 _)) (Spec.map (CommRingCat.ofHom f)) ≫ pullback.fst _ _ ∧
      θ ≫ pullback.snd _ _ =
        pullback.snd (pullback.snd (projModelStrCR W₀) (𝟙 _)) (Spec.map (CommRingCat.ofHom f)) := by
  have H := WeierstrassCurve.DrinfeldGlobal.isPullback_projMap_of_isCoefficientHom W₀ f φ hφ hφc
  have c1 : pullback.fst (projModelStrCR W₀) (𝟙 (Spec (CommRingCat.of T))) ≫ projModelStrCR W₀ =
      pullback.snd (projModelStrCR W₀) (𝟙 _) ≫ 𝟙 _ := pullback.condition
  have c2 : pullback.fst (pullback.snd (projModelStrCR W₀) (𝟙 (Spec (CommRingCat.of T)))) (Spec.map (CommRingCat.ofHom f)) ≫
      pullback.snd (projModelStrCR W₀) (𝟙 _) =
      pullback.snd (pullback.snd (projModelStrCR W₀) (𝟙 (Spec (CommRingCat.of T)))) (Spec.map (CommRingCat.ofHom f)) ≫
        Spec.map (CommRingCat.ofHom f) := pullback.condition

  let u := H.lift (pullback.fst _ _ ≫ pullback.fst (projModelStrCR W₀) (𝟙 _))
    (pullback.snd (pullback.snd (projModelStrCR W₀) (𝟙 (Spec (CommRingCat.of T)))) (Spec.map (CommRingCat.ofHom f)))
    (by rw [Category.assoc, c1, ← Category.assoc, c2, Category.assoc, Category.comp_id])
  refine ⟨pullback.lift u (pullback.snd _ _) (by rw [IsPullback.lift_snd, Category.comp_id]), ?_, ?_⟩
  · rw [← Category.assoc, pullback.lift_fst, IsPullback.lift_fst]
  · rw [pullback.lift_snd]
