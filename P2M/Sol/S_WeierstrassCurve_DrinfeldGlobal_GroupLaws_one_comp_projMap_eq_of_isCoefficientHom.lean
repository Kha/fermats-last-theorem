import Mathlib
import Definitions.Def_WeierstrassCurve_ProjModel
import Definitions.Def_WeierstrassCurve_DrinfeldBasisGlobal
import Definitions.Def_WeierstrassCurve_DrinfeldTransportPin
import Definitions.Def_WeierstrassCurve_SectionAtOrigin
import Definitions.Def_WeierstrassCurve_DrinfeldLevelFunctor
import Definitions.Def_WeierstrassCurve_DrinfeldBasisRelative
import Theorems.Thm_WeierstrassCurve_DrinfeldGlobal_one_comp_projMap_eq_of_isOriginChartSection
import P2M.Util
namespace P2MW.S_WeierstrassCurve_DrinfeldGlobal_GroupLaws_one_comp_projMap_eq_of_isCoefficientHom

set_option autoImplicit false

universe u

open AlgebraicGeometry CategoryTheory WeierstrassProjModel WeierstrassCurve.DrinfeldGlobal NeronModelInfra

theorem solution
    (A : Type u) [CommRing A] (𝒢 : GroupLaws A) (h𝒢O : 𝒢.IsOriginIdentity)
    (T : Type u) [CommRing T] [Algebra A T] (K : Type u) [Field K] [Algebra A K] (f : T →ₐ[A] K)
    (W : WeierstrassCurve T) (hΔ : IsUnit W.Δ) (hΔ' : IsUnit (W.map f.toRingHom).Δ)
    (φ : projModelGradingCR W →+*ᵍ projModelGradingCR (W.map f.toRingHom))
    (hφ : HomogeneousIdeal.irrelevant (projModelGradingCR (W.map f.toRingHom)) ≤
      (HomogeneousIdeal.irrelevant (projModelGradingCR W)).map φ)
    (hφc : IsCoefficientHom W f.toRingHom φ)
    {S : Scheme.{u}} (s : S ⟶ Spec (CommRingCat.of K)) :
    ((𝒢 K (W.map f.toRingHom) hΔ').one s).1 ≫ Proj.map φ hφ =
      ((𝒢 T W hΔ).one (s ≫ Spec.map (CommRingCat.ofHom f.toRingHom))).1 := by
  obtain ⟨χ, hχ, hχx, hχz⟩ := h𝒢O T W hΔ
  obtain ⟨χ', hχ', hχ'x, hχ'z⟩ := h𝒢O K (W.map f.toRingHom) hΔ'
  have hK : ((𝒢 K (W.map f.toRingHom) hΔ').one s).1 =
      s ≫ ((𝒢 K (W.map f.toRingHom) hΔ').one (𝟙 _)).1 := by
    rw [← (𝒢 K (W.map f.toRingHom) hΔ').one_natural (𝟙 _) s s (Category.comp_id s), schemeHomOverComp_coe]
  have hT : ((𝒢 T W hΔ).one (s ≫ Spec.map (CommRingCat.ofHom f.toRingHom))).1 =
      (s ≫ Spec.map (CommRingCat.ofHom f.toRingHom)) ≫ ((𝒢 T W hΔ).one (𝟙 _)).1 := by
    rw [← (𝒢 T W hΔ).one_natural (𝟙 _) (s ≫ Spec.map (CommRingCat.ofHom f.toRingHom))
      (s ≫ Spec.map (CommRingCat.ofHom f.toRingHom)) (Category.comp_id _), schemeHomOverComp_coe]
  rw [hK, hT, Category.assoc, Category.assoc,
    WeierstrassCurve.DrinfeldGlobal.one_comp_projMap_eq_of_isOriginChartSection W f.toRingHom φ hφ hφc
      (𝒢 T W hΔ) (𝒢 K (W.map f.toRingHom) hΔ') χ hχ hχx hχz χ' hχ' hχ'x hχ'z]
