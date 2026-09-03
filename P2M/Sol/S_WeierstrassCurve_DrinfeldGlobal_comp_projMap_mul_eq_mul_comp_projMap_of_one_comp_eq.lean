import Mathlib
import Definitions.Def_WeierstrassCurve_DrinfeldLevelFunctor
import Theorems.Thm_WeierstrassProjModel_RelativeGroupLaw_mul_eq_of_one_eq_of_isElliptic
import Theorems.Thm_WeierstrassCurve_DrinfeldGlobal_isPullback_projMap_of_isCoefficientHom
import Theorems.Thm_WeierstrassProjModel_RelativeGroupLaw_exists_relativeGroupLaw_comp_eq_of_isPullback
import P2M.Util
namespace P2MW.S_WeierstrassCurve_DrinfeldGlobal_comp_projMap_mul_eq_mul_comp_projMap_of_one_comp_eq
attribute [-instance] WeierstrassProjModel.quotGradingSubmoduleDegreeZeroFiniteType WeierstrassProjModel.kw_lrChart_tensorCommRing WeierstrassProjModel.kw_lrChart_biGrading_gradedAlgebra WeierstrassProjModel.projModel_isIso_spec_mapCR WeierstrassProjModel.kw_lrSymOC_isDomain_ℬ₀ WeierstrassProjModel.isProper_projModelStrCR WeierstrassProjModel.homogeneousSubmoduleDegreeZeroFiniteType
attribute [-simp] WeierstrassProjModel.kw_lrAdd_substHom_X WeierstrassProjModel.kw_lrSym_substHom_X

set_option autoImplicit false

universe u

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits NeronModelInfra WeierstrassProjModel WeierstrassCurve.DrinfeldGlobal

attribute [local instance] MvPolynomial.gradedAlgebra

theorem solution
    {T T' : Type u} [CommRing T] [CommRing T'] (V : WeierstrassCurve.Projective T) [V.toAffine.IsElliptic]
    (f : T →+* T')
    (φ : projModelGradingCR V →+*ᵍ projModelGradingCR (V.map f))
    (hφ : HomogeneousIdeal.irrelevant (projModelGradingCR (V.map f)) ≤
      (HomogeneousIdeal.irrelevant (projModelGradingCR V)).map φ)
    (hcoef : IsCoefficientHom V f φ)
    (G : RelativeGroupLaw T (projModelStrCR V)) (L : RelativeGroupLaw T' (projModelStrCR (V.map f)))
    (h1 : (L.one (𝟙 (Spec (CommRingCat.of T')))).1 ≫ Proj.map φ hφ =
      Spec.map (CommRingCat.ofHom f) ≫ (G.one (𝟙 (Spec (CommRingCat.of T)))).1)
    (hsq : Proj.map φ hφ ≫ projModelStrCR V = projModelStrCR (V.map f) ≫ Spec.map (CommRingCat.ofHom f))
    {S : Scheme.{u}} (s : S ⟶ Spec (CommRingCat.of T')) (x y : SchemeHomOver s (projModelStrCR (V.map f))) :
    (L.mul s x y).1 ≫ Proj.map φ hφ =
      (G.mul (s ≫ Spec.map (CommRingCat.ofHom f))
        ⟨x.1 ≫ Proj.map φ hφ, by rw [Category.assoc, hsq, ← Category.assoc, x.2]⟩
        ⟨y.1 ≫ Proj.map φ hφ, by rw [Category.assoc, hsq, ← Category.assoc, y.2]⟩).1 := by

  have hP := WeierstrassCurve.DrinfeldGlobal.isPullback_projMap_of_isCoefficientHom V f φ hφ hcoef

  obtain ⟨G', hmul', hone'⟩ :=
    WeierstrassProjModel.RelativeGroupLaw.exists_relativeGroupLaw_comp_eq_of_isPullback f
      (projModelStrCR V) (projModelStrCR (V.map f)) (Proj.map φ hφ) hP G

  haveI : (V.map f).toAffine.IsElliptic := by
    change (V.toAffine.map f).IsElliptic
    infer_instance

  have hidx : ∀ {t t' : Spec (CommRingCat.of T') ⟶ Spec (CommRingCat.of T)} (h : t = t'),
      (G.one t).1 = (G.one t').1 := by
    intro t t' h; subst h; rfl
  have hGone : (G.one (𝟙 (Spec (CommRingCat.of T')) ≫ Spec.map (CommRingCat.ofHom f))).1 =
      Spec.map (CommRingCat.ofHom f) ≫ (G.one (𝟙 (Spec (CommRingCat.of T)))).1 := by
    rw [← G.one_natural (𝟙 _) (𝟙 (Spec (CommRingCat.of T')) ≫ Spec.map (CommRingCat.ofHom f))
      (Spec.map (CommRingCat.ofHom f)) (by simp), schemeHomOverComp_coe]
  have hunits : (L.one (𝟙 (Spec (CommRingCat.of T')))).1 = (G'.one (𝟙 (Spec (CommRingCat.of T')))).1 := by
    apply hP.hom_ext
    · rw [h1, hone', hGone]
    · rw [(L.one _).2, (G'.one _).2]

  have hLG' := WeierstrassProjModel.RelativeGroupLaw.mul_eq_of_one_eq_of_isElliptic (V.map f) L G' hunits s x y
  rw [hLG']
  exact hmul' s x y
