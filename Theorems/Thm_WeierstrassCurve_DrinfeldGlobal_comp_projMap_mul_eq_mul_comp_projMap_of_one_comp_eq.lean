import Mathlib
import Definitions.Def_WeierstrassCurve_DrinfeldLevelFunctor
import P2M.Util
import P2M.Sol.S_WeierstrassCurve_DrinfeldGlobal_comp_projMap_mul_eq_mul_comp_projMap_of_one_comp_eq
attribute [-instance] WeierstrassProjModel.quotGradingSubmoduleDegreeZeroFiniteType WeierstrassProjModel.kw_lrChart_tensorCommRing WeierstrassProjModel.kw_lrChart_biGrading_gradedAlgebra WeierstrassProjModel.projModel_isIso_spec_mapCR WeierstrassProjModel.kw_lrSymOC_isDomain_ℬ₀ WeierstrassProjModel.isProper_projModelStrCR WeierstrassProjModel.homogeneousSubmoduleDegreeZeroFiniteType
attribute [-simp] WeierstrassProjModel.kw_lrAdd_substHom_X WeierstrassProjModel.kw_lrSym_substHom_X

set_option autoImplicit false

universe u

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits NeronModelInfra WeierstrassProjModel
  WeierstrassCurve.DrinfeldGlobal

attribute [local instance] MvPolynomial.gradedAlgebra

theorem WeierstrassCurve.DrinfeldGlobal.comp_projMap_mul_eq_mul_comp_projMap_of_one_comp_eq
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
        ⟨y.1 ≫ Proj.map φ hφ, by rw [Category.assoc, hsq, ← Category.assoc, y.2]⟩).1 := by p2m_exact_reverting @_root_.P2MW.S_WeierstrassCurve_DrinfeldGlobal_comp_projMap_mul_eq_mul_comp_projMap_of_one_comp_eq.solution
