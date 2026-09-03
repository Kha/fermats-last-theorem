import Mathlib
import Definitions.Def_WeierstrassCurve_ProjModel_GroupLawVocabulary
import Definitions.Def_WeierstrassCurve_DrinfeldLevelFunctor
import P2M.Util
import P2M.Sol.S_WeierstrassCurve_DrinfeldGlobal_exists_isPointsEval_of_mul_comp_projMap_eq_of_isPullback

set_option autoImplicit false

universe u

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits NeronModelInfra WeierstrassProjModel
  WeierstrassCurve.DrinfeldGlobal

attribute [local instance] MvPolynomial.gradedAlgebra WeierstrassProjModel.kw_pbac_awayAlgebra

theorem WeierstrassCurve.DrinfeldGlobal.exists_isPointsEval_of_mul_comp_projMap_eq_of_isPullback
    {T T' : Type u} [CommRing T] [CommRing T'] (W : WeierstrassCurve.Projective T) (f : T →+* T')
    (φ : projModelGradingCR W →+*ᵍ projModelGradingCR (W.map f))
    (hφ : HomogeneousIdeal.irrelevant (projModelGradingCR (W.map f)) ≤
      (HomogeneousIdeal.irrelevant (projModelGradingCR W)).map φ)
    (hcoef : IsCoefficientHom W f φ)
    (hP : IsPullback (Proj.map φ hφ) (projModelStrCR (W.map f)) (projModelStrCR W)
      (Spec.map (CommRingCat.ofHom f)))
    (G : RelativeGroupLaw T (projModelStrCR W)) (G' : RelativeGroupLaw T' (projModelStrCR (W.map f)))
    (hmul : ∀ {S : Scheme.{u}} (s : S ⟶ Spec (CommRingCat.of T')) (x y : SchemeHomOver s (projModelStrCR (W.map f))),
      (G'.mul s x y).1 ≫ Proj.map φ hφ =
        (G.mul (s ≫ Spec.map (CommRingCat.ofHom f))
          ⟨x.1 ≫ Proj.map φ hφ, by rw [Category.assoc, hP.w, ← Category.assoc, x.2]⟩
          ⟨y.1 ≫ Proj.map φ hφ, by rw [Category.assoc, hP.w, ← Category.assoc, y.2]⟩).1)
    (ev : ∀ (F : Type u) [Field F] [DecidableEq F] [Algebra T F],
      SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap T F))) (projModelStrCR W) ≃
        (W.baseChange F).toAffine.Point)
    (hev : IsPointsEval W G ev) :
    ∃ ev' : ∀ (F : Type u) [Field F] [DecidableEq F] [Algebra T' F],
        SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap T' F))) (projModelStrCR (W.map f)) ≃
          ((W.map f).baseChange F).toAffine.Point,
      IsPointsEval (W.map f) G' ev' := by p2m_exact_reverting @_root_.P2MW.S_WeierstrassCurve_DrinfeldGlobal_exists_isPointsEval_of_mul_comp_projMap_eq_of_isPullback.solution
