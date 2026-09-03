import Mathlib
import Definitions.Def_WeierstrassCurve_ProjModel_GroupLawVocabulary
import Definitions.Def_WeierstrassCurve_DrinfeldLevelFunctor
import P2M.Util
import P2M.Sol.S_WeierstrassCurve_DrinfeldGlobal_one_eq_zeroSect_of_one_comp_projMap_eq_of_isPullback

set_option autoImplicit false

universe u

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits NeronModelInfra WeierstrassProjModel
  WeierstrassCurve.DrinfeldGlobal

attribute [local instance] MvPolynomial.gradedAlgebra WeierstrassProjModel.kw_pbac_awayAlgebra

theorem WeierstrassCurve.DrinfeldGlobal.one_eq_zeroSect_of_one_comp_projMap_eq_of_isPullback
    {T T' : Type u} [CommRing T] [CommRing T'] (W : WeierstrassCurve.Projective T) (f : T →+* T')
    (φ : projModelGradingCR W →+*ᵍ projModelGradingCR (W.map f))
    (hφ : HomogeneousIdeal.irrelevant (projModelGradingCR (W.map f)) ≤
      (HomogeneousIdeal.irrelevant (projModelGradingCR W)).map φ)
    (hcoef : IsCoefficientHom W f φ)
    (hP : IsPullback (Proj.map φ hφ) (projModelStrCR (W.map f)) (projModelStrCR W)
      (Spec.map (CommRingCat.ofHom f)))
    (G : RelativeGroupLaw T (projModelStrCR W)) (G' : RelativeGroupLaw T' (projModelStrCR (W.map f)))
    (hG : ∀ {S : Scheme.{u}} (s : S ⟶ Spec (CommRingCat.of T)), (G.one s).1 = s ≫ (kwZeroSect T W.toAffine).1)
    (hone : ∀ {S : Scheme.{u}} (s : S ⟶ Spec (CommRingCat.of T')),
      (G'.one s).1 ≫ Proj.map φ hφ = (G.one (s ≫ Spec.map (CommRingCat.ofHom f))).1)
    {S : Scheme.{u}} (s : S ⟶ Spec (CommRingCat.of T')) :
    (G'.one s).1 = s ≫ (kwZeroSect T' (W.map f).toAffine).1 := by p2m_exact_reverting @_root_.P2MW.S_WeierstrassCurve_DrinfeldGlobal_one_eq_zeroSect_of_one_comp_projMap_eq_of_isPullback.solution
