import Mathlib
import Definitions.Def_WeierstrassCurve_ProjModel_GroupLawVocabulary
import Definitions.Def_WeierstrassCurve_DrinfeldLevelFunctor
import P2M.Util
import P2M.Sol.S_WeierstrassCurve_DrinfeldGlobal_exists_groupLaws_isChordTangent_isOriginIdentity_one_eq_zeroSect
attribute [-simp] WeierstrassProjModel.kw_lrThird_substHom_X

set_option autoImplicit false

universe u

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits NeronModelInfra WeierstrassProjModel
  WeierstrassCurve.DrinfeldGlobal

attribute [local instance] MvPolynomial.gradedAlgebra WeierstrassProjModel.kw_pbac_awayAlgebra

theorem WeierstrassCurve.DrinfeldGlobal.exists_groupLaws_isChordTangent_isOriginIdentity_one_eq_zeroSect
    (A : Type) [CommRing A] :
    ∃ 𝒢 : GroupLaws.{0} A, 𝒢.IsChordTangent ∧ 𝒢.IsOriginIdentity ∧
      ∀ (T : Type) [CommRing T] [Algebra A T] (W : WeierstrassCurve.Projective T) (hΔ : IsUnit W.Δ)
        {S : Scheme.{0}} (s : S ⟶ Spec (CommRingCat.of T)),
        ((𝒢 T W hΔ).one s).1 = s ≫ (kwZeroSect T W.toAffine).1 := by p2m_exact_reverting @_root_.P2MW.S_WeierstrassCurve_DrinfeldGlobal_exists_groupLaws_isChordTangent_isOriginIdentity_one_eq_zeroSect.solution
