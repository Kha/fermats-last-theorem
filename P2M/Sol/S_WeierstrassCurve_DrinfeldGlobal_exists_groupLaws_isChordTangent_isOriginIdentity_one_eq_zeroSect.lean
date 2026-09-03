import Mathlib
import Definitions.Def_WeierstrassCurve_ProjModel_GroupLawVocabulary
import Definitions.Def_WeierstrassCurve_DrinfeldLevelFunctor
import Theorems.Thm_WeierstrassProjModel_exists_relativeGroupLaw_one_eq_zeroSect_isPointsEval_of_isUnit
import Theorems.Thm_WeierstrassProjModel_RelativeGroupLaw_exists_isOriginChartSection_iff_one_eq_kwZeroSect
import P2M.Util
namespace P2MW.S_WeierstrassCurve_DrinfeldGlobal_exists_groupLaws_isChordTangent_isOriginIdentity_one_eq_zeroSect
attribute [-simp] WeierstrassProjModel.kw_lrThird_substHom_X

set_option autoImplicit false

universe u

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits NeronModelInfra WeierstrassProjModel WeierstrassCurve.DrinfeldGlobal

attribute [local instance] MvPolynomial.gradedAlgebra WeierstrassProjModel.kw_pbac_awayAlgebra

theorem solution
    (A : Type) [CommRing A] :
    ∃ 𝒢 : GroupLaws.{0} A, 𝒢.IsChordTangent ∧ 𝒢.IsOriginIdentity ∧
      ∀ (T : Type) [CommRing T] [Algebra A T] (W : WeierstrassCurve.Projective T) (hΔ : IsUnit W.Δ)
        {S : Scheme.{0}} (s : S ⟶ Spec (CommRingCat.of T)),
        ((𝒢 T W hΔ).one s).1 = s ≫ (kwZeroSect T W.toAffine).1 := by
  classical
  refine ⟨fun T _ _ W hΔ =>
    (WeierstrassProjModel.exists_relativeGroupLaw_one_eq_zeroSect_isPointsEval_of_isUnit W hΔ).choose,
    ?_, ?_, ?_⟩
  · intro T _ _ W hΔ
    obtain ⟨ev, -, hev⟩ :=
      (WeierstrassProjModel.exists_relativeGroupLaw_one_eq_zeroSect_isPointsEval_of_isUnit W hΔ).choose_spec
    exact ⟨ev, hev⟩
  · intro T _ _ W hΔ
    obtain ⟨-, hone, -⟩ :=
      (WeierstrassProjModel.exists_relativeGroupLaw_one_eq_zeroSect_isPointsEval_of_isUnit W hΔ).choose_spec
    refine (WeierstrassProjModel.RelativeGroupLaw.exists_isOriginChartSection_iff_one_eq_kwZeroSect
      (T := T) W.toAffine _).mpr ?_
    rw [hone, Category.id_comp]
  · intro T _ _ W hΔ S s
    obtain ⟨-, hone, -⟩ :=
      (WeierstrassProjModel.exists_relativeGroupLaw_one_eq_zeroSect_isPointsEval_of_isUnit W hΔ).choose_spec
    exact hone s
