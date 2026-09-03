import Mathlib
import Definitions.Def_AlgebraicGeometry_RigKerDualNumber
import Definitions.Def_AlgebraicGeometry_PicDualNumberDeformationClassSpec
import Definitions.Def_AlgebraicGeometry_TwoAffineOpenCoverH1BaseChange
import Definitions.Def_AlgebraicGeometry_TwoAffineOpenCover
import Definitions.Def_AlgebraicGeometry_TwoChartCech
import Definitions.Def_AlgebraicCurve_CechSectionsOfDivisor
import Definitions.Def_AlgebraicCurve_PlacesOf
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_RelPicard_IsDeformationClassMap_cechH1ToH1_germ_eq_of_two_covers
attribute [-instance] AlgebraicGeometry.SmoothOfRelativeDimension.fiberToSpecResidueField AlgebraicGeometry.SmoothOfRelativeDimension.pullback_snd AlgebraicGeometry.SmoothOfRelativeDimension.pullback_fst AlgebraicGeometry.SmoothOfRelativeDimension.smooth_one AlgebraicGeometry.SmoothProperCurve.isIntegral_pullback_Spec_field AlgebraicGeometry.IsProper.fiberToSpecResidueField SheafOfModules.isIso_ihomModelToIhom AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation
attribute [-simp] AlgebraicGeometry.RelPicard.BaseChange.relSubPicPresheafRestrictIso_hom_app_coe AlgebraicGeometry.RelPicard.BaseChange.relSubPicPresheafRestrictIso_inv_app_coe AlgebraicGeometry.RelPicard.BaseChange.restrict_P AlgebraicGeometry.SmoothProperCurve.sectionBaseChange_coe_snd AlgebraicGeometry.SmoothProperCurve.sectionBaseChange_coe_fst PresheafOfModules.InternalHom.IsSheafAux.appAt_toPresheafHom SheafOfModules.ihomSectionsEquivFamily_unit AlgebraicGeometry.Scheme.Modules.restrictHomEquivFamily_apply SheafOfModules.ihomEval_unit_app AlgebraicGeometry.Scheme.Modules.ihomEval_zero_right AlgebraicGeometry.Scheme.Modules.ihomEval_zero_left AlgebraicGeometry.Scheme.Modules.homOfFamily_app_apply SheafOfModules.unit_ihomSectionsEquivFamily AlgebraicGeometry.Scheme.Modules.familyOfHom_app AlgebraicGeometry.Scheme.Modules.restrictUnitIso_hom_app_apply AlgebraicGeometry.Scheme.Modules.restrictUnitIso_inv_app_apply AlgebraicGeometry.Scheme.Modules.restrictHomOfFamily_app_apply AlgebraicGeometry.Scheme.Modules.restrictHomEquivFamily_symm_apply AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_neg AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_zero AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_sub AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_add AlgebraicGeometry.tilde.functorCompPullbackSpecIso_app AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.RelPicard NeronModelInfra
  AlgebraicGeometry.Scheme.TwoAffineOpenCover
namespace AlgebraicGeometry.RelPicard

theorem IsDeformationClassMap.cechH1ToH1_germ_eq_of_two_covers
    {R : Type u} [CommRing R] {C : Scheme.{u}} (c : C ⟶ Spec (.of R)) (ε : SchemeHomOver (𝟙 (Spec (.of R))) c)
    (K : Type u) [Field K] [Algebra R K]
    [IsIntegral (Limits.pullback c (Scheme.TwoAffineOpenCover.specMap R K))]
    [IsSeparated (pullback.snd c (Scheme.TwoAffineOpenCover.specMap R K))]
    [SmoothOfRelativeDimension 1 (pullback.snd c (Scheme.TwoAffineOpenCover.specMap R K))]
    (𝒲 𝒲' : C.TwoAffineOpenCover)
    {δ  : RigKerDualNumber c ε K → H1StructureSheaf c K 𝒲}
    {δ' : RigKerDualNumber c ε K → H1StructureSheaf c K 𝒲'}
    (hδ : IsDeformationClassMap c ε K 𝒲 δ) (hδ' : IsDeformationClassMap c ε K 𝒲' δ')
    (x : RigKerDualNumber c ε K)
    (s  : ((𝒲.pullback c K).cover  (pullback.snd c (Scheme.TwoAffineOpenCover.specMap R K))).A01)
    (s' : ((𝒲'.pullback c K).cover (pullback.snd c (Scheme.TwoAffineOpenCover.specMap R K))).A01)
    (hs : δ x = Submodule.Quotient.mk s) (hs' : δ' x = Submodule.Quotient.mk s') :
    letI X' := Limits.pullback c (Scheme.TwoAffineOpenCover.specMap R K)
    letI c' : X' ⟶ Spec (.of K) := pullback.snd c (Scheme.TwoAffineOpenCover.specMap R K)
    letI := (AlgebraicCurve.baseToFunctionField c').toAlgebra
    letI W := 𝒲.pullback c K; letI W' := 𝒲'.pullback c K
    ∀ [Nonempty (W.U0 ⊓ W.U1 : X'.Opens)] [Nonempty (W'.U0 ⊓ W'.U1 : X'.Opens)]
      (hW  : AlgebraicCurve.placesOf c' W.U0  ∪ AlgebraicCurve.placesOf c' W.U1  = Set.univ)
      (hW' : AlgebraicCurve.placesOf c' W'.U0 ∪ AlgebraicCurve.placesOf c' W'.U1 = Set.univ)
      (hsr  : (X'.germToFunctionField (W.U0 ⊓ W.U1)).hom s ∈
        AlgebraicCurve.lSpaceOn (AlgebraicCurve.placesOf c' W.U0 ∩ AlgebraicCurve.placesOf c' W.U1)
          (0 : AlgebraicCurve.Divisor K X'.functionField))
      (hsr' : (X'.germToFunctionField (W'.U0 ⊓ W'.U1)).hom s' ∈
        AlgebraicCurve.lSpaceOn (AlgebraicCurve.placesOf c' W'.U0 ∩ AlgebraicCurve.placesOf c' W'.U1)
          (0 : AlgebraicCurve.Divisor K X'.functionField)),
      AlgebraicCurve.cechH1ToH1 hW 0
          (Submodule.Quotient.mk ⟨(X'.germToFunctionField (W.U0 ⊓ W.U1)).hom s, hsr⟩) =
        AlgebraicCurve.cechH1ToH1 hW' 0
          (Submodule.Quotient.mk ⟨(X'.germToFunctionField (W'.U0 ⊓ W'.U1)).hom s', hsr'⟩) := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_RelPicard_IsDeformationClassMap_cechH1ToH1_germ_eq_of_two_covers.solution
end AlgebraicGeometry.RelPicard
