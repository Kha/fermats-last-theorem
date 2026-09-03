import Mathlib
import Definitions.Def_AlgebraicGeometry_PicDualNumberDeformationClassSpec
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_RelPicard_exists_isFrameOn_and_map_eq_oneAddEpsMul_smul_of_nonempty_pullback_iso_unit
attribute [-instance] AlgebraicGeometry.SmoothOfRelativeDimension.fiberToSpecResidueField AlgebraicGeometry.SmoothOfRelativeDimension.pullback_snd AlgebraicGeometry.SmoothOfRelativeDimension.pullback_fst AlgebraicGeometry.SmoothOfRelativeDimension.smooth_one AlgebraicGeometry.SmoothProperCurve.isIntegral_pullback_Spec_field AlgebraicGeometry.IsProper.fiberToSpecResidueField SheafOfModules.isIso_ihomModelToIhom
attribute [-simp] AlgebraicGeometry.RelPicard.BaseChange.relSubPicPresheafRestrictIso_hom_app_coe AlgebraicGeometry.RelPicard.BaseChange.relSubPicPresheafRestrictIso_inv_app_coe AlgebraicGeometry.RelPicard.BaseChange.restrict_P AlgebraicGeometry.SmoothProperCurve.sectionBaseChange_coe_snd AlgebraicGeometry.SmoothProperCurve.sectionBaseChange_coe_fst PresheafOfModules.InternalHom.IsSheafAux.appAt_toPresheafHom SheafOfModules.ihomSectionsEquivFamily_unit AlgebraicGeometry.Scheme.Modules.restrictHomEquivFamily_apply SheafOfModules.ihomEval_unit_app AlgebraicGeometry.Scheme.Modules.ihomEval_zero_right AlgebraicGeometry.Scheme.Modules.ihomEval_zero_left AlgebraicGeometry.Scheme.Modules.homOfFamily_app_apply SheafOfModules.unit_ihomSectionsEquivFamily AlgebraicGeometry.Scheme.Modules.familyOfHom_app AlgebraicGeometry.Scheme.Modules.restrictUnitIso_hom_app_apply AlgebraicGeometry.Scheme.Modules.restrictUnitIso_inv_app_apply AlgebraicGeometry.Scheme.Modules.restrictHomOfFamily_app_apply AlgebraicGeometry.Scheme.Modules.restrictHomEquivFamily_symm_apply AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_neg AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_zero AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_sub AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_add AlgebraicGeometry.tilde.functorCompPullbackSpecIso_app

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.RelPicard NeronModelInfra
  AlgebraicGeometry.Scheme.TwoAffineOpenCover
namespace AlgebraicGeometry.RelPicard

theorem exists_isFrameOn_and_map_eq_oneAddEpsMul_smul_of_nonempty_pullback_iso_unit
    {R : Type u} [CommRing R] {C : Scheme.{u}} (c : C ⟶ Spec (.of R))
    (A : Type u) [CommRing A] [Algebra R A] (𝒲 : C.TwoAffineOpenCover)
    (N : (Limits.pullback c (Scheme.TwoAffineOpenCover.specMap R (DualNumber A))).Modules)
    (hN : Scheme.Modules.IsInvertible N)
    (h0 : Nonempty ((Scheme.Modules.pullback (RelPicard.baseChangeSnd c (dualNumberReductionOver R A))).obj N ≅
      SheafOfModules.unit.{u} (Limits.pullback c (Scheme.TwoAffineOpenCover.specMap R A)).ringCatSheaf)) :
    ∃ (e₀ : Γ(N, (𝒲.pullback c (DualNumber A)).U0)) (e₁ : Γ(N, (𝒲.pullback c (DualNumber A)).U1))
      (g : ((𝒲.pullback c A).cover (pullback.snd c (Scheme.TwoAffineOpenCover.specMap R A))).A01),
      Scheme.Modules.IsFrameOn e₀ (𝒲.pullback c (DualNumber A)).U0 ∧
      Scheme.Modules.IsFrameOn e₁ (𝒲.pullback c (DualNumber A)).U1 ∧
      N.presheaf.map (homOfLE inf_le_right).op e₁ =
        (show Γ(Limits.pullback c (Scheme.TwoAffineOpenCover.specMap R (DualNumber A)),
            (𝒲.pullback c (DualNumber A)).U0 ⊓ (𝒲.pullback c (DualNumber A)).U1) from oneAddEpsMul A 𝒲 c g) •
          N.presheaf.map (homOfLE inf_le_left).op e₀ := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_RelPicard_exists_isFrameOn_and_map_eq_oneAddEpsMul_smul_of_nonempty_pullback_iso_unit.solution
end AlgebraicGeometry.RelPicard
