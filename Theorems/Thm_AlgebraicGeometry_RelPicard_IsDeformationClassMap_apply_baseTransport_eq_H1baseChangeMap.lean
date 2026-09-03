import Mathlib
import Definitions.Def_AlgebraicGeometry_PicDualNumberDeformationClassSpec
import Definitions.Def_AlgebraicGeometry_RigKerDualNumberBaseTransport
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_RelPicard_IsDeformationClassMap_apply_baseTransport_eq_H1baseChangeMap
attribute [-instance] SheafOfModules.isIso_ihomModelToIhom
attribute [-simp] PresheafOfModules.InternalHom.IsSheafAux.appAt_toPresheafHom SheafOfModules.ihomSectionsEquivFamily_unit AlgebraicGeometry.Scheme.Modules.restrictHomEquivFamily_apply SheafOfModules.ihomEval_unit_app AlgebraicGeometry.Scheme.Modules.ihomEval_zero_right AlgebraicGeometry.Scheme.Modules.ihomEval_zero_left AlgebraicGeometry.Scheme.Modules.homOfFamily_app_apply SheafOfModules.unit_ihomSectionsEquivFamily AlgebraicGeometry.Scheme.Modules.familyOfHom_app AlgebraicGeometry.Scheme.Modules.restrictUnitIso_hom_app_apply AlgebraicGeometry.Scheme.Modules.restrictUnitIso_inv_app_apply AlgebraicGeometry.Scheme.Modules.restrictHomOfFamily_app_apply AlgebraicGeometry.Scheme.Modules.restrictHomEquivFamily_symm_apply AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_neg AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_zero AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_sub AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_add AlgebraicGeometry.tilde.functorCompPullbackSpecIso_app

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.RelPicard
  AlgebraicGeometry.SmoothProperCurve NeronModelInfra

namespace AlgebraicGeometry.RelPicard

theorem IsDeformationClassMap.apply_baseTransport_eq_H1baseChangeMap
    {R : Type u} [CommRing R] {C : Scheme.{u}} (c : C ⟶ Spec (.of R)) (ε : SchemeHomOver (𝟙 (Spec (.of R))) c)
    (K : Type u) [CommRing K] [Algebra R K] (𝒲 : C.TwoAffineOpenCover)
    {δ : RigKerDualNumber c ε K → H1StructureSheaf c K 𝒲}
    {δ' : RigKerDualNumber (baseChange R c K) (sectionBaseChange K ε) K →
      H1StructureSheaf (baseChange R c K) K (𝒲.pullback c K)}
    (hδ : IsDeformationClassMap c ε K 𝒲 δ)
    (hδ' : IsDeformationClassMap (baseChange R c K) (sectionBaseChange K ε) K (𝒲.pullback c K) δ')
    (m : RigKerDualNumber c ε K) :
    δ' (RigKerDualNumber.baseTransport K c ε K m) =
      Scheme.TwoAffineOpenCover.H1baseChangeMap (𝒲.pullback c K) (baseChange R c K) K (δ m) := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_RelPicard_IsDeformationClassMap_apply_baseTransport_eq_H1baseChangeMap.solution

end AlgebraicGeometry.RelPicard
