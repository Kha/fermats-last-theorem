import Mathlib
import Definitions.Def_JacJ1Iface
import Definitions.Def_AlgebraicGeometry_RelativeGroupLaw
import Definitions.Def_AlgebraicGeometry_NeronModelEndomorphismExtension
import Definitions.Def_AlgebraicGeometry_RelativeGroupLawEndDegree
import Definitions.Def_SheafOfModules_MonoidalV2
import Definitions.Def_AlgebraicGeometry_ModulesTensorPowV2
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_OModulePresheafEulerChar
import Definitions.Def_AlgebraicGeometry_OModulePresheafOfModules
import Definitions.Def_GoodReductionJacobian_RelativeGroupLawTranslate
import Definitions.Def_AlgebraicGeometry_PolarisationRosati
import Definitions.Def_AlgebraicGeometry_PolarisationPicZero
import Definitions.Def_AlgebraicGeometry_ModulesPullbackMonoidalV2
import Theorems.Thm_AlgebraicGeometry_Polarisation_isIso_lift_fst_addMor
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_dual_monoidalV2
import P2M.Util
namespace P2MW.S_AlgebraicGeometry_Polarisation_exists_iso_mumfordBundle_tensor_pullback_snd_iso_pullback

set_option autoImplicit false

p2m_open "CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory AlgebraicGeometry NeronModelInfra GoodReductionJacobian AlgebraicGeometry.Polarisation"

theorem solution
    {S : Type} [CommRing S] {A : Scheme.{0}} (f : A ⟶ Spec (CommRingCat.of S)) (L : RelativeGroupLaw S f)
    (M : A.Modules) (hM : Scheme.Modules.IsInvertible M) :
    ∃ σ : pullback f f ≅ pullback f f,
      σ.hom ≫ pullback.fst f f = pullback.fst f f ∧ σ.hom ≫ pullback.snd f f = addMor f L ∧
      Nonempty (mumfordBundle f L M ⊗ (Scheme.Modules.pullback (pullback.snd f f)).obj M ≅
        (Scheme.Modules.pullback σ.hom).obj
          ((Scheme.Modules.pullback (pullback.fst f f)).obj (Scheme.Modules.dual M) ⊗
            (Scheme.Modules.pullback (pullback.snd f f)).obj M)) := by
  haveI := Polarisation.isIso_lift_fst_addMor f L
  let σ : pullback f f ≅ pullback f f :=
    asIso (pullback.lift (pullback.fst f f) (addMor f L) (addMor_over f L).symm)
  have hσ1 : σ.hom ≫ pullback.fst f f = pullback.fst f f := pullback.lift_fst _ _ _
  have hσ2 : σ.hom ≫ pullback.snd f f = addMor f L := pullback.lift_snd _ _ _
  obtain ⟨-, ⟨εM⟩⟩ := Scheme.Modules.IsInvertible.dual_monoidalV2 hM
  refine ⟨σ, hσ1, hσ2, ⟨?_⟩⟩

  have e2 : (Scheme.Modules.pullback (pullback.snd f f)).obj (Scheme.Modules.dual M) ⊗
      (Scheme.Modules.pullback (pullback.snd f f)).obj M ≅ 𝟙_ _ :=
    (Scheme.Modules.pullbackTensorObjIso (pullback.snd f f) (Scheme.Modules.dual M) M).symm ≪≫
      (Scheme.Modules.pullback (pullback.snd f f)).mapIso (β_ _ _ ≪≫ εM) ≪≫
      Scheme.Modules.pullbackTensorUnitObjIso (pullback.snd f f)

  have c1 : (Scheme.Modules.pullback σ.hom).obj ((Scheme.Modules.pullback (pullback.fst f f)).obj (Scheme.Modules.dual M)) ≅
      (Scheme.Modules.pullback (pullback.fst f f)).obj (Scheme.Modules.dual M) :=
    (Scheme.Modules.pullbackComp σ.hom (pullback.fst f f)).app _ ≪≫ (Scheme.Modules.pullbackCongr hσ1).app _
  have c2 : (Scheme.Modules.pullback σ.hom).obj ((Scheme.Modules.pullback (pullback.snd f f)).obj M) ≅
      (Scheme.Modules.pullback (addMor f L)).obj M :=
    (Scheme.Modules.pullbackComp σ.hom (pullback.snd f f)).app _ ≪≫ (Scheme.Modules.pullbackCongr hσ2).app _

  have lhs : mumfordBundle f L M ⊗ (Scheme.Modules.pullback (pullback.snd f f)).obj M ≅
      (Scheme.Modules.pullback (pullback.fst f f)).obj (Scheme.Modules.dual M) ⊗
        (Scheme.Modules.pullback (addMor f L)).obj M :=
    α_ _ _ _ ≪≫ (Iso.refl _ ⊗ᵢ (α_ _ _ _ ≪≫ (Iso.refl _ ⊗ᵢ e2) ≪≫ ρ_ _)) ≪≫ β_ _ _

  have rhs : (Scheme.Modules.pullback σ.hom).obj
      ((Scheme.Modules.pullback (pullback.fst f f)).obj (Scheme.Modules.dual M) ⊗
        (Scheme.Modules.pullback (pullback.snd f f)).obj M) ≅
      (Scheme.Modules.pullback (pullback.fst f f)).obj (Scheme.Modules.dual M) ⊗
        (Scheme.Modules.pullback (addMor f L)).obj M :=
    Scheme.Modules.pullbackTensorObjIso σ.hom _ _ ≪≫ (c1 ⊗ᵢ c2)
  exact lhs ≪≫ rhs.symm
