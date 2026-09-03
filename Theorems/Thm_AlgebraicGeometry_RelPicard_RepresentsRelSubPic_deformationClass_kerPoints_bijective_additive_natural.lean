import Mathlib
import Definitions.Def_AlgebraicGeometry_RigKerDualNumber
import Definitions.Def_AlgebraicGeometry_RelPicardStageHom
import Definitions.Def_AlgebraicGeometry_PicDualNumberDeformationClassSpec
import Definitions.Def_AlgebraicGeometry_TwoAffineOpenCoverH1BaseChange
import Definitions.Def_AlgebraicGeometry_RelativeGroupLaw
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_RelPicard_RepresentsRelSubPic_deformationClass_kerPoints_bijective_additive_natural
attribute [-instance] GaloisRepAdic.instAddCommGroup GaloisRepAdic.instFree GaloisRepAdic.instFinite GaloisRepAdic.instModule ResidualGaloisRep.instModule ResidualGaloisRep.instModuleFinite ResidualGaloisRep.instAddCommGroup WeierstrassCurve.Affine.Point.instSMulCommClassAlgEquivZModTorsionBy instDecEqAlgebraicClosureRat WeierstrassCurve.Affine.Point.instDistribMulActionAlgEquiv WeierstrassCurve.Affine.Point.instModuleZModTorsionBy WeierstrassCurve.Affine.Point.instSMulTorsionBy WeierstrassCurve.Affine.Point.instDistribMulActionTorsionBy WeierstrassCurve.Affine.Point.instSMulAlgEquiv WeierstrassCurve.Affine.Point.instFinite AlgebraicGeometry.SmoothOfRelativeDimension.fiberToSpecResidueField AlgebraicGeometry.SmoothOfRelativeDimension.pullback_snd AlgebraicGeometry.SmoothOfRelativeDimension.pullback_fst AlgebraicGeometry.SmoothOfRelativeDimension.smooth_one AlgebraicGeometry.SmoothProperCurve.isIntegral_pullback_Spec_field AlgebraicGeometry.IsProper.fiberToSpecResidueField SheafOfModules.isIso_ihomModelToIhom
attribute [-simp] GoodReductionJacobian.RelativeGroupLaw.nsmul_zero GoodReductionJacobian.RelativeGroupLaw.mem_torsionSubset GoodReductionJacobian.RelativeGroupLaw.nsmul_succ NeronModelInfra.NeronModelPropertyBundle.endExtensionEquiv_symm_restrict NeronModelInfra.schemeHomOverComp_id_left NeronModelInfra.schemeHomOverComp_id_right NeronModelInfra.schemeHomOverId_coe NeronModelInfra.NeronModelPropertyBundle.endExtensionEquiv_apply NeronModelInfra.NeronModelPropertyBundle.restrict_endExtensionEquiv_symm NeronModelInfra.schemeHomOverComp_coe GaloisRepAdic.mk.injEq GaloisRepAdic.mk.sizeOf_spec GaloisRepAdic.Equiv.mk.sizeOf_spec GaloisRepAdic.Equiv.mk.injEq ResidualGaloisRep.mk.sizeOf_spec ResidualGaloisRep.mk.injEq WeierstrassCurve.Affine.Point.galoisRepModuleEnd_apply FreyPackage.mk.sizeOf_spec FreyPackage.mk.injEq ResidualGaloisRep.Equiv.mk.sizeOf_spec ResidualGaloisRep.Equiv.mk.injEq AlgebraicGeometry.RelPicard.BaseChange.relSubPicPresheafRestrictIso_hom_app_coe AlgebraicGeometry.RelPicard.BaseChange.relSubPicPresheafRestrictIso_inv_app_coe AlgebraicGeometry.RelPicard.BaseChange.restrict_P AlgebraicGeometry.SmoothProperCurve.sectionBaseChange_coe_snd AlgebraicGeometry.SmoothProperCurve.sectionBaseChange_coe_fst PresheafOfModules.InternalHom.IsSheafAux.appAt_toPresheafHom SheafOfModules.ihomSectionsEquivFamily_unit AlgebraicGeometry.Scheme.Modules.restrictHomEquivFamily_apply SheafOfModules.ihomEval_unit_app AlgebraicGeometry.Scheme.Modules.ihomEval_zero_right AlgebraicGeometry.Scheme.Modules.ihomEval_zero_left AlgebraicGeometry.Scheme.Modules.homOfFamily_app_apply SheafOfModules.unit_ihomSectionsEquivFamily AlgebraicGeometry.Scheme.Modules.familyOfHom_app AlgebraicGeometry.Scheme.Modules.restrictUnitIso_hom_app_apply AlgebraicGeometry.Scheme.Modules.restrictUnitIso_inv_app_apply AlgebraicGeometry.Scheme.Modules.restrictHomOfFamily_app_apply AlgebraicGeometry.Scheme.Modules.restrictHomEquivFamily_symm_apply AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_neg
attribute [-simp] AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_zero AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_sub AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_add AlgebraicGeometry.tilde.functorCompPullbackSpecIso_app

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.RelPicard GoodReductionJacobian AlgebraicGeometry.Scheme.TwoAffineOpenCover open NeronModelInfra hiding schemeHomOverComp

theorem AlgebraicGeometry.RelPicard.RepresentsRelSubPic.deformationClass_kerPoints_bijective_additive_natural
    {R : Type u} [CommRing R] {C : Scheme.{u}} {c : C ⟶ Spec (.of R)}
    {ε : SchemeHomOver (𝟙 (Spec (.of R))) c} {D : RelativePic0Designation R c}
    (h : RepresentsRelSubPic c ε (algEquivZeroCut c ε) D) {𝒱 : C.TwoAffineOpenCover}
    (A : Type u) [CommRing A] [Algebra R A]
    {δ : RigKerDualNumber c ε A → H1StructureSheaf c A 𝒱} (hδ : IsDeformationClassMap c ε A 𝒱 δ) :
    letI L := RepresentsRelSubPic.relativeGroupLaw (P := algEquivZeroGroupCut c ε) h

    Function.Bijective (fun x => δ (h.kerPointsToRigKer A x)) ∧

    (∀ h1, δ (h.kerPointsToRigKer A ⟨L.one (specMap R (DualNumber A)), h1⟩) = 0) ∧

    (∀ (x y : {x : SchemeHomOver (specMap R (DualNumber A)) D.toBase //
          dualNumberReduction R A ≫ x.1 = (L.one (specMap R A)).1}) (hxy),
        δ (h.kerPointsToRigKer A ⟨L.mul _ x.1 y.1, hxy⟩) =
          δ (h.kerPointsToRigKer A x) + δ (h.kerPointsToRigKer A y)) ∧

    (∀ (A' : Type u) [CommRing A'] [Algebra R A'] (g : A →ₐ[R] A')
        (x : SchemeHomOver (specMap R (DualNumber A)) D.toBase),
        dualNumberReduction R A ≫ x.1 = (L.one (specMap R A)).1 →
        dualNumberReduction R A' ≫ ((LFP.stageHom R (DualNumber.lift
            ⟨((IsScalarTower.toAlgHom R A' (DualNumber A')).comp g, DualNumber.eps),
              DualNumber.eps_mul_eps, fun _ => Commute.all _ _⟩)).1 ≫ x.1) = (L.one (specMap R A')).1) ∧

    (∀ (A' : Type u) [CommRing A'] [Algebra R A'] {δ' : RigKerDualNumber c ε A' → H1StructureSheaf c A' 𝒱}
        (_ : IsDeformationClassMap c ε A' 𝒱 δ') (g : A →ₐ[R] A')
        (x : {x : SchemeHomOver (specMap R (DualNumber A)) D.toBase //
          dualNumberReduction R A ≫ x.1 = (L.one (specMap R A)).1}) (hx'),
        δ' (h.kerPointsToRigKer A' ⟨GoodReductionJacobian.schemeHomOverComp
            (LFP.stageHom R (DualNumber.lift
              ⟨((IsScalarTower.toAlgHom R A' (DualNumber A')).comp g, DualNumber.eps),
                DualNumber.eps_mul_eps, fun _ => Commute.all _ _⟩)).1
            (LFP.stageHom R (DualNumber.lift
              ⟨((IsScalarTower.toAlgHom R A' (DualNumber A')).comp g, DualNumber.eps),
                DualNumber.eps_mul_eps, fun _ => Commute.all _ _⟩)).2 x.1, hx'⟩) =
          𝒱.H1stageMap c g (δ (h.kerPointsToRigKer A x))) := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_RelPicard_RepresentsRelSubPic_deformationClass_kerPoints_bijective_additive_natural.solution
