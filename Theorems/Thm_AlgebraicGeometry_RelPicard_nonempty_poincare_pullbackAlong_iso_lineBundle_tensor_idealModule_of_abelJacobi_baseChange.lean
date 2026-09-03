import Mathlib
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_RepresentsRelSubPic
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroCut
import Definitions.Def_AlgebraicGeometry_RelSubPicBaseChange
import Definitions.Def_AlgebraicGeometry_RelativePic0DesignationBaseChange
import Definitions.Def_AlgebraicGeometry_SmoothProperCurveBase
import Definitions.Def_AlgebraicGeometry_NeronModelPropertyBundleCarrier
import Definitions.Def_AlgebraicGeometry_IdealSheafModule
import Definitions.Def_AlgebraicGeometry_RelEffCartierDiv
import Definitions.Def_AlgebraicGeometry_RelEffCartierDivOfPoint
import Definitions.Def_SheafOfModules_Monoidal
import Definitions.Def_JacJ1Iface
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_RelPicard_nonempty_poincare_pullbackAlong_iso_lineBundle_tensor_idealModule_of_abelJacobi_baseChange
attribute [-instance] AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instNeg AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instSMulInt AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instAddCommGroup AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instAdd AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instSub AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instModuleCarrierObjOppositeOpensCarrierCarrierCommRingCatPresheafOpOpensTop AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instSMulCarrierObjOppositeOpensCarrierCarrierCommRingCatPresheafOpOpensTop AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instSMulNat AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instZero AlgebraicGeometry.Scheme.Modules.preservesBinaryProducts_opensMap AlgebraicGeometry.Scheme.Modules.pullback_monoidal AlgebraicGeometry.Scheme.Modules.sheafify_isLocalization' AlgebraicGeometry.Scheme.Modules.preservesTerminal_opensMap AlgebraicGeometry.Scheme.Modules.pullback₀_monoidal AlgebraicGeometry.Scheme.Modules.preservesFiniteProducts_opensMap AlgebraicGeometry.Scheme.Modules.instLiftingPresheafOfModulesSheafifyPresheafWOpensCarrierCarrierCommRingCatGrothendieckTopologyObjFunctorOppositeIsSheafSheafCompPullback₀Pullback PresheafOfModules.PullbackMonoidal.pullback_monoidal PresheafOfModules.PullbackMonoidal.isIso_δ PresheafOfModules.pushforward_laxMonoidal PresheafOfModules.PullbackMonoidal.isIso_η PresheafOfModules.free_monoidal PresheafOfModules.restrictScalars_laxMonoidal PresheafOfModules.PullbackMonoidal.isIso_δ_gS PresheafOfModules.pullback_oplaxMonoidal PresheafOfModules.PullbackMonoidal.instPreservesColimitsOfSizeCompOppositeCommRingCatRingCatForget₂RingHomCarrierCarrierPb PresheafOfModules.pullback_monoidal'
attribute [-simp] NeronModelInfra.NeronModelPropertyBundle.endExtensionEquiv_symm_restrict NeronModelInfra.schemeHomOverComp_id_left NeronModelInfra.schemeHomOverComp_id_right NeronModelInfra.schemeHomOverId_coe NeronModelInfra.NeronModelPropertyBundle.endExtensionEquiv_apply NeronModelInfra.NeronModelPropertyBundle.restrict_endExtensionEquiv_symm NeronModelInfra.schemeHomOverComp_coe AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.sub_app AlgebraicGeometry.Scheme.IdealSheafData.sres_sresTop AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.add_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.mk.sizeOf_spec AlgebraicGeometry.Scheme.IdealSheafData.coe_resLE AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.smul_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.coe_ofLE_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.ideal_range AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.zero_app AlgebraicGeometry.Scheme.IdealSheafData.sres_sres AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.comp_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.neg_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.id_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.coe_mulRight_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.nsmul_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.mk.injEq AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.zsmul_app PresheafOfModules.freeεIso_hom_app PresheafOfModules.freeμIso_hom_app

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry AlgebraicGeometry.RelPicard NeronModelInfra GoodReductionJacobian
  AlgebraicGeometry.SmoothProperCurve

theorem AlgebraicGeometry.RelPicard.nonempty_poincare_pullbackAlong_iso_lineBundle_tensor_idealModule_of_abelJacobi_baseChange
    {R : Type u} [CommRing R] {X : Scheme.{u}} (cX : X ⟶ Spec (CommRingCat.of R)) [IsSeparated cX]
    (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) cX)
    (D : RelativePic0Designation R cX) (hrep : RepresentsRelSubPic cX ε (algEquivZeroCut cX ε) D)
    (L' : Type u) [CommRing L'] [Algebra R L'] (k' : Type u) [Field k'] [Algebra R k'] [Algebra L' k'] [IsScalarTower R L' k']
    [SmoothOfRelativeDimension 1 (baseChange R cX k')]
    (hDL : RepresentsRelSubPic (baseChange R cX L') (sectionBaseChange L' ε)
      (algEquivZeroCut (baseChange R cX L') (sectionBaseChange L' ε)) (D.baseChange L'))
    (hPL : Nonempty (hDL.poincare.L ≅ (BaseChange.ofR cX ε L'
      (hrep.poincare.pullbackAlong ⟨pullback.fst D.toBase (specMap R L'), pullback.condition⟩)).L))
    (hrepQ : RepresentsRelSubPic (baseChange R cX k') (sectionBaseChange k' ε)
      (algEquivZeroCut (baseChange R cX k') (sectionBaseChange k' ε)) (D.baseChange k'))
    (ajL : SchemeHomOver (baseChange R cX L') (D.baseChange L').toBase)
    (hajL : ∀ (x : SchemeHomOver (specMap L' k') (baseChange R cX L')),
      Nonempty ((hDL.poincare.pullbackAlong
          ⟨x.1 ≫ ajL.1, (Category.assoc _ _ _).trans ((congrArg (x.1 ≫ ·) ajL.2).trans x.2)⟩).L ≅
        (RelEffCartierDiv.ofPoint (baseChange R cX L') x.1 x.2).lineBundle ⊗
          (RelEffCartierDiv.ofPoint (baseChange R cX L') (specMap L' k' ≫ (sectionBaseChange L' ε).1)
            ((Category.assoc _ _ _).trans ((congrArg (specMap L' k' ≫ ·) (sectionBaseChange L' ε).2).trans
              (Category.comp_id _)))).idealModule))
    (kL : pullback cX (specMap R k') ⟶ pullback cX (specMap R L'))
    (hkL₁ : kL ≫ pullback.fst _ _ = pullback.fst _ _) (hkL₂ : kL ≫ pullback.snd _ _ = pullback.snd _ _ ≫ specMap L' k')
    (P : SchemeHomOver (𝟙 (Spec (CommRingCat.of k'))) (baseChange R cX k'))
    (G : SchemeHomOver (specMap R k') D.toBase) (hG : G.1 = P.1 ≫ kL ≫ ajL.1 ≫ pullback.fst D.toBase (specMap R L'))
    (g : SchemeHomOver (𝟙 (Spec (CommRingCat.of k'))) (D.baseChange k').toBase)
    (isoΘ : Nonempty ((hrep.poincare.pullbackAlong G).L ≅
      (Scheme.Modules.pullback (BaseChange.κ cX k' (𝟙 (Spec (CommRingCat.of k')))).inv).obj (hrepQ.poincare.pullbackAlong g).L)) :
    Nonempty ((hrepQ.poincare.pullbackAlong g).L ≅
      (RelEffCartierDiv.ofPoint (baseChange R cX k') P.1 P.2).lineBundle ⊗
        (RelEffCartierDiv.ofPoint (baseChange R cX k') (sectionBaseChange k' ε).1 (sectionBaseChange k' ε).2).idealModule) := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_RelPicard_nonempty_poincare_pullbackAlong_iso_lineBundle_tensor_idealModule_of_abelJacobi_baseChange.solution
