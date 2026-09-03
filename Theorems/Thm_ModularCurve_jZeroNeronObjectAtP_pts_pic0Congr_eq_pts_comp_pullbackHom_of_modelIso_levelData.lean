import Mathlib
import Definitions.Def_ModularCurve_XHDRModelAtP
import Definitions.Def_ModularCurve_JHNeronObjectAtP
import Definitions.Def_AlgebraicCurve_GluedPic0Functoriality
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_RepresentsRelSubPic
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroCut
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroGroupCut
import Definitions.Def_AlgebraicGeometry_RelativePic0DesignationBaseChange
import Definitions.Def_AlgebraicGeometry_RelSubPicBaseChange
import Definitions.Def_SheafOfModules_Monoidal
import Definitions.Def_AlgebraicGeometry_IdealSheafModule
import Definitions.Def_AlgebraicGeometry_RelEffCartierDiv
import Definitions.Def_AlgebraicGeometry_RelEffCartierDivOfPoint
import Definitions.Def_ModularCurve_XHOperators
import Definitions.Def_ModularCurve_CharacterLatticePairings
import Definitions.Def_EllipticCurve_FrobeniusTrace
import Definitions.Def_FLTPrelim_Ramification
import Definitions.Def_ModularCurve_JZeroNeronObjectAtP
import Definitions.Def_AlgebraicCurve_CurveModel
import Definitions.Def_ModularCurve_JZeroSemistableSpecialization
import Definitions.Def_ModularCurve_HeckeModule
import Definitions.Def_ValuationSubring_ReduceAt
import Definitions.Def_WeierstrassCurve_ReductionMap
import Definitions.Def_ModularCurve_SupersingularNodePlaces
import Definitions.Def_ModularCurve_CoeffSemilinearAut
import Definitions.Def_ModularCurve_PlaceSpecialization
import Definitions.Def_ModularCurve_GlueData
import Definitions.Def_ModularCurve_ProlongationTuple
import Definitions.Def_AlgebraicCurve_Pic0Congr
import Definitions.Def_ModularCurve_DRModelPackageLevel
import Definitions.Def_AlgebraicGeometry_SmoothProperCurveBase
import Definitions.Def_AlgebraicGeometry_RelPicardPullback
import Definitions.Def_AlgebraicGeometry_ModulesRigidify
import P2M.Util
import P2M.Sol.S_ModularCurve_jZeroNeronObjectAtP_pts_pic0Congr_eq_pts_comp_pullbackHom_of_modelIso_levelData
attribute [-instance] PresheafOfModules.ExteriorPower.instModulePresheafAb AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instNeg AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instSMulInt AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instAddCommGroup AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instAdd AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instSub AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instModuleCarrierObjOppositeOpensCarrierCarrierCommRingCatPresheafOpOpensTop AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instSMulCarrierObjOppositeOpensCarrierCarrierCommRingCatPresheafOpOpensTop AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instSMulNat AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instZero AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions
attribute [-simp] AlgebraicGeometry.Scheme.Modules.normModuleFunctor_obj AlgebraicGeometry.Scheme.Modules.exteriorPower_obj PresheafOfModules.exteriorPower_map_ιMulti PresheafOfModules.ExteriorPower.appₗ_apply AlgebraicGeometry.RelPicard.rigSection_snd AlgebraicGeometry.RelPicard.RigidifiedLineBundle.ofInvertible_L AlgebraicGeometry.RelPicard.rigSection_snd_assoc AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.sub_app AlgebraicGeometry.Scheme.IdealSheafData.sres_sresTop AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.add_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.mk.sizeOf_spec AlgebraicGeometry.Scheme.IdealSheafData.coe_resLE AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.smul_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.coe_ofLE_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.ideal_range AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.zero_app AlgebraicGeometry.Scheme.IdealSheafData.sres_sres AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.comp_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.neg_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.id_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.coe_mulRight_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.nsmul_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.mk.injEq AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.zsmul_app AlgebraicGeometry.Scheme.Modules.toUnitSection_ofUnitSection AlgebraicGeometry.Scheme.Modules.pullbackSection_def AlgebraicGeometry.Scheme.Modules.ofUnitSection_toUnitSection AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry NeronModelInfra GoodReductionJacobian
  AlgebraicCurve IsLocalRing ModularCurve ModularCurve.JZeroNeronObjectAtP ModularCurve.DRLevel
  AlgebraicGeometry.RelPicard AlgebraicGeometry.SmoothProperCurve ModularCurve.CharacterLattice
open scoped MatrixGroups

set_option synthInstance.maxHeartbeats 400000 in
set_option maxHeartbeats 1600000 in

theorem ModularCurve.jZeroNeronObjectAtP_pts_pic0Congr_eq_pts_comp_pullbackHom_of_modelIso_levelData
    (N₀ p : ℕ) [NeZero N₀] [Fact p.Prime] [NeZero p] (hpN₀ : ¬ p ∣ N₀) [NeZero (N₀ * p)]
    (hpM : p ∣ N₀ * p) (hpM2 : ¬ p ^ 2 ∣ N₀ * p) [NeZero (N₀ * p / p)]
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p) [IsAlgClosed (ResidueField ↥A)] :
    haveI : CharP (ResidueField ↥A) p := ValuationSubring.charP_residueField_of_liesOverPrime_def (Fact.out) hA
    letI := heckeModuleBar (N₀ * p)
    letI := heckeModuleBar N₀
    letI := instDecidableEqResidueFieldSemistable A
    letI := instAlgebraResidueFieldModularFunctionFieldCSemistable A N₀
    letI : Algebra (ResidueField ↥A) ↥(modularFunctionFieldFullC (ResidueField ↥A) N₀) :=
      (modularFunctionFieldFullC (ResidueField ↥A) N₀).algebra

    ∀ (hj : jqModC ℚ ∈ qExpFunctionFieldC ℚ (⊤ : Subgroup SL(2, ℤ)))
    (𝔛 : XHDRModelAtP p (N₀ * p) ⊤ hpM hj)
    (Λ : JHNeronObjectAtP.LevelData p (N₀ * p) ⊤ hpM A) (O : JHNeronObjectAtP p (N₀ * p) ⊤ hpM A hA Λ)
    (hD : RepresentsRelSubPic (XHDRLevel.toBase p (XHDRLevel.ΓM (N₀ * p) ⊤) hj) 𝔛.εinf (algEquivZeroCut (XHDRLevel.toBase p (XHDRLevel.ΓM (N₀ * p) ⊤) hj) 𝔛.εinf) (⟨O.G, O.g, (O.L.one (𝟙 (Spec (CommRingCat.of (R p))))).1, (O.L.one (𝟙 (Spec (CommRingCat.of (R p))))).2⟩ : RelativePic0Designation (R p) (XHDRLevel.toBase p (XHDRLevel.ΓM (N₀ * p) ⊤) hj)))
      (hDQT : RepresentsRelSubPic (baseChange (R p) (XHDRLevel.toBase p (XHDRLevel.ΓM (N₀ * p) ⊤) hj) ℚ) (sectionBaseChange ℚ 𝔛.εinf)
          (algEquivZeroCut (baseChange (R p) (XHDRLevel.toBase p (XHDRLevel.ΓM (N₀ * p) ⊤) hj) ℚ) (sectionBaseChange ℚ 𝔛.εinf)) (((⟨O.G, O.g, (O.L.one (𝟙 (Spec (CommRingCat.of (R p))))).1, (O.L.one (𝟙 (Spec (CommRingCat.of (R p))))).2⟩ : RelativePic0Designation (R p) (XHDRLevel.toBase p (XHDRLevel.ΓM (N₀ * p) ⊤) hj))).baseChange ℚ))
      (_ : IsSeparated (baseChange (R p) (XHDRLevel.toBase p (XHDRLevel.ΓM (N₀ * p) ⊤) hj) ℚ))
      (ajQT : SchemeHomOver (baseChange (R p) (XHDRLevel.toBase p (XHDRLevel.ΓM (N₀ * p) ⊤) hj) ℚ) (((⟨O.G, O.g, (O.L.one (𝟙 (Spec (CommRingCat.of (R p))))).1, (O.L.one (𝟙 (Spec (CommRingCat.of (R p))))).2⟩ : RelativePic0Designation (R p) (XHDRLevel.toBase p (XHDRLevel.ΓM (N₀ * p) ⊤) hj))).baseChange ℚ).toBase)
      (kQT : pullback (XHDRLevel.toBase p (XHDRLevel.ΓM (N₀ * p) ⊤) hj) (genPt p) ⟶ pullback (XHDRLevel.toBase p (XHDRLevel.ΓM (N₀ * p) ⊤) hj) (specMap (R p) ℚ))
      (ajbarT : 𝔛.Meta.C ⟶ O.G)
      (εbarT : {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ 𝔛.Meta.C // q ≫ 𝔛.Meta.toBase = 𝟙 _})
    (HAJ :

      Nonempty (hDQT.poincare.L ≅ (BaseChange.ofR (XHDRLevel.toBase p (XHDRLevel.ΓM (N₀ * p) ⊤) hj) 𝔛.εinf ℚ
        (hD.poincare.pullbackAlong ⟨pullback.fst O.g (specMap (R p) ℚ), pullback.condition⟩)).L) ∧

      (sectionBaseChange ℚ 𝔛.εinf).1 ≫ ajQT.1 = (((⟨O.G, O.g, (O.L.one (𝟙 (Spec (CommRingCat.of (R p))))).1, (O.L.one (𝟙 (Spec (CommRingCat.of (R p))))).2⟩ : RelativePic0Designation (R p) (XHDRLevel.toBase p (XHDRLevel.ΓM (N₀ * p) ⊤) hj))).baseChange ℚ).zeroSection ∧

      (∀ (K : Type) [Field K] (t : Spec (CommRingCat.of K) ⟶ Spec (CommRingCat.of ℚ))
          (x : SchemeHomOver t (baseChange (R p) (XHDRLevel.toBase p (XHDRLevel.ΓM (N₀ * p) ⊤) hj) ℚ)),
        Nonempty ((hDQT.poincare.pullbackAlong
            ⟨x.1 ≫ ajQT.1, (Category.assoc _ _ _).trans ((congrArg (x.1 ≫ ·) ajQT.2).trans x.2)⟩).L ≅
          (RelEffCartierDiv.ofPoint (baseChange (R p) (XHDRLevel.toBase p (XHDRLevel.ΓM (N₀ * p) ⊤) hj) ℚ) x.1 x.2).lineBundle ⊗
            (RelEffCartierDiv.ofPoint (baseChange (R p) (XHDRLevel.toBase p (XHDRLevel.ΓM (N₀ * p) ⊤) hj) ℚ) (t ≫ (sectionBaseChange ℚ 𝔛.εinf).1)
              ((Category.assoc _ _ _).trans ((congrArg (t ≫ ·) (sectionBaseChange ℚ 𝔛.εinf).2).trans
                (Category.comp_id t)))).idealModule)) ∧

      kQT ≫ pullback.fst (XHDRLevel.toBase p (XHDRLevel.ΓM (N₀ * p) ⊤) hj) (specMap (R p) ℚ) = pullback.fst (XHDRLevel.toBase p (XHDRLevel.ΓM (N₀ * p) ⊤) hj) (genPt p) ∧
      kQT ≫ pullback.snd (XHDRLevel.toBase p (XHDRLevel.ΓM (N₀ * p) ⊤) hj) (specMap (R p) ℚ) = pullback.snd (XHDRLevel.toBase p (XHDRLevel.ΓM (N₀ * p) ⊤) hj) (genPt p) ≫ specMap ℚ (AlgebraicClosure ℚ) ∧

      ajbarT = 𝔛.eeta ≫ kQT ≫ ajQT.1 ≫ pullback.fst O.g (specMap (R p) ℚ) ∧
      ajbarT ≫ O.g = 𝔛.Meta.toBase ≫ genPt p ∧
      εbarT.1 ≫ 𝔛.eeta ≫ pullback.fst (XHDRLevel.toBase p (XHDRLevel.ΓM (N₀ * p) ⊤) hj) (genPt p) = genPt p ≫ 𝔛.εinf.1 ∧
      εbarT.1 ≫ ajbarT = genPt p ≫ (O.L.one (𝟙 (Spec (CommRingCat.of (R p))))).1 ∧

      (∀ x y : JH (N₀ * p) ⊤,
        O.pts (x + y) = (RepresentsRelSubPic.relativeGroupLaw (P := algEquivZeroGroupCut _ _) hD).mul _ (O.pts x) (O.pts y)) ∧

      (∀ (x s : {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ 𝔛.Meta.C // q ≫ 𝔛.Meta.toBase = 𝟙 _}),
        s.1 ≫ 𝔛.eeta ≫ pullback.fst (XHDRLevel.toBase p (XHDRLevel.ΓM (N₀ * p) ⊤) hj) (genPt p) = genPt p ≫ 𝔛.εinf.1 →
        ∃ Dv : Divisor.degZero (K := AlgebraicClosure ℚ) (F := ↥(xHFunctionFieldBar (N₀ * p) ⊤)),
          (Dv : Divisor (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar (N₀ * p) ⊤)) =
            Finsupp.single (𝔛.Meta.pointEquivPlace x) 1 - Finsupp.single (𝔛.Meta.pointEquivPlace s) 1 ∧
          (O.pts (Pic0.mk Dv)).1 = x.1 ≫ ajbarT)),
    ∀ (Λ₀ : JZeroNeronObjectAtP.LevelData N₀ p A) (𝔓 : DRModelPackageLevel N₀ p hpN₀)
      (O₀ : JZeroNeronObjectAtP N₀ p hpN₀ A hA Λ₀)
      (hD₀ : RepresentsRelSubPic (toBase N₀ p) 𝔓.εinf (algEquivZeroCut (toBase N₀ p) 𝔓.εinf) (⟨O₀.G, O₀.g, (O₀.L.one (𝟙 (Spec (CommRingCat.of (R p))))).1, (O₀.L.one (𝟙 (Spec (CommRingCat.of (R p))))).2⟩ : RelativePic0Designation (R p) (toBase N₀ p)))
        (hDQ₀ : RepresentsRelSubPic (baseChange (R p) (toBase N₀ p) ℚ) (sectionBaseChange ℚ 𝔓.εinf)
            (algEquivZeroCut (baseChange (R p) (toBase N₀ p) ℚ) (sectionBaseChange ℚ 𝔓.εinf)) ((⟨O₀.G, O₀.g, (O₀.L.one (𝟙 (Spec (CommRingCat.of (R p))))).1, (O₀.L.one (𝟙 (Spec (CommRingCat.of (R p))))).2⟩ : RelativePic0Designation (R p) (toBase N₀ p)).baseChange ℚ))
        (hPQ₀ : Nonempty (hDQ₀.poincare.L ≅ (BaseChange.ofR (toBase N₀ p) 𝔓.εinf ℚ
            (hD₀.poincare.pullbackAlong ⟨pullback.fst O₀.g (specMap (R p) ℚ), pullback.condition⟩)).L))
        (hsep₀ : IsSeparated (baseChange (R p) (toBase N₀ p) ℚ))

        (ajQ₀ : SchemeHomOver (baseChange (R p) (toBase N₀ p) ℚ) ((⟨O₀.G, O₀.g, (O₀.L.one (𝟙 (Spec (CommRingCat.of (R p))))).1, (O₀.L.one (𝟙 (Spec (CommRingCat.of (R p))))).2⟩ : RelativePic0Designation (R p) (toBase N₀ p)).baseChange ℚ).toBase)
        (hajQε₀ : (sectionBaseChange ℚ 𝔓.εinf).1 ≫ ajQ₀.1 = ((⟨O₀.G, O₀.g, (O₀.L.one (𝟙 (Spec (CommRingCat.of (R p))))).1, (O₀.L.one (𝟙 (Spec (CommRingCat.of (R p))))).2⟩ : RelativePic0Designation (R p) (toBase N₀ p)).baseChange ℚ).zeroSection)
        (hajQ₀ : ∀ (K : Type) [Field K] (t : Spec (CommRingCat.of K) ⟶ Spec (CommRingCat.of ℚ))
            (x : SchemeHomOver t (baseChange (R p) (toBase N₀ p) ℚ)),
          Nonempty ((hDQ₀.poincare.pullbackAlong
              ⟨x.1 ≫ ajQ₀.1, (Category.assoc _ _ _).trans ((congrArg (x.1 ≫ ·) ajQ₀.2).trans x.2)⟩).L ≅
            (RelEffCartierDiv.ofPoint (baseChange (R p) (toBase N₀ p) ℚ) x.1 x.2).lineBundle ⊗
              (RelEffCartierDiv.ofPoint (baseChange (R p) (toBase N₀ p) ℚ) (t ≫ (sectionBaseChange ℚ 𝔓.εinf).1)
                ((Category.assoc _ _ _).trans ((congrArg (t ≫ ·) (sectionBaseChange ℚ 𝔓.εinf).2).trans
                  (Category.comp_id t)))).idealModule))

        (kQ₀ : pullback (toBase N₀ p) (genPt p) ⟶ pullback (toBase N₀ p) (specMap (R p) ℚ))
        (hkQ₁₀ : kQ₀ ≫ pullback.fst (toBase N₀ p) (specMap (R p) ℚ) = pullback.fst (toBase N₀ p) (genPt p))
        (hkQ₂₀ : kQ₀ ≫ pullback.snd (toBase N₀ p) (specMap (R p) ℚ) = pullback.snd (toBase N₀ p) (genPt p) ≫ specMap ℚ (AlgebraicClosure ℚ))

        (ajbar₀ : 𝔓.Meta.C ⟶ O₀.G) (hajbar₀ : ajbar₀ = 𝔓.eeta ≫ kQ₀ ≫ ajQ₀.1 ≫ pullback.fst O₀.g (specMap (R p) ℚ))
        (hajbar_over₀ : ajbar₀ ≫ O₀.g = 𝔓.Meta.toBase ≫ genPt p)
        (εbar₀ : {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ 𝔓.Meta.C // q ≫ 𝔓.Meta.toBase = 𝟙 _})
        (hεbar₀ : εbar₀.1 ≫ 𝔓.eeta ≫ pullback.fst (toBase N₀ p) (genPt p) = genPt p ≫ 𝔓.εinf.1) (hεbar_aj₀ : εbar₀.1 ≫ ajbar₀ = genPt p ≫ (⟨O₀.G, O₀.g, (O₀.L.one (𝟙 (Spec (CommRingCat.of (R p))))).1, (O₀.L.one (𝟙 (Spec (CommRingCat.of (R p))))).2⟩ : RelativePic0Designation (R p) (toBase N₀ p)).zeroSection)
      (hpts_law₀ : ∀ x y : JZero (N₀ * p),
          O₀.pts (x + y) = (RepresentsRelSubPic.relativeGroupLaw (P := algEquivZeroGroupCut _ _) hD₀).mul _ (O₀.pts x) (O₀.pts y))
      (hAJ₀ : ∀ (x s : {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ 𝔓.Meta.C // q ≫ 𝔓.Meta.toBase = 𝟙 _}),
          s.1 ≫ 𝔓.eeta ≫ pullback.fst (toBase N₀ p) (genPt p) = genPt p ≫ 𝔓.εinf.1 →
          ∃ Dv : Divisor.degZero (K := AlgebraicClosure ℚ) (F := modularFunctionFieldBar (N₀ * p)),
            (Dv : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (N₀ * p))) =
              Finsupp.single (𝔓.Meta.pointEquivPlace x) 1 - Finsupp.single (𝔓.Meta.pointEquivPlace s) 1 ∧
            (O₀.pts (Pic0.mk Dv)).1 = x.1 ≫ ajbar₀),
    ∀ (hF : xHFunctionFieldBar (N₀ * p) ⊤ = modularFunctionFieldBar (N₀ * p))
      (φ : XHDRLevel.X p (XHDRLevel.ΓM (N₀ * p) ⊤) hj ≅ DRLevel.X N₀ p)
      (hφb : φ.hom ≫ DRLevel.toBase N₀ p = XHDRLevel.toBase p (XHDRLevel.ΓM (N₀ * p) ⊤) hj)
      (hφb' : φ.inv ≫ XHDRLevel.toBase p (XHDRLevel.ΓM (N₀ * p) ⊤) hj = DRLevel.toBase N₀ p)
      (hφε : 𝔛.εinf.1 ≫ φ.hom = 𝔓.εinf.1) (hφε' : 𝔓.εinf.1 ≫ φ.inv = 𝔛.εinf.1)
      (_ : ∀ (y : {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ 𝔛.Meta.C // q ≫ 𝔛.Meta.toBase = 𝟙 _})
          (y₀ : {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ 𝔓.Meta.C // q ≫ 𝔓.Meta.toBase = 𝟙 _}),
        y.1 ≫ 𝔛.eeta ≫ pullback.fst _ _ ≫ φ.hom = y₀.1 ≫ 𝔓.eeta ≫ pullback.fst (DRLevel.toBase N₀ p) (genPt p) →
        𝔓.Meta.pointEquivPlace y₀ =
          Place.congrRingEquiv (IntermediateField.equivOfEq hF).toRingEquiv (fun a => (IntermediateField.equivOfEq hF).commutes a)
            (𝔛.Meta.pointEquivPlace y)),
    ∀ (e : JH (N₀ * p) ⊤ ≃+ JZero (N₀ * p))
      (_ : ∀ x : JH (N₀ * p) ⊤,
        e x = Pic0.congr (IntermediateField.equivOfEq hF).toRingEquiv (fun a => (IntermediateField.equivOfEq hF).commutes a) x),
    ∀ y : JH (N₀ * p) ⊤,
      (O₀.pts (e y)).1 = (O.pts y).1 ≫ (RepresentsRelSubPic.pullbackHom φ.inv hφb' hφε' hD hD₀).1 := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_jZeroNeronObjectAtP_pts_pic0Congr_eq_pts_comp_pullbackHom_of_modelIso_levelData.solution
