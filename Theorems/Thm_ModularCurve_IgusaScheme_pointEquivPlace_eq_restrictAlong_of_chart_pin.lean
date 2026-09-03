import Mathlib
import Definitions.Def_ModularCurve_DRModelPackageLevel
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_RepresentsRelSubPic
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroCut
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroGroupCut
import Definitions.Def_AlgebraicGeometry_RelPicardPullback
import Definitions.Def_AlgebraicGeometry_ModulesRigidify
import Definitions.Def_AlgebraicGeometry_ModulesNormModule
import Definitions.Def_AlgebraicGeometry_SmoothProperCurveBase
import Definitions.Def_AlgebraicGeometry_RelativePic0DesignationBaseChange
import Definitions.Def_AlgebraicGeometry_RelSubPicBaseChange
import Definitions.Def_GoodReductionJacobian_RelativeGroupLawBaseChange
import Definitions.Def_AlgebraicGeometry_NeronModelEndomorphismExtension
import Definitions.Def_ModularCurve_JZeroNeronObjectAtP_LevelModel
import Definitions.Def_ModularCurve_ToricDescentData
import Definitions.Def_ModularCurve_HeckeOperator
import Definitions.Def_AlgebraicCurve_Correspondence
import Definitions.Def_AlgebraicGeometry_RelEffCartierDiv
import Definitions.Def_AlgebraicGeometry_RelEffCartierDivOfPoint
import Definitions.Def_AlgebraicGeometry_IdealSheafModule
import Definitions.Def_SheafOfModules_Monoidal
import P2M.Util
import P2M.Sol.S_ModularCurve_IgusaScheme_pointEquivPlace_eq_restrictAlong_of_chart_pin
attribute [-instance] ModularCurve.PhiGen.instNeZeroPhiGenCosetA AlgebraicCurve.CurveModel.locallyOfFiniteType_gluedToBase AlgebraicCurve.CurveModel.isFractionRing_overlap AlgebraicCurve.CurveModel.isLocallyNoetherian_glued AlgebraicCurve.CurveModel.jacobsonSpace_glued AlgebraicCurve.CurveModel.isOpenImmersion_ι₀ AlgebraicCurve.CurveModel.isIntegral_glued AlgebraicCurve.CurveModel.quasiSeparated_gluedToBase AlgebraicCurve.CurveModel.compactSpace_glued AlgebraicCurve.CurveModel.isIntegral_adjoin_chartRing AlgebraicCurve.CurveModel.isFractionRing_overlap_functionField AlgebraicCurve.CurveModel.isProper_gluedToBase AlgebraicCurve.CurveModel.isOpenImmersion_ιU AlgebraicCurve.CurveModel.isOpenImmersion_f₀ AlgebraicCurve.CurveModel.isOpenImmersion_fInf AlgebraicCurve.CurveModel.isOpenImmersion_ιInf AlgebraicCurve.CurveModel.algebra_overlap_functionField AlgebraicCurve.CurveModel.quasiCompact_gluedToBase AlgebraicCurve.CurveModel.algebraAdjoin AlgebraicCurve.CurveModel.isDedekindDomain_chartRing AlgebraicCurve.CurveModel.isIntegralClosure AlgebraicCurve.CurveModel.finite_chartRing AlgebraicCurve.CurveModel.centre_isPrime AlgebraicCurve.CurveModel.isFractionRing_chartRing AlgebraicCurve.CurveModel.finiteType_chartRing AlgebraicCurve.CurveModel.isNoetherianRing_chartRing AlgebraicCurve.CurveModel.isScalarTower_base_adjoin AlgebraicCurve.CurveModel.isScalarTower_adjoin AlgebraicCurve.CurveModel.chartRing_finitePresentation AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt
attribute [-simp] ModularCurve.CharPModel.FibreModel.mk.injEq ModularCurve.CharPModel.FibreModel.mk.sizeOf_spec ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ AlgebraicCurve.CurveModel.coe_gInf AlgebraicCurve.CurveModel.coe_tInvChart AlgebraicCurve.CurveModel.ιInf_gluedToBase_assoc AlgebraicCurve.CurveModel.ιInf_gluedToBase AlgebraicCurve.CurveModel.primeOfι₀_asIdeal AlgebraicCurve.CurveModel.coe_tChart AlgebraicCurve.CurveModel.ι₀_gluedToBase_assoc AlgebraicCurve.CurveModel.primeOfιInf_asIdeal AlgebraicCurve.CurveModel.ι₀_gluedToBase AlgebraicCurve.CurveModel.coe_tma AlgebraicCurve.CurveModel.coe_primeEquivChartPlaces AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry NeronModelInfra GoodReductionJacobian
  AlgebraicGeometry.RelPicard AlgebraicGeometry.SmoothProperCurve ModularCurve ModularCurve.DRLevel
  ModularCurve.JZeroNeronObjectAtP AlgebraicCurve
open Topology
open scoped TensorProduct

theorem ModularCurve.IgusaScheme.pointEquivPlace_eq_restrictAlong_of_chart_pin
    (M M' p : ℕ) [NeZero M] [NeZero M'] [Fact p.Prime]

    (C₂ : CurveModel (AlgebraicClosure ℚ) (modularFunctionFieldBar M'))
    (e₂ : C₂.C ⟶ pullback (IgusaScheme.igusaTo M' p) (genPt p)) [IsIso e₂] (he₂ : e₂ ≫ pullback.snd _ _ = C₂.toBase)
    (hne₂ : Nonempty (Scheme.Opens.toScheme ((e₂ ≫ pullback.fst (IgusaScheme.igusaTo M' p) (genPt p)) ⁻¹ᵁ ((IgusaScheme.ιFin M' p) ''ᵁ ⊤))))
    (pin₂ : ∀ b : ↥(IgusaScheme.chartAlgFin M' p),
      ((C₂.ffEquiv.symm
          (C₂.C.germToFunctionField
            ((e₂ ≫ pullback.fst (IgusaScheme.igusaTo M' p) (genPt p)) ⁻¹ᵁ ((IgusaScheme.ιFin M' p) ''ᵁ ⊤))
            (((e₂ ≫ pullback.fst (IgusaScheme.igusaTo M' p) (genPt p)).app ((IgusaScheme.ιFin M' p) ''ᵁ ⊤)).hom
              (((IgusaScheme.ιFin M' p).appIso ⊤).inv
                ((Scheme.ΓSpecIso (CommRingCat.of ↥(IgusaScheme.chartAlgFin M' p))).inv b))))
          : ↥(modularFunctionFieldBar M')) : LaurentSeries (AlgebraicClosure ℚ)) =
        coeffEmb (AlgebraicClosure ℚ) ((b : ↥(modularFunctionFieldFull M')) : LaurentSeries ℚ))

    (C₁ : CurveModel (AlgebraicClosure ℚ) (modularFunctionFieldBar M))
    (e₁ : C₁.C ⟶ pullback (IgusaScheme.igusaTo M p) (genPt p)) [IsIso e₁] (he₁ : e₁ ≫ pullback.snd _ _ = C₁.toBase)
    (hne₁ : Nonempty (Scheme.Opens.toScheme ((e₁ ≫ pullback.fst (IgusaScheme.igusaTo M p) (genPt p)) ⁻¹ᵁ ((IgusaScheme.ιFin M p) ''ᵁ ⊤))))
    (pin₁ : ∀ a : ↥(IgusaScheme.chartAlgFin M p),
      ((C₁.ffEquiv.symm
          (C₁.C.germToFunctionField
            ((e₁ ≫ pullback.fst (IgusaScheme.igusaTo M p) (genPt p)) ⁻¹ᵁ ((IgusaScheme.ιFin M p) ''ᵁ ⊤))
            (((e₁ ≫ pullback.fst (IgusaScheme.igusaTo M p) (genPt p)).app ((IgusaScheme.ιFin M p) ''ᵁ ⊤)).hom
              (((IgusaScheme.ιFin M p).appIso ⊤).inv
                ((Scheme.ΓSpecIso (CommRingCat.of ↥(IgusaScheme.chartAlgFin M p))).inv a))))
          : ↥(modularFunctionFieldBar M)) : LaurentSeries (AlgebraicClosure ℚ)) =
        coeffEmb (AlgebraicClosure ℚ) ((a : ↥(modularFunctionFieldFull M)) : LaurentSeries ℚ))
    (θ : ↥(IgusaScheme.chartAlgFin M p) →ₐ[R p] ↥(IgusaScheme.chartAlgFin M' p))
    (Φ : ↥(modularFunctionFieldBar M) →ₐ[AlgebraicClosure ℚ] ↥(modularFunctionFieldBar M'))
    (hΦθ : ∀ a : ↥(IgusaScheme.chartAlgFin M p),
      ((Φ ⟨coeffEmb (AlgebraicClosure ℚ) ((a : ↥(modularFunctionFieldFull M)) : LaurentSeries ℚ),
          coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (a : ↥(modularFunctionFieldFull M)).2⟩ :
          ↥(modularFunctionFieldBar M')) : LaurentSeries (AlgebraicClosure ℚ)) =
        coeffEmb (AlgebraicClosure ℚ) (((θ a : ↥(IgusaScheme.chartAlgFin M' p)) :
          ↥(modularFunctionFieldFull M')) : LaurentSeries ℚ))
    (πX : IgusaScheme M' p ⟶ IgusaScheme M p) (hπX : πX ≫ IgusaScheme.igusaTo M p = IgusaScheme.igusaTo M' p)
    (hchart : IgusaScheme.ιFin M' p ≫ πX = Spec.map (CommRingCat.ofHom θ.toRingHom) ≫ IgusaScheme.ιFin M p)

    (hint : Φ.toRingHom.IsIntegral) (hfin : FiniteAlong (AlgebraicClosure ℚ) Φ)

    (y : {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ C₂.C // q ≫ C₂.toBase = 𝟙 _})
    (x : {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ C₁.C // q ≫ C₁.toBase = 𝟙 _})
    (hyx : x.1 ≫ e₁ ≫ pullback.fst (IgusaScheme.igusaTo M p) (genPt p) =
      y.1 ≫ e₂ ≫ pullback.fst (IgusaScheme.igusaTo M' p) (genPt p) ≫ πX) :
    C₁.pointEquivPlace x = (C₂.pointEquivPlace y).restrictAlong Φ hint := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_IgusaScheme_pointEquivPlace_eq_restrictAlong_of_chart_pin.solution
