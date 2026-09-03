import Mathlib
import Definitions.Def_AlgebraicGeometry_NeronModelPropertyBundleCarrier
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_RepresentsRelSubPic
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroCut
import Definitions.Def_AlgebraicGeometry_RelPicardChartSections
import Definitions.Def_AlgebraicGeometry_SmoothProperCurveBase
import Definitions.Def_AlgebraicGeometry_TwoAffineOpenCover
import Definitions.Def_AlgebraicGeometry_TwoChartCechSectionsOf
import Definitions.Def_JacJ1Iface
import Definitions.Def_SheafOfModules_Monoidal
import Definitions.Def_ModularCurve_XHDRModelAtP
import Definitions.Def_AlgebraicGeometry_RelPicardPullback
import P2M.Util
import P2M.Sol.S_ModularCurve_XHDRModelAtP_range_epsInf_inter_range_iotaFin_eq_empty_and_range_epsZero_inter_range_iotaFin_eq_empty
attribute [-simp] ModularCurve.qInftyPlaceBar_toValuationSubring ModularCurve.qSeriesBar_zero ModularCurve.qSeriesBar_add ModularCurve.cuspInftyFull_toValuationSubring ModularCurve.qInftyPlaceRat_toValuationSubring ModularCurve.qSeriesBar_mul ModularCurve.qSeriesBar_div ModularCurve.qSeriesBar_eq_zero_iff ModularCurve.coe_uniformizerBar ModularCurve.qSeriesBar_pow ModularCurve.cuspInfty_toValuationSubring ModularCurve.qSeriesBar_one ModularCurve.qSeriesBar_inv ModularCurve.qSeriesBar_sub ModularCurve.qSeriesBar_neg

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry AlgebraicGeometry.RelPicard AlgebraicCurve
  AlgebraicGeometry.SmoothProperCurve NeronModelInfra GoodReductionJacobian ModularCurve ModularCurve.XHDRLevel
open scoped MatrixGroups Polynomial

set_option synthInstance.maxHeartbeats 400000 in

theorem ModularCurve.XHDRModelAtP.range_epsInf_inter_range_iotaFin_eq_empty_and_range_epsZero_inter_range_iotaFin_eq_empty
    (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M) (hpM2 : ¬ p ^ 2 ∣ M)
    (hHp : ∀ u : (ZMod M)ˣ, ZMod.unitsMap (Nat.div_dvd_of_dvd hpM) u = 1 → u ∈ H)
    (hj : jqModC ℚ ∈ qExpFunctionFieldC ℚ (⊤ : Subgroup SL(2, ℤ)))
    (𝔛 : XHDRModelAtP p M H hpM hj)
    (hwfin : 𝔛.w.hom ⁻¹ᵁ (ιFin p (ΓM M H) hj).opensRange = (ιFin p (ΓM M H) hj).opensRange) :
    Set.range 𝔛.εinf.1.base ∩ Set.range (ιFin p (ΓM M H) hj).base = ∅ ∧
    Set.range 𝔛.εzero.1.base ∩ Set.range (ιFin p (ΓM M H) hj).base = ∅ := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_XHDRModelAtP_range_epsInf_inter_range_iotaFin_eq_empty_and_range_epsZero_inter_range_iotaFin_eq_empty.solution
