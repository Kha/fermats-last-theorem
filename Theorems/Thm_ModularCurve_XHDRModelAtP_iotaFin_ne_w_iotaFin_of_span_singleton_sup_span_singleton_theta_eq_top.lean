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
import P2M.Sol.S_ModularCurve_XHDRModelAtP_iotaFin_ne_w_iotaFin_of_span_singleton_sup_span_singleton_theta_eq_top

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry AlgebraicGeometry.RelPicard AlgebraicCurve
  AlgebraicGeometry.SmoothProperCurve NeronModelInfra GoodReductionJacobian ModularCurve ModularCurve.XHDRLevel
open scoped MatrixGroups Polynomial

set_option synthInstance.maxHeartbeats 400000 in

theorem ModularCurve.XHDRModelAtP.iotaFin_ne_w_iotaFin_of_span_singleton_sup_span_singleton_theta_eq_top
    (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M) (hpM2 : ¬ p ^ 2 ∣ M)
    (hHp : ∀ u : (ZMod M)ˣ, ZMod.unitsMap (Nat.div_dvd_of_dvd hpM) u = 1 → u ∈ H)
    (hj : jqModC ℚ ∈ qExpFunctionFieldC ℚ (⊤ : Subgroup SL(2, ℤ)))
    (𝔛 : XHDRModelAtP p M H hpM hj)
    (theta : ↥(chartAlgFin p (ΓM M H) hj) ≃ₐ[R p] ↥(chartAlgFin p (ΓM M H) hj))
    (hwchart : ιFin p (ΓM M H) hj ≫ 𝔛.w.hom = Spec.map (CommRingCat.ofHom theta.toRingEquiv.toRingHom) ≫ ιFin p (ΓM M H) hj)
    (a b : ↥(chartAlgFin p (ΓM M H) hj))
    (hab : Ideal.span {b} ⊔ Ideal.span {theta a} = ⊤)
    (𝔮 𝔮' : PrimeSpectrum ↥(chartAlgFin p (ΓM M H) hj)) (ha : a ∈ 𝔮.asIdeal) (hb : b ∈ 𝔮'.asIdeal) :
    (ιFin p (ΓM M H) hj).base 𝔮 ≠ 𝔛.w.hom.base ((ιFin p (ΓM M H) hj).base 𝔮') := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_XHDRModelAtP_iotaFin_ne_w_iotaFin_of_span_singleton_sup_span_singleton_theta_eq_top.solution
