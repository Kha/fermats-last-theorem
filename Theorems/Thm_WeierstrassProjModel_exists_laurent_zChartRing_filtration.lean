import Mathlib
import Definitions.Def_WeierstrassCurve_ProjModel
import Definitions.Def_WeierstrassCurve_DrinfeldBasisGlobal
import Definitions.Def_WeierstrassCurve_PointChart
import Definitions.Def_WeierstrassCurve_SectionAtOrigin
import Definitions.Def_WeierstrassCurve_FormalGroupLaw
import P2M.Util
import P2M.Sol.S_WeierstrassProjModel_exists_laurent_zChartRing_filtration
attribute [-instance] WeierstrassProjModel.quotGradingSubmoduleDegreeZeroFiniteType WeierstrassProjModel.kw_lrChart_tensorCommRing WeierstrassProjModel.kw_lrChart_biGrading_gradedAlgebra WeierstrassProjModel.projModel_isIso_spec_mapCR WeierstrassProjModel.kw_lrSymOC_isDomain_ℬ₀ WeierstrassProjModel.isProper_projModelStrCR WeierstrassProjModel.homogeneousSubmoduleDegreeZeroFiniteType
attribute [-simp] WeierstrassProjModel.kw_lrAdd_substHom_X WeierstrassProjModel.kw_lrSym_substHom_X

set_option autoImplicit false
open AlgebraicGeometry CategoryTheory WeierstrassProjModel WeierstrassCurve.DrinfeldGlobal HomogeneousLocalization
attribute [local instance] MvPolynomial.gradedAlgebra

theorem WeierstrassProjModel.exists_laurent_zChartRing_filtration
    (T : Type) [CommRing T] (V : WeierstrassCurve T)
    (Φ : OriginChartRing V.toProjective →+* PowerSeries T)
    (hΦc : ∀ t : T, Φ (fromZeroRingHom (projModelGradingCR V.toProjective) _ (algebraMap T ((projModelGradingCR V.toProjective) 0) t)) =
      PowerSeries.C t)
    (hΦx : Φ (xOverY V.toProjective) = - PowerSeries.X) (hΦz : Φ (zOverY V.toProjective) = - V.formalW) :
    ∃ lam : ZChartRing V.toProjective →+* LaurentSeries T,
      (∀ t : T, lam (fromZeroRingHom (projModelGradingCR V.toProjective) _ (algebraMap T ((projModelGradingCR V.toProjective) 0) t)) =
        HahnSeries.C t) ∧
      lam (xOverZ V.toProjective) * HahnSeries.ofPowerSeries ℤ T (Φ (zOverY V.toProjective)) =
        HahnSeries.ofPowerSeries ℤ T (Φ (xOverY V.toProjective)) ∧
      lam (yOverZ V.toProjective) * HahnSeries.ofPowerSeries ℤ T (Φ (zOverY V.toProjective)) = 1 ∧
      (∀ a : ZChartRing V.toProjective, (∀ n : ℤ, n < -2 → (lam a).coeff n = 0) →
        ∃ c₀ c₁ : T, a = fromZeroRingHom (projModelGradingCR V.toProjective) _ (algebraMap T ((projModelGradingCR V.toProjective) 0) c₁) *
            xOverZ V.toProjective +
          fromZeroRingHom (projModelGradingCR V.toProjective) _ (algebraMap T ((projModelGradingCR V.toProjective) 0) c₀) ∧
          c₁ = (lam a).coeff (-2)) ∧
      (∀ a : ZChartRing V.toProjective, (∀ n : ℤ, n < -3 → (lam a).coeff n = 0) →
        ∃ c₀ c₁ c₂ : T, a = fromZeroRingHom (projModelGradingCR V.toProjective) _ (algebraMap T ((projModelGradingCR V.toProjective) 0) c₂) *
            yOverZ V.toProjective +
          fromZeroRingHom (projModelGradingCR V.toProjective) _ (algebraMap T ((projModelGradingCR V.toProjective) 0) c₁) *
            xOverZ V.toProjective +
          fromZeroRingHom (projModelGradingCR V.toProjective) _ (algebraMap T ((projModelGradingCR V.toProjective) 0) c₀) ∧
          c₂ = -((lam a).coeff (-3))) := by p2m_exact_reverting @_root_.P2MW.S_WeierstrassProjModel_exists_laurent_zChartRing_filtration.solution
