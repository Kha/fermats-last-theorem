import Definitions.Def_WeierstrassCurve_ProjModel
import Definitions.Def_WeierstrassCurve_DrinfeldBasisGlobal
import Definitions.Def_WeierstrassCurve_PointChart
import Definitions.Def_WeierstrassCurve_SectionAtOrigin
import Definitions.Def_WeierstrassCurve_ProjModel_GroupLawVocabulary
import Definitions.Def_WeierstrassCurve_DrinfeldLevelFunctor
import P2M.Util
import P2M.Sol.S_WeierstrassCurve_DrinfeldGlobal_exists_ringEquiv_originChartRing_quotient_span_xOverY_pow_zOverY_pow_adjoinRoot_X_pow
attribute [-simp] WeierstrassCurve.wIter_zero MvPowerSeries.kw_coeff_pderiv FormalGroup.nthSeries_zero FormalGroup.evalNSMul_zero

set_option autoImplicit false
open AlgebraicGeometry CategoryTheory NeronModelInfra WeierstrassProjModel WeierstrassCurve.DrinfeldGlobal
attribute [local instance] MvPolynomial.gradedAlgebra

theorem WeierstrassCurve.DrinfeldGlobal.exists_ringEquiv_originChartRing_quotient_span_xOverY_pow_zOverY_pow_adjoinRoot_X_pow
    (q : ℕ) (T : Type) [CommRing T] (W : WeierstrassCurve T) :
    ∃ e : (OriginChartRing W.toProjective ⧸
          Ideal.span {xOverY W.toProjective ^ q, zOverY W.toProjective ^ q}) ≃+* AdjoinRoot ((Polynomial.X : Polynomial T) ^ q),
      (∀ t : T, e (Ideal.Quotient.mk _ (HomogeneousLocalization.fromZeroRingHom (projModelGradingCR W.toProjective) _ (algebraMap T ((projModelGradingCR W.toProjective) 0) t))) =
        algebraMap T (AdjoinRoot ((Polynomial.X : Polynomial T) ^ q)) t) ∧
      e (Ideal.Quotient.mk _ (xOverY W.toProjective)) = AdjoinRoot.root ((Polynomial.X : Polynomial T) ^ q) := by p2m_exact_reverting @_root_.P2MW.S_WeierstrassCurve_DrinfeldGlobal_exists_ringEquiv_originChartRing_quotient_span_xOverY_pow_zOverY_pow_adjoinRoot_X_pow.solution
