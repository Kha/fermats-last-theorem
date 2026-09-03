import Mathlib
import Definitions.Def_AlgebraicCurve_TwoChartIntegralModel
import Definitions.Def_ModularCurve_IgusaScheme
import P2M.Util
import P2M.Sol.S_AlgebraicCurve_TwoChartIntegralModel_isReduced_pullback_toBase_of_isReduced_chartAlg_quotient_span_natCast

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicCurve

theorem AlgebraicCurve.TwoChartIntegralModel.isReduced_pullback_toBase_of_isReduced_chartAlg_quotient_span_natCast
    (p : ℕ) [Fact p.Prime] (F : Type) [Field F] [Algebra ↥(GaloisRep.ratLocalizedAt p) F] (j : F) [Fact (j ≠ 0)]
    (hFin : IsReduced (↥(TwoChartIntegralModel.chartAlgFin ↥(GaloisRep.ratLocalizedAt p) F j) ⧸
      Ideal.span {((p : ℕ) : ↥(TwoChartIntegralModel.chartAlgFin ↥(GaloisRep.ratLocalizedAt p) F j))}))
    (hInf : IsReduced (↥(TwoChartIntegralModel.chartAlgInf ↥(GaloisRep.ratLocalizedAt p) F j) ⧸
      Ideal.span {((p : ℕ) : ↥(TwoChartIntegralModel.chartAlgInf ↥(GaloisRep.ratLocalizedAt p) F j))}))
    (L : Type) [Field L] (toL : ↥(GaloisRep.ratLocalizedAt p) →+* L) :
    IsReduced (pullback (TwoChartIntegralModel.toBase ↥(GaloisRep.ratLocalizedAt p) F j) (Spec.map (CommRingCat.ofHom toL))) := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicCurve_TwoChartIntegralModel_isReduced_pullback_toBase_of_isReduced_chartAlg_quotient_span_natCast.solution
