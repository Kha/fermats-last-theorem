import Mathlib.RingTheory.MvPowerSeries.Rename
import Definitions.Def_DrinfeldCurve_LocalChart
import P2M.Util
import P2M.Sol.S_DrinfeldCurve_LocalChart_ChartPresentation_exists_swap_ringEquiv

set_option autoImplicit false

open MvPowerSeries IsLocalRing DrinfeldCurve DrinfeldCurve.LocalChart

theorem DrinfeldCurve.LocalChart.ChartPresentation.exists_swap_ringEquiv
    (q : ℕ) [Fact q.Prime] (O : Type) [CommRing O] (ϖ : O) (pr : ChartPresentation q O ϖ) :
    ∃ (pr' : ChartPresentation q O ϖ) (e : pr.Ring ≃+* pr'.Ring),
      (∀ o : O, e (Ideal.Quotient.mk _ (C o)) = Ideal.Quotient.mk _ (C o)) ∧
      e (Ideal.Quotient.mk _ (X 0)) = Ideal.Quotient.mk _ (X 1) ∧
      e (Ideal.Quotient.mk _ (X 1)) = Ideal.Quotient.mk _ (X 0) ∧
      pr'.v = MvPowerSeries.rename (Equiv.swap (0 : Fin 2) 1) pr.v ∧
      pr'.u = -MvPowerSeries.rename (Equiv.swap (0 : Fin 2) 1) pr.u ∧
      pr'.f = -MvPowerSeries.rename (Equiv.swap (0 : Fin 2) 1) pr.f := by p2m_exact_reverting @_root_.P2MW.S_DrinfeldCurve_LocalChart_ChartPresentation_exists_swap_ringEquiv.solution
