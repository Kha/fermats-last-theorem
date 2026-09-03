import Mathlib
import Definitions.Def_DrinfeldCurve_LocalChart
import P2M.Util
import P2M.Sol.S_DrinfeldCurve_LocalChart_ChartPresentation_mem_nonZeroDivisors_and_flat_of_mem_maximalIdeal

set_option autoImplicit false

open MvPowerSeries IsLocalRing DrinfeldCurve DrinfeldCurve.LocalChart

theorem DrinfeldCurve.LocalChart.ChartPresentation.mem_nonZeroDivisors_and_flat_of_mem_maximalIdeal
    (q : ℕ) [Fact q.Prime]
    (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    (ϖ : O) (hϖ : ϖ ∈ maximalIdeal O) (hϖ0 : ϖ ≠ 0)
    (pr : ChartPresentation q O ϖ) :
    (∀ a : O, a ≠ 0 → Ideal.Quotient.mk (Ideal.span {pr.rel}) (C a) ∈ nonZeroDivisors pr.Ring) ∧
    Module.Flat O pr.Ring ∧
    Ideal.Quotient.mk (Ideal.span {pr.rel}) (X 0) ∈ nonZeroDivisors pr.Ring ∧
    Ideal.Quotient.mk (Ideal.span {pr.rel}) (X 1) ∈ nonZeroDivisors pr.Ring := by p2m_exact_reverting @_root_.P2MW.S_DrinfeldCurve_LocalChart_ChartPresentation_mem_nonZeroDivisors_and_flat_of_mem_maximalIdeal.solution
