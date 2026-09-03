import Mathlib
import Definitions.Def_DrinfeldCurve_LocalChart
import P2M.Util
import P2M.Sol.S_DrinfeldCurve_LocalChart_mem_of_mk_sum_C_mul_X_mem_span_sq

set_option autoImplicit false

theorem DrinfeldCurve.LocalChart.mem_of_mk_sum_C_mul_X_mem_span_sq
    (q : ℕ) [Fact q.Prime]
    (W : Type) [CommRing W] (I : Ideal W)
    (t : W) (ht : t ∈ I) (f u v : MvPowerSeries (Fin 2) W)
    (hf : f - DrinfeldCurve.LocalChart.drinfeldForm q W ∈
      (Ideal.span {(MvPowerSeries.X 0 : MvPowerSeries (Fin 2) W), MvPowerSeries.X 1}) ^ (q + 2))
    (a : Fin 2 → W)
    (h : Ideal.Quotient.mk (Ideal.span {MvPowerSeries.C t * v - f * u})
        (∑ ii : Fin 2, MvPowerSeries.C (a ii) * MvPowerSeries.X ii) ∈
      (Ideal.span {Ideal.Quotient.mk (Ideal.span {MvPowerSeries.C t * v - f * u}) (MvPowerSeries.X 0),
        Ideal.Quotient.mk (Ideal.span {MvPowerSeries.C t * v - f * u}) (MvPowerSeries.X 1)}) ^ 2) :
    ∀ ii : Fin 2, a ii ∈ I := by p2m_exact_reverting @_root_.P2MW.S_DrinfeldCurve_LocalChart_mem_of_mk_sum_C_mul_X_mem_span_sq.solution
