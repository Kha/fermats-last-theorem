import Mathlib
import Definitions.Def_DrinfeldCurve_LocalChart
import P2M.Util
import P2M.Sol.S_DrinfeldCurve_LocalChart_mem_span_pow_of_mul_mem_span_pow_succ_of_sub_drinfeldForm_mem_pow

set_option autoImplicit false

theorem DrinfeldCurve.LocalChart.mem_span_pow_of_mul_mem_span_pow_succ_of_sub_drinfeldForm_mem_pow
    (q : ℕ) [Fact q.Prime]
    (W : Type) [CommRing W] [IsDomain W] [IsDiscreteValuationRing W]
    [IsAdicComplete (IsLocalRing.maximalIdeal W) W]
    (π : W) (hπ : IsLocalRing.maximalIdeal W = Ideal.span {π})
    (T : W) (hT : T ∈ IsLocalRing.maximalIdeal W) (hT0 : T ≠ 0)
    (c : W) (hcT : c = T ^ (q + 1))
    (f u v : MvPowerSeries (Fin 2) W) (hu : IsUnit u) (hv : IsUnit v)
    (hf : f - DrinfeldCurve.LocalChart.drinfeldForm q W ∈
      (Ideal.span {(MvPowerSeries.X 0 : MvPowerSeries (Fin 2) W), MvPowerSeries.X 1}) ^ (q + 2)) :
    ∀ (n : ℕ) (s : MvPowerSeries (Fin 2) W ⧸ Ideal.span {MvPowerSeries.C c * v - f * u}),
      s * Ideal.Quotient.mk (Ideal.span {MvPowerSeries.C c * v - f * u}) (MvPowerSeries.C T) ∈
          (Ideal.span {Ideal.Quotient.mk (Ideal.span {MvPowerSeries.C c * v - f * u}) (MvPowerSeries.C T),
            Ideal.Quotient.mk (Ideal.span {MvPowerSeries.C c * v - f * u}) (MvPowerSeries.X 0),
            Ideal.Quotient.mk (Ideal.span {MvPowerSeries.C c * v - f * u}) (MvPowerSeries.X 1)}) ^ (n + 1) →
      s ∈ (Ideal.span {Ideal.Quotient.mk (Ideal.span {MvPowerSeries.C c * v - f * u}) (MvPowerSeries.C T),
            Ideal.Quotient.mk (Ideal.span {MvPowerSeries.C c * v - f * u}) (MvPowerSeries.X 0),
            Ideal.Quotient.mk (Ideal.span {MvPowerSeries.C c * v - f * u}) (MvPowerSeries.X 1)}) ^ n := by p2m_exact_reverting @_root_.P2MW.S_DrinfeldCurve_LocalChart_mem_span_pow_of_mul_mem_span_pow_succ_of_sub_drinfeldForm_mem_pow.solution
