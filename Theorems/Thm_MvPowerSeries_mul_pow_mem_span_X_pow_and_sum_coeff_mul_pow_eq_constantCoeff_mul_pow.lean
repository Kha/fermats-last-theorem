import Mathlib
import P2M.Util
import P2M.Sol.S_MvPowerSeries_mul_pow_mem_span_X_pow_and_sum_coeff_mul_pow_eq_constantCoeff_mul_pow
attribute [-instance] DrinfeldCurve.instAlgebraCoordRing DrinfeldCurve.instCommRingCoordRing
attribute [-simp] DrinfeldCurve.LocalChart.ChartPresentation.mk.sizeOf_spec DrinfeldCurve.LocalChart.ChartPresentation.mk.injEq

set_option autoImplicit false

theorem MvPowerSeries.mul_pow_mem_span_X_pow_and_sum_coeff_mul_pow_eq_constantCoeff_mul_pow
    (W : Type) [CommRing W] (G h : MvPowerSeries (Fin 2) W) (d k : ℕ)
    (hh : h ∈ (Ideal.span {(MvPowerSeries.X 0 : MvPowerSeries (Fin 2) W), MvPowerSeries.X 1}) ^ d) (a b : W) :
    G * h ^ k ∈ (Ideal.span {(MvPowerSeries.X 0 : MvPowerSeries (Fin 2) W), MvPowerSeries.X 1}) ^ (d * k) ∧
      (∑ i ∈ Finset.range (d * k + 1),
            MvPowerSeries.coeff (Finsupp.single (0 : Fin 2) i + Finsupp.single (1 : Fin 2) (d * k - i)) (G * h ^ k)
              * a ^ i * b ^ (d * k - i)) =
        MvPowerSeries.constantCoeff G *
          (∑ i ∈ Finset.range (d + 1),
            MvPowerSeries.coeff (Finsupp.single (0 : Fin 2) i + Finsupp.single (1 : Fin 2) (d - i)) h
              * a ^ i * b ^ (d - i)) ^ k := by p2m_exact_reverting @_root_.P2MW.S_MvPowerSeries_mul_pow_mem_span_X_pow_and_sum_coeff_mul_pow_eq_constantCoeff_mul_pow.solution
