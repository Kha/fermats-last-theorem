import Mathlib
import Definitions.Def_DrinfeldCurve_LocalChart
import P2M.Util
import P2M.Sol.S_MvPowerSeries_isReduced_residueField_tensorProduct_quotient_span_C_mul_sub_mul_of_sub_drinfeldForm_mem_pow

set_option autoImplicit false

p2m_open "IsLocalRing TensorProduct MvPowerSeries~exists_ringEquiv_quotient_quotient_span_C_of_maximalIdeal_eq_span~isReduced_quotient_span_of_sub_drinfeld_mem_pow"

theorem MvPowerSeries.isReduced_residueField_tensorProduct_quotient_span_C_mul_sub_mul_of_sub_drinfeldForm_mem_pow
    (q : ℕ) [Fact q.Prime]
    (W : Type) [CommRing W] [IsLocalRing W] (ϖ : W) (hϖ : maximalIdeal W = Ideal.span {ϖ})
    (hq : (q : W) ∈ maximalIdeal W)
    (a : W) (ha : a ∈ maximalIdeal W)
    (f u v : MvPowerSeries (Fin 2) W) (hu : IsUnit u)
    (hf : f - DrinfeldCurve.LocalChart.drinfeldForm q W ∈
      (Ideal.span {(X 0 : MvPowerSeries (Fin 2) W), X 1}) ^ (q + 2)) :
    IsReduced (ResidueField W ⊗[W] (MvPowerSeries (Fin 2) W ⧸ Ideal.span {C a * v - f * u})) := by p2m_exact_reverting @_root_.P2MW.S_MvPowerSeries_isReduced_residueField_tensorProduct_quotient_span_C_mul_sub_mul_of_sub_drinfeldForm_mem_pow.solution
