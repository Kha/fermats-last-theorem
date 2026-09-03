import Mathlib
import Definitions.Def_DrinfeldCurve_LocalChart
import P2M.Util
import P2M.Sol.S_DrinfeldCurve_LocalChart_isUnit_sum_pow_mul_pow_of_pow_mul_sub_mul_pow_mem_maximalIdeal

set_option autoImplicit false

open IsLocalRing

theorem DrinfeldCurve.LocalChart.isUnit_sum_pow_mul_pow_of_pow_mul_sub_mul_pow_mem_maximalIdeal
    (q : ℕ) [Fact q.Prime] (W : Type) [CommRing W] [IsLocalRing W] (hqW : (q : W) ∈ maximalIdeal W)
    (a b : W) (hab : a ∉ maximalIdeal W ∨ b ∉ maximalIdeal W)
    (hdir : a ^ q * b - a * b ^ q ∈ maximalIdeal W) :
    IsUnit (∑ i ∈ Finset.range (q + 1), a ^ ((q - 1) * i) * b ^ ((q - 1) * (q - i))) := by p2m_exact_reverting @_root_.P2MW.S_DrinfeldCurve_LocalChart_isUnit_sum_pow_mul_pow_of_pow_mul_sub_mul_pow_mem_maximalIdeal.solution
